.PHONY: all fmt help

all: fmt
fmt:
	@echo Formatting...
	@go fmt ./*.go
	@go vet ./*.go
help:
	@echo "make: fmt"
.EXPORT_ALL_VARIABLES:
GO111MODULE = on
