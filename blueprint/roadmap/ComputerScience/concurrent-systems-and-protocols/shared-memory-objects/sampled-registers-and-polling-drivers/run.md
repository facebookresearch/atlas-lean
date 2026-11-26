# Execution of an overwrite-newest register history

Run a finite list of atomic operations from the empty slot and zero publication count.
Return the tagged events in input order, one per operation, and the final slot. Publications use
consecutive one-based numbers independently of reads; `.read none` records an empty read.
