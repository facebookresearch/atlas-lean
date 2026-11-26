# Well-formed concurrent event histories

A finite event history `H` is well formed if the subhistory at every process is sequential:
it consists of matched adjacent pairs and at most one pending invocation, at the end of that
process's subhistory.
