# Event pairing uses the next event of the process

In a well-formed finite event history, positions `i` and `j` are paired if and only if
`j` is later than `i`, its event matches `i`'s invocation in process and object, and no response
matching that invocation occurs strictly between those positions.
