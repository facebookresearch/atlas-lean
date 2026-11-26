# Pairing invocation and response occurrences

Positions `i` and `j` in a finite event history are paired if `i < j`, the event at `j`
is a response matching the invocation at `i` in process and object, and no event of that
process lies strictly between them. In a well-formed history this is the invocation and its
next matching response.
