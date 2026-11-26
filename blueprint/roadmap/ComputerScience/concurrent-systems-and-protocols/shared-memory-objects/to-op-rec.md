# Position-preserving encoding of a completed operation

Export a completed operation of `H` to the completed-only `OpRec` model. The object,
operation name, and the original zero-based invocation and response positions are unchanged.
Two supplied functions encode the argument list and the termination condition with its result
list as natural numbers. The record does not retain the process; no injectivity of the payload
encodings is assumed.
