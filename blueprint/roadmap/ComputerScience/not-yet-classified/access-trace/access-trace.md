# Access Trace

Ordered observations made by an instrumented evaluator.

`accesses`, `pushDepths`, `memoryEvents`, and `policyEvents` are chronological
within their respective channels.  A `pushDepths` entry is the pending-array
size *after* one unconditional push.  Fuel exhaustion composes by Boolean
disjunction.
