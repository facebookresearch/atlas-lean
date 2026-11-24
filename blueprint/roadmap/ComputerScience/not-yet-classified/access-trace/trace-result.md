# Trace Result

The result type used by local instrumented evaluators.

An invalid modeled operation returns `none`, but its already-produced trace is
retained.  Successful continuations compose their observations in order.
