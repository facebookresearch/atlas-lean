# Trace bind

The trace side of `bind`: a rejected first operation retains its local
trace, while a successful continuation appends its trace in execution order.
