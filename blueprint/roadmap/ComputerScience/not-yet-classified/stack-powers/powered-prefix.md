# Powered Prefix

Steady-state PowerSort invariant, immediately after a run is pushed.

The empty stack is valid.  On every nonempty stack there is exactly one newest
run, whose stored `power` field is deliberately unconstrained because
CPython's push writes only its base and length.  Every older run's stored power
is exactly the transcribed `powerloop` result for its boundary with the next
run, lies in `1 .. 60`, and increases strictly in C array order.  Consequently
the condition is vacuous for a singleton stack.
