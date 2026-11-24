# Gallop Left safe

Public source-generic `gallop_left` safety theorem.

No consistency, transitivity, totality, or stability law is assumed of
`state.key_compare`.  The traced evaluator succeeds without exhausting either
fuel counter, returns an index at most `n`, emits no pending-stack pushes,
records only signed in-bounds and live accesses, and erases exactly to the
agreeing reviewed `gallopLeft?` call.
