# Gallop Right safe

Public source-generic `gallop_right` safety theorem.

The traced evaluator succeeds without fuel exhaustion, returns an index at
most `n`, emits no pending-stack pushes, records only signed in-bounds and live
accesses, and erases exactly to the agreeing reviewed `gallopRight?`
transcription.
