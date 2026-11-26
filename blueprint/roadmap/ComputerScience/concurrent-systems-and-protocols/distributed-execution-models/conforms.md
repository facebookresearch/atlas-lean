# Conforms

Local conformance checks the recorded initial state and every step of `p` against the
instruction from its actual prior state. At a receive, the successor is computed from the batch
listed at that step. The legality of the schedule and deliveries is checked by `WellFormed`.
