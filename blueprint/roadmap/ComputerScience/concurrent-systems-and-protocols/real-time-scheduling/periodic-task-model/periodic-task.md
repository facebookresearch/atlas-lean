# Periodic tasks

A periodic task has a run-time `C ≥ 1`, a period `T ≥ 1` and a phase: its
request `k`, for `k = 0, 1, 2, …`, is made at slot `phase + k * T`, and its deadline is the time of
the next request, `phase + (k + 1) * T`. The run-time may exceed the period.
