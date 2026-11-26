# Fair shared-memory executions

Fairness requires a process to perform atomic operations at arbitrarily late positions
unless it has halted or crashed. A crash itself is not an atomic operation.
This constrains schedules; it does not assume that every execution is fair.
