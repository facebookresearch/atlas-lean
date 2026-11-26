# Fair

Fairness requires a process to perform atomic operations at arbitrarily late positions
unless it has halted or crashed. The stopping events themselves are not atomic operations.
This constrains schedules; it does not assume that every execution is fair.
