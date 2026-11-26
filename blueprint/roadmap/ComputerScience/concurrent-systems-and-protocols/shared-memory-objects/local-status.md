# Classifying a process as running or halted

Classify a process's local state as halted when it has no next operation, and as running
otherwise. Both outcomes retain that state. This applies on initialization and after an
operation, not on an additional turn of the schedule.
