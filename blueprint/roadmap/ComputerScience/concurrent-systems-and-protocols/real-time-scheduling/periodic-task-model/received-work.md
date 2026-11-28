# Work received by a request

`receivedWork tasks sched i k t` is the number of slots `s < t`
from the release of request `k` of task `i` up to its deadline, `release ≤ s < deadline`, in which
the schedule runs task `i`. Slots at or after the deadline do not count, so the work stops growing
once the deadline passes.
