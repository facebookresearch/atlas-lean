# Two-phase commit invariant

A global state $s$ of the two-phase commit protocol
satisfies the invariant when two conditions hold: if the coordinator has committed, then every
participant is prepared or committed; and every committed participant has a committed
coordinator.
