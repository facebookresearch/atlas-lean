# The two-phase commit invariant holds in reachable states

For every set $P$ of
participants, every global state of the two-phase commit protocol that is reachable from the
initial state satisfies the inductive invariant, that is, both of the following hold: if the
coordinator has committed, then every participant is prepared or committed; and every committed
participant has a committed coordinator.
