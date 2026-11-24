# Rejected Uninitialized Temp Read is observable

Rejection because a live in-bounds cell is uninitialized does not erase
the attempt or falsely fail either the bounds or backing-liveness predicate.
