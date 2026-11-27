# Counters at which a ticket is held

The predicate on program counters that holds exactly at `doorway`, `waitChoosing`, `waitNumber`, `critical` and `exit`, the counters during which a ticket is meant to be held; in particular the ticket is still held at `exit`. It is a predicate of the counter alone, not a read of the ticket; that the ticket is nonzero exactly at these counters is part of the invariant.
