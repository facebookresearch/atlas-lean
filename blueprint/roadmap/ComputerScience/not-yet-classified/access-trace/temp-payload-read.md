# Temp Payload Read?

Read one initialized temporary payload cell.  Both the region's backing
and its extent come from `storage` at the attempt.  An in-bounds but
uninitialized (`none`) cell rejects the read only after preserving that event.
