# Merge At Pending Update Traced third Last access order

On CPython's third-last branch, the pending mutation exposes the physical
write/read/write sequence in source order.  The final logical shrink emits no
indexed event.
