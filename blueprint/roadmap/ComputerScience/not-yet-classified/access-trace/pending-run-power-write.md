# Pending Run Power Write?

Update only the stored power field of one pending run while recording the
single indexed write performed by C.  Looking up the other fields is part of
constructing the replacement record, not a second source-level read event.
Rejected negative and out-of-range writes retain their attempted event.
