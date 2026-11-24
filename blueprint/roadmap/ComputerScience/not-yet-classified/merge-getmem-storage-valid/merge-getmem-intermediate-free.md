# Merge Getmem Intermediate Free

Certificate for the state between `merge_freemem` and successful heap
allocation on the growth path.  Inline backing is retained unchanged; live
heap backing becomes released with no accessible payload.  In both cases the
representation invariant remains true even though the heap case is
temporarily not live.
