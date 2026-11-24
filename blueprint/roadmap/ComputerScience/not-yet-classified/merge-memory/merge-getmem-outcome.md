# Merge Getmem Outcome

Observable control-flow outcome of `merge_getmem`. The `.grown` case is the
version-one successful-allocation abstraction. `.guardRejected` is not an
allocator failure: it is the deterministic `size_t` overflow guard from the C
source, which runs after `merge_freemem`.
