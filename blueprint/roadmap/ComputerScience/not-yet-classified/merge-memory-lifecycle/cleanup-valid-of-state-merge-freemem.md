# Cleanup Valid of State merge Freemem

The real terminal `merge_freemem` transition satisfies the cleanup
contract.  The post-state may retain stale `alloced`, but its released payload
is empty and its physical-slot observation is zero.
