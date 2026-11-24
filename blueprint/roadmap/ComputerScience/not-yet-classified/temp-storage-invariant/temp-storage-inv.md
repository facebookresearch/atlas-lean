# Temp Storage Inv

Reachability invariant for temporary merge storage. Inline storage must fit the
256 raw pointer slots in `temparray`; keyed entries consume two pointer slots.
Heap storage records the same one-or-two-slot multiplier used by
`merge_getmem`. In the released case, `cells` is empty but there is deliberately
no relationship to `alloced`: pinned `merge_freemem` clears `a.keys` while
leaving `alloced` stale. `hasValues` likewise remains available as mode
metadata.
