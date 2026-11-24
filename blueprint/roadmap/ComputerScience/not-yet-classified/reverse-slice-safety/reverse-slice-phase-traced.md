# Reverse Slice Phase Traced?

Traced half-open `reverse_slice` for one physical array.

The returned `SortSlice` is the paired-snapshot semantic update for that
physical phase, not a literal intermediate C store.  In particular, callers
that instrument both key and values phases must run each phase from the same
pre-state and compose their traces; they must not feed the key-phase result to
the values phase.
