# Memcpy Source

Provenance of the source operand of `memcpy` relative to its destination.

The same-backing constructor carries no second `SortSlice`: its source is the
destination itself by construction.  The distinct-backing constructor is an
explicit provenance assertion and therefore remains distinct even when its
stored contents are extensionally equal to the destination.
