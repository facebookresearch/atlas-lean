# Count Run Canonical Range

The input-side condition needed for occurrence stability: within the
remaining source range, comparator-equivalent occurrences already appear in
increasing origin order.  The permutation half is deliberately the reflexive
one, so this is the shared `StableOccurrencePermutation` predicate rather
than a weaker local surrogate.
