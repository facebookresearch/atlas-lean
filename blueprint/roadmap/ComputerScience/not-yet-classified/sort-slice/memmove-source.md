# Memmove Source

Provenance of the source operand of `sortslice_memmove`.  Movement uses the
same dependent backing witness as `memcpy`, but imposes no disjointness
condition: shared storage is handled by overlap-safe traversal instead.
