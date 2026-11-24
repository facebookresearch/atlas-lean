# Memmove From Traced?

Traced general two-store `sortslice_memmove`.  Explicit same-backing
provenance selects the overlap-safe directional trace, while explicit distinct
provenance selects increasing-address key and values phases over the unchanged
source store.
