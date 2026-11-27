# Tendsto compact sandwich

Let `𝕜` be a real or complex scalar field and let `E` and `F` be normed inner-product spaces
over `𝕜`, equipped with the specified Hilbert bases. The coordinate subsets are finite. Assume
the continuous linear map `T : E →L[𝕜] F` is compact. The Hilbert-basis index types are
arbitrary, and coordinate truncations are indexed by their finite subsets.

For independent Hilbert bases, their finite-span projections sandwich a compact map to itself in
the operator norm. Both index types are arbitrary; no separability, nonzero-space or
approximation-property assumption is needed. Completeness is derived from the supplied basis
representations; callers need no separate completeness instances. The existing basis projections
are reused.
