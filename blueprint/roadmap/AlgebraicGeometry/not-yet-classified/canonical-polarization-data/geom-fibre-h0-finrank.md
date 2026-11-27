# Geom Fibre H0 Finrank

The dimension over `k` of the global sections of `L` on the fibre of `f`
over `sk : S →+* k`, that is, of the pullback of `L` to `A ×_S Spec k`.  The
definition takes any field `k`; geometric fibres are the case `k`
algebraically closed, which is how `CanonicalPolarizationData.positiveRank`
uses it.  It is `Module.finrank`, so it is `0` when the sections are
infinite-dimensional: a positive value says that they are finite-dimensional
and nonzero.
