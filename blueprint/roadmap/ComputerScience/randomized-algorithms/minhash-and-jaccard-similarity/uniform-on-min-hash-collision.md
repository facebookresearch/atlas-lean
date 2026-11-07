# MinHash collision probability

**MinHash collision probability** (Broder 1997): for a uniformly random permutation `π` of
the finite universe `U` (`uniformOn Set.univ` on `Equiv.Perm U`, for any measurable structure in
which singletons are measurable, e.g. `⊤`) and sets `A`, `B` with `A ∪ B` nonempty,
`P(min π(A) = min π(B)) = |A ∩ B| / |A ∪ B|`, the Jaccard similarity of `A` and `B`.
