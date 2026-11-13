# Indistinguishability relative to `Admissible`

**Indistinguishability relative to `Admissible`** of a family `G n : S n → Y n`: every
admissible family of distinguishers has negligible `prgAdvantage` (the pseudorandomness condition
of Katz and Lindell, Definition 3.14, with the class of admissible distinguishers as a parameter,
as for `PubCPASecure`). The coin types must be nonempty, or there would be no distinguishers.

This is an abstract relative-indistinguishability predicate: Definition 3.14 also requires `G` to
be deterministic polynomial-time computable and the distinguishers to be probabilistic
polynomial-time. Nothing here constrains how `G` is computed, and the restriction on
distinguishers is whatever `Admissible` encodes.
