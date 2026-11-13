# Asymptotic PRF security relative to `Admissible`

**Asymptotic PRF security relative to `Admissible`** of a family of keyed functions
`F n : K n → X n → Y n`: every admissible family of distinguishers with coins in `S n` has
negligible `prfAdvantage` (the indistinguishability condition of Katz and Lindell,
Definition 3.25, with the admissible class as a parameter).

This is an abstract relative-indistinguishability predicate. Omitted source conditions: `F` an
efficient, length-preserving keyed function (`F_k(x)` computable in deterministic polynomial
time), and probabilistic polynomial-time distinguishers. Nothing here constrains how `F` is
computed, so a noncomputable family can satisfy `PRFSecure`; any restriction on distinguishers
must be supplied through `Admissible`.
