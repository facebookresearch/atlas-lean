# Asymptotic PRP security relative to `Admissible`

**Asymptotic PRP security relative to `Admissible`** of a family of keyed permutations
`F n : K n → Perm (X n)`: every admissible family of distinguishers with coins in `S n` has
negligible `prpAdvantage` (the indistinguishability condition of Katz and Lindell, Section 3.5.1,
with the admissible class as a parameter).

This is an abstract relative-indistinguishability predicate. The source conditions it omits are
recorded here: Katz and Lindell require `F` to be an efficient, length-preserving keyed
permutation (`F_k` and `F_k⁻¹` computable in deterministic polynomial time) and quantify over
probabilistic polynomial-time distinguishers. Nothing here constrains how `F` is computed, so a
noncomputable family can satisfy `PRPSecure`; any restriction on distinguishers must be supplied
through `Admissible`.
