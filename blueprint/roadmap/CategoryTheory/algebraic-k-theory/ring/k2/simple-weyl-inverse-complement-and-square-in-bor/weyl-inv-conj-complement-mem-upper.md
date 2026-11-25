# Weyl inv conj complement mem upper

Inverse simple-Weyl conjugate of the complement stays upper: for
`hm : m + 1 < n`, `c ∈ simpleRootComplementSubgroup n m`, and
`s = weyl m (m + 1) 1`, `s⁻¹ * c * s ∈ upperUnipotentSubgroup n`.
Purpose: structural inverse-transport prerequisite for Lemma 25, avoiding a
duplicate four-case root proof. Reuses the forward
`weyl_conj_complement_mem_upper` plus one torus normalization.
Orientation: `s⁻¹ * c * s`. Characteristic-two safe.
Nonclaim: no Lemma 25 containment, Bruhat, quotient, or Matsumoto claim.
