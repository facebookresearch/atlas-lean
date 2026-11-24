# Finite Weyl simple Root mem borel

Positive simple-root transport: for `hm : m + 1 < n`, a finite-Weyl
element `w`, and positivity of its induced permutation on `m, m + 1`, every
`w * g * w⁻¹` with `g ∈ simpleRootSubgroup m` lies in
`finiteBorelSubgroup n`. Purpose: reusable Lemma-25 prerequisite sending the
simple root into the finite Borel. The proof eliminates `g` to one
`x m (m + 1)` generator via `simpleRootSubgroup_exists_eq_x`, conjugates by
`finiteWeyl_conj_x`, and lands in the upper subgroup (hence the Borel) since
positivity gives the strict index inequality. Nonclaim: no complement,
quotient, Bruhat, or Matsumoto claim.
