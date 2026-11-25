/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.StableMatchingSequences

/-!
# At most one hell-couple in a stable matching

For a preference profile `P` for `n` men and `n` women and a stable matching `μ` for `P`,
`hellCouple_subsingleton` shows that at most one man forms a hell-couple with his wife: at most
one married couple of `μ` consists of two people who rank each other last.

The proof is the one in the source. If two different men `i` and `i'` formed hell-couples, then
man `i` and the wife `μ i'` of man `i'` would form a blocking pair: man `i` ranks his own wife
last, so he prefers `μ i'` to her, and `μ i'` ranks her husband `i'` last, so she prefers `i` to
him.

The companion result `hellCouple_mem_all_stable`, in
`MathlibExt.Combinatorics.Enumerative.StableMatchingSequences`, shows that a hell-couple of one
stable matching is married in every stable matching of the same profile.

The result is from Borodin et al., *Sequences of the Stable Matching Problem*, Journal of Integer
Sequences 27 (2024), Article 24.2.2. The preprint arXiv:2201.00645v1 states it as Proposition 6,
in Section 6.1 ("A hell-pair and a hell-couple").
-/

set_option autoImplicit false

public section

namespace MetaMathlibExt.StableMatchingSequences

variable {n : ℕ}

/-- If a ranking puts `b` in the last position `n - 1`, it puts every `a ≠ b` strictly before
`b`. -/
private theorem lt_of_ne_of_last (σ : Equiv.Perm (Fin n)) {a b : Fin n}
    (hb : (σ.symm b : ℕ) = n - 1) (hab : a ≠ b) : (σ.symm a : ℕ) < (σ.symm b : ℕ) := by
  have ha := (σ.symm a).isLt
  have hne : (σ.symm a : ℕ) ≠ (σ.symm b : ℕ) := fun h => hab (σ.symm.injective (Fin.ext h))
  omega

/-- **At most one hell-couple in a stable matching.** Let $P$ be a preference profile of $n$
men and $n$ women, and let $\mu$ be a stable matching for $P$, in which man $i$ marries woman
$\mu(i)$. Then at most one man $i$ forms a hell-couple with his wife $\mu(i)$.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Proposition 12
(`jis-2024-24.2.2-prop-12`). -/
theorem hellCouple_subsingleton (P : PreferenceProfile n)
    (μ : Equiv.Perm (Fin n)) (hμ : IsStableMatching P μ) :
    {i : Fin n | IsHellCouple P μ i}.Subsingleton := by
  intro i hi i' hi'
  by_contra hne
  -- Man `i` and the wife of man `i'` would block `μ`.
  refine (isStableMatching_iff P μ).mp hμ i (μ i') ⟨?_, ?_⟩
  · exact lt_of_ne_of_last (P.1 i) hi.1 (μ.injective.ne (Ne.symm hne))
  · rw [μ.symm_apply_apply]
    exact lt_of_ne_of_last (P.2 (μ i')) hi'.2 hne

end MetaMathlibExt.StableMatchingSequences
