/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.StableMatchingSequences

/-!
# When the Gale–Shapley algorithm ends in one round

For a preference profile `P` for `n ≥ 1` men and `n` women, `galeShapleyRounds_eq_one_iff` shows
that the men-proposing Gale–Shapley algorithm on `P` ends in exactly one round if and only if
every woman is the first choice of exactly one man.

The proof follows the algorithm through its first round. Before anyone proposes, no man is
provisionally engaged, so the algorithm takes at least one round. In the first round every man
proposes to his first choice. A woman who receives several proposals holds only one of these
suitors, so every man is engaged after the first round exactly when no two men have the same
first choice, that is, when the first choices form a bijection between the men and the women.

The result is from Borodin et al., *Sequences of the Stable Matching Problem*, Journal of Integer
Sequences 27 (2024), Article 24.2.2. The preprint arXiv:2201.00645v1 states it in Section 3.5
("Tastes differ").
-/

set_option autoImplicit false

public section

namespace MetaMathlibExt.StableMatchingSequences

variable {n : ℕ}

/-- No man is provisionally engaged before anyone has proposed. -/
private theorem not_gsEngaged_zero (P : PreferenceProfile n) (i : Fin n) :
    ¬ GSEngaged P (fun _ => 0) i := by
  rintro ⟨r, hr, -⟩
  exact Nat.succ_ne_zero _ hr

/-- After the first round every man has proposed once, to his first choice. -/
private theorem gsProposals_one (P : PreferenceProfile n) : gsProposals P 1 = fun _ => 1 := by
  funext i
  rw [gsProposals_succ, gsProposals_zero, ite_eq_right (not_gsEngaged_zero P i)]

/-- After the first round every man is provisionally engaged if and only if no two men have the
same first choice. -/
private theorem forall_gsEngaged_one_iff (P : PreferenceProfile n) (hn : 0 < n) :
    (∀ i, GSEngaged P (fun _ => 1) i) ↔ Function.Injective fun i => P.1 i ⟨0, hn⟩ := by
  constructor
  · intro h i i' hii'
    replace hii' : P.1 i ⟨0, hn⟩ = P.1 i' ⟨0, hn⟩ := hii'
    obtain ⟨r, hr, hi⟩ := h i
    obtain ⟨r', hr', hi'⟩ := h i'
    dsimp only at hr hr'
    obtain rfl : r = ⟨0, hn⟩ := Fin.ext (show (r : ℕ) = 0 by omega)
    obtain rfl : r' = ⟨0, hn⟩ := Fin.ext (show (r' : ℕ) = 0 by omega)
    have h₁ := hi i' ⟨0, hn⟩ Nat.zero_lt_one hii'.symm
    have h₂ := hi' i ⟨0, hn⟩ Nat.zero_lt_one hii'
    rw [← hii'] at h₂
    exact (P.2 (P.1 i ⟨0, hn⟩)).symm.injective (Fin.ext (le_antisymm h₁ h₂))
  · intro h i
    refine ⟨⟨0, hn⟩, rfl, fun i' r' hr' hi' => ?_⟩
    dsimp only at hr'
    obtain rfl : r' = ⟨0, hn⟩ := Fin.ext (show (r' : ℕ) = 0 by omega)
    rw [h hi']

/-- The algorithm ends after exactly one round if and only if every man is provisionally engaged
after the first round. -/
private theorem galeShapleyRounds_eq_one_iff_forall_gsEngaged (P : PreferenceProfile n)
    (hn : 0 < n) : galeShapleyRounds P = 1 ↔ ∀ i, GSEngaged P (gsProposals P 1) i := by
  constructor
  · intro h
    have hne : {t : ℕ | ∀ i : Fin n, GSEngaged P (gsProposals P t) i}.Nonempty := by
      refine Set.nonempty_iff_ne_empty.mpr fun hem => ?_
      have h₀ : galeShapleyRounds P = 0 := Nat.sInf_eq_zero.mpr (Or.inr hem)
      omega
    have hmem : galeShapleyRounds P ∈ {t : ℕ | ∀ i : Fin n, GSEngaged P (gsProposals P t) i} :=
      Nat.sInf_mem hne
    rwa [h] at hmem
  · intro h₁
    refine le_antisymm (Nat.sInf_le h₁) (Nat.one_le_iff_ne_zero.mpr fun h => ?_)
    rcases Nat.sInf_eq_zero.mp h with h₀ | hem
    · exact not_gsEngaged_zero P ⟨0, hn⟩ (h₀ ⟨0, hn⟩)
    · exact Set.eq_empty_iff_forall_notMem.mp hem 1 h₁

/-- **When the Gale–Shapley algorithm ends in one round.** Let $n \ge 1$ and let $P$ be a
preference profile for $n$ men and $n$ women. The men-proposing Gale–Shapley algorithm on $P$ ends
in exactly one round if and only if every woman is the first choice of exactly one man.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Proposition 2
(`jis-2024-24.2.2-prop-2`). -/
theorem galeShapleyRounds_eq_one_iff (P : PreferenceProfile n) (hn : 0 < n) :
    galeShapleyRounds P = 1 ↔ ∀ j : Fin n, ∃! i : Fin n, P.1 i ⟨0, hn⟩ = j := by
  rw [galeShapleyRounds_eq_one_iff_forall_gsEngaged P hn, gsProposals_one,
    forall_gsEngaged_one_iff P hn, Finite.injective_iff_bijective,
    Function.bijective_iff_existsUnique]

end MetaMathlibExt.StableMatchingSequences
