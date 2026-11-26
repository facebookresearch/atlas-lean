/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fintype.Prod
public import Domains.Biology.ComputationalBiology.CenterStarCenterStarBound

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Positivity

/-!
# Center-star alignment ratio

Using the pairwise and multiple alignment values of
`Domains.Biology.ComputationalBiology.CenterStarCenterStarBound`, this module proves the
center-star approximation ratio `V(Ac) / V(A*) ≤ 2 * (k - 1) / k < 2` for a positive optimum.

Source: D. Gusfield, "Efficient methods for multiple sequence alignment with
guaranteed error bounds", Bulletin of Mathematical Biology 55(1):141-154,
1993, doi:10.1007/BF02460299, Lemma 3.1 and Theorem 3.1.
-/

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.CenterStarWanted

variable {α : Type*} [DecidableEq α]

private theorem inducedValue_eq_sum {β : Type*} (s : Option β → Option β → ℝ)
    {k : ℕ} (A : MSAlignment β k) (i j : Fin k) :
    inducedValue s A i j = (A.cols.map fun col => s (col i) (col j)).sum := by
  simp only [inducedValue, List.zip_map', List.map_map]
  rfl

private theorem inducedValue_symm {β : Type*} (s : Option β → Option β → ℝ)
    (hsymm : ∀ x y, s x y = s y x) {k : ℕ} (A : MSAlignment β k) (i j : Fin k) :
    inducedValue s A i j = inducedValue s A j i := by
  simp only [inducedValue_eq_sum]
  congr 1
  exact List.map_congr_left fun col _ => hsymm (col i) (col j)

private theorem inducedValue_self {β : Type*} (s : Option β → Option β → ℝ)
    (hdiag : ∀ x, s x x = 0) {k : ℕ} (A : MSAlignment β k) (i : Fin k) :
    inducedValue s A i i = 0 := by
  simp [inducedValue_eq_sum, hdiag]

private theorem inducedValue_triangle {β : Type*} (s : Option β → Option β → ℝ)
    (htria : ∀ x y z, s x z ≤ s x y + s y z) {k : ℕ}
    (A : MSAlignment β k) (i c j : Fin k) :
    inducedValue s A i j ≤ inducedValue s A i c + inducedValue s A c j := by
  simp only [inducedValue_eq_sum, ← List.sum_map_add]
  exact List.sum_le_sum fun col _ => htria (col i) (col c) (col j)

private theorem sum_pairs {k : ℕ} (f : Fin k → Fin k → ℝ)
    (hsymm : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) =
      2 * ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter (fun p => p.1 < p.2),
        f p.1 p.2 := by
  have hsplit (i j : Fin k) : f i j =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt.mpr (le_of_lt h)]
    · subst j
      simp [hdiag]
    · simp [h, not_lt.mpr (le_of_lt h), hsymm]
  calc
    (∑ i, ∑ j, f i j) =
        ∑ i, ∑ j, ((if i < j then f i j else 0) +
          (if j < i then f j i else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl fun j _ => hsplit i j
    _ = (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if j < i then f j i else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = 2 * ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
        (fun p => p.1 < p.2), f p.1 p.2 := by
      rw [Finset.sum_comm (f := fun i j => if j < i then f j i else 0)]
      simp [Finset.sum_filter, Fintype.sum_prod_type, two_mul]

private theorem sum_inducedValue {β : Type*} (s : Option β → Option β → ℝ)
    (hsymm : ∀ x y, s x y = s y x) (hdiag : ∀ x, s x x = 0)
    {k : ℕ} (A : MSAlignment β k) :
    (∑ i, ∑ j, inducedValue s A i j) = 2 * msaValue s A :=
  sum_pairs (inducedValue s A) (inducedValue_symm s hsymm A)
    (inducedValue_self s hdiag A)

private theorem pairDist_le_inducedValue {β : Type*} (s : Option β → Option β → ℝ)
    {k : ℕ} (X : Fin k → List β)
    (hD_le : ∀ (U V : List β) (A : PairAlignment β),
      IsPairAlignmentOf A U V → pairDist s U V ≤ alignValue s A)
    (A : MSAlignment β k) (hA : msErasesTo A X) (i j : Fin k) :
    pairDist s (X i) (X j) ≤ inducedValue s A i j := by
  let P : PairAlignment β :=
    ⟨A.cols.map (fun col => col i), A.cols.map (fun col => col j), by simp⟩
  exact hD_le (X i) (X j) P ⟨hA i, hA j⟩

private theorem sum_star {k : ℕ} (d : Fin k → ℝ) :
    (∑ i, ∑ j, (d i + d j - if i = j then 2 * d j else 0)) =
      2 * ((k : ℝ) - 1) * ∑ i, d i := by
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  ring

omit [DecidableEq α] in
/-- **Center-star ratio form** (Gusfield 1993, Theorem 3.1): same hypotheses
as `centerStar_bound` (including `s none none = 0` and zero self-costs `s x x = 0` for every
`x : Option α`, `hdiag`, and the projection property `hproj` of `Ac` onto the center row) plus
positivity of the optimum (`hpos`). Conclusion:
`V(Ac) / V(Astar) ≤ 2 * (k - 1) / k < 2`.

Source: Gusfield (1993), Theorem 3.1. -/
theorem centerStar_ratio (s : Option α → Option α → ℝ)
    (hgap : s none none = 0)
    (hdiag : ∀ x : Option α, s x x = 0)
    (htria : ∀ x y z : Option α, s x z ≤ s x y + s y z)
    (hsymm : ∀ x y : Option α, s x y = s y x)
    (k : ℕ) (hk : 2 ≤ k)
    (X : Fin k → List α)
    (hD_le : ∀ (U V : List α) (A : PairAlignment α),
      IsPairAlignmentOf A U V → pairDist s U V ≤ alignValue s A)
    (hD_att : ∀ U V : List α, ∃ A : PairAlignment α,
      IsPairAlignmentOf A U V ∧ pairDist s U V = alignValue s A)
    (c : Fin k)
    (hcenter : ∀ i : Fin k, centerTotal s X (X c) ≤ centerTotal s X (X i))
    (Ac : MSAlignment α k)
    (hac : msErasesTo Ac X)
    (hproj : ∀ i, inducedValue s Ac c i = pairDist s (X c) (X i))
    (Astar : MSAlignment α k)
    (hastar : msErasesTo Astar X)
    (hopt : ∀ A' : MSAlignment α k, msErasesTo A' X →
      msaValue s Astar ≤ msaValue s A')
    (hpos : 0 < msaValue s Astar) :
    msaValue s Ac / msaValue s Astar ≤ 2 * ((k : ℝ) - 1) / k ∧
      2 * ((k : ℝ) - 1) / k < 2
    := by
  have _ := hgap
  have _ := hD_att
  have _ := hac
  have _ := hopt
  have hkpos : 0 < (k : ℝ) := by positivity
  have hkone : 0 ≤ (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hcenter_sum : (k : ℝ) * centerTotal s X (X c) ≤ 2 * msaValue s Astar := by
    calc
      (k : ℝ) * centerTotal s X (X c) = ∑ _i : Fin k, centerTotal s X (X c) := by
        simp
      _ ≤ ∑ i, centerTotal s X (X i) := Finset.sum_le_sum fun i _ => hcenter i
      _ ≤ ∑ i, ∑ j, inducedValue s Astar i j := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum fun j _ =>
          pairDist_le_inducedValue s X hD_le Astar hastar i j
      _ = 2 * msaValue s Astar := sum_inducedValue s hsymm hdiag Astar
  have hstar : 2 * msaValue s Ac ≤
      2 * ((k : ℝ) - 1) * centerTotal s X (X c) := by
    calc
      2 * msaValue s Ac = ∑ i, ∑ j, inducedValue s Ac i j :=
        (sum_inducedValue s hsymm hdiag Ac).symm
      _ ≤ ∑ i, ∑ j, (pairDist s (X c) (X i) + pairDist s (X c) (X j) -
          if i = j then 2 * pairDist s (X c) (X j) else 0) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : i = j
        · subst j
          rw [inducedValue_self s hdiag, ite_eq_left rfl]
          linarith
        · rw [ite_eq_right hij, sub_zero]
          calc
            inducedValue s Ac i j ≤ inducedValue s Ac i c + inducedValue s Ac c j :=
              inducedValue_triangle s htria Ac i c j
            _ = pairDist s (X c) (X i) + pairDist s (X c) (X j) := by
              rw [inducedValue_symm s hsymm Ac i c, hproj i, hproj j]
      _ = 2 * ((k : ℝ) - 1) * centerTotal s X (X c) :=
        sum_star (fun i => pairDist s (X c) (X i))
  have hbound : (k : ℝ) * msaValue s Ac ≤
      2 * ((k : ℝ) - 1) * msaValue s Astar := by
    have hstar' : msaValue s Ac ≤ ((k : ℝ) - 1) * centerTotal s X (X c) := by
      linarith
    have h₁ := mul_le_mul_of_nonneg_left hstar' hkpos.le
    have h₂ := mul_le_mul_of_nonneg_left hcenter_sum hkone
    nlinarith
  constructor
  · rw [div_le_iff₀ hpos, div_mul_eq_mul_div, le_div_iff₀ hkpos]
    nlinarith [hbound]
  · rw [div_lt_iff₀ hkpos]
    linarith

end WantedExt.Biology.ComputationalBiology.CenterStarWanted
