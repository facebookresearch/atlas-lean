/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field

/-!
# Cohen's kappa

Two raters classify the same items into `k` categories with joint table `pᵢⱼ` (a probability
table: entries nonnegative, summing to `1`), row margins `pᵢ.` and column margins `p.ⱼ`. The
observed agreement is `p_o = ∑ᵢ pᵢᵢ`, the chance agreement is `p_e = ∑ᵢ pᵢ. p.ᵢ`, and Cohen's
kappa is `κ = (p_o - p_e) / (1 - p_e)`.

## Main statements

* `kappa_eq_zero_of_independent`: when the table is the product of its margins (independent
  raters), `p_o = p_e`, so `κ = 0` when `p_e < 1`.
* `kappa_le_kappaMax`: when `p_e < 1`, every joint probability table with the margins of `P`
  has `κ ≤ κ_max = (∑ᵢ min(pᵢ., p.ᵢ) - p_e) / (1 - p_e)`, since `pᵢᵢ ≤ min(pᵢ., p.ᵢ)`, with
  equality for a table with these margins whose diagonal is `min(pᵢ., p.ᵢ)` (Cohen's `κ_M`,
  the maximum permitted by the margins).

The definitions follow Cohen (1960) as restated in secondary sources, and the statements here are
derived from them.

## References

* J. Cohen, "A coefficient of agreement for nominal scales", Educ. Psychol. Meas. 20 (1960)
  37–46, doi:10.1177/001316446002000104.
-/

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.CohenKappaWanted

/-- `P` is a joint probability table: every entry is nonnegative and the entries sum to `1`. -/
def IsTable {k : ℕ} (P : Fin k → Fin k → ℝ) : Prop := (∀ i j, 0 ≤ P i j) ∧ ∑ i, ∑ j, P i j = 1

/-- Row margin `pᵢ. = ∑ⱼ pᵢⱼ`. -/
noncomputable def rowMargin {k : ℕ} (P : Fin k → Fin k → ℝ) (i : Fin k) : ℝ := ∑ j, P i j

/-- Column margin `p.ⱼ = ∑ᵢ pᵢⱼ`. -/
noncomputable def colMargin {k : ℕ} (P : Fin k → Fin k → ℝ) (j : Fin k) : ℝ := ∑ i, P i j

/-- Observed agreement `p_o = ∑ᵢ pᵢᵢ`. -/
noncomputable def observed {k : ℕ} (P : Fin k → Fin k → ℝ) : ℝ := ∑ i, P i i

/-- Chance agreement `p_e = ∑ᵢ pᵢ. p.ᵢ`. -/
noncomputable def chance {k : ℕ} (P : Fin k → Fin k → ℝ) : ℝ :=
  ∑ i, rowMargin P i * colMargin P i

/-- **Cohen's kappa** `κ = (p_o - p_e) / (1 - p_e)`. -/
noncomputable def kappa {k : ℕ} (P : Fin k → Fin k → ℝ) : ℝ :=
  (observed P - chance P) / (1 - chance P)

/-- The **maximum kappa for the margins of `P`**:
`κ_max = (∑ᵢ min(pᵢ., p.ᵢ) - p_e) / (1 - p_e)`. It is the maximum of `κ` over the joint
probability tables with the margins of `P` when `P` is a joint probability table with
`p_e < 1` (`kappa_le_kappaMax`). At `p_e = 1` the denominator vanishes, and the formula gives `0`
by the convention `x / 0 = 0`. -/
noncomputable def kappaMax {k : ℕ} (P : Fin k → Fin k → ℝ) : ℝ :=
  (∑ i, min (rowMargin P i) (colMargin P i) - chance P) / (1 - chance P)

set_option linter.unusedVariables false in
/-- **Independent raters** (Cohen 1960; derived): let `P` be a joint probability table that is the
product of its margins (`pᵢⱼ = pᵢ. p.ⱼ` for all `i, j`) with chance agreement `p_e < 1`. Then
`κ = 0`.

Source: Cohen (1960). -/
public theorem kappa_eq_zero_of_independent {k : ℕ} (P : Fin k → Fin k → ℝ)
    (hP : IsTable P) (hind : ∀ i j, P i j = rowMargin P i * colMargin P j)
    (he : chance P < 1) :
    kappa P = 0 := by
  have h : observed P = chance P := by
    simp only [observed, chance, hind]
  simp only [kappa, h, sub_self, zero_div]

private lemma residual_mul_div {k : ℕ} (a : Fin k → ℝ) (ha : ∀ i, 0 ≤ a i)
    (t : ℝ) (ht : ∑ i, a i = t) (i : Fin k) : a i * t / t = a i := by
  by_cases h : t = 0
  · have hi : a i = 0 := le_antisymm
      (by simpa [ht, h] using
        (Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i))) (ha i)
    simp [hi]
  · exact mul_div_cancel_right₀ (a i) h

private lemma exists_table_with_diagonal {k : ℕ} (r c : Fin k → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hc : ∀ i, 0 ≤ c i) (hs : ∑ i, r i = ∑ i, c i) :
    ∃ Q : Fin k → Fin k → ℝ, (∀ i j, 0 ≤ Q i j) ∧
      (∀ i, rowMargin Q i = r i) ∧ (∀ j, colMargin Q j = c j) ∧
      (∀ i, Q i i = min (r i) (c i)) := by
  let d := fun i => min (r i) (c i)
  let a := fun i => r i - d i
  let b := fun i => c i - d i
  let t := ∑ i, a i
  have ha : ∀ i, 0 ≤ a i := fun i => sub_nonneg.mpr (min_le_left _ _)
  have hb : ∀ i, 0 ≤ b i := fun i => sub_nonneg.mpr (min_le_right _ _)
  have hbt : ∑ i, b i = t := by
    dsimp [t, a, b]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hs]
  have ht : 0 ≤ t := Finset.sum_nonneg (fun i _ => ha i)
  have hab : ∀ i, a i * b i = 0 := by
    intro i
    dsimp [a, b, d]
    rcases le_total (r i) (c i) with h | h
    · simp [min_eq_left h]
    · simp [min_eq_right h]
  let Q := fun i j => (if i = j then d i else 0) + a i * b j / t
  have hrow : ∀ i, rowMargin Q i = r i := by
    intro i
    simp only [rowMargin, Q, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ i),
      ← Finset.sum_div, ← Finset.mul_sum, hbt,
      residual_mul_div a ha t rfl i]
    exact add_sub_cancel _ _
  have hcol : ∀ j, colMargin Q j = c j := by
    intro j
    simp only [colMargin, Q, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ j),
      ← Finset.sum_div, ← Finset.sum_mul]
    change d j + t * b j / t = c j
    rw [mul_comm t, residual_mul_div b hb t hbt j]
    exact add_sub_cancel _ _
  refine ⟨Q, ?_, hrow, hcol, ?_⟩
  · intro i j
    exact add_nonneg
      (by
        split_ifs
        · exact le_min (hr i) (hc i)
        · exact le_rfl)
      (div_nonneg (mul_nonneg (ha i) (hb j)) ht)
  · intro i
    simp [Q, hab i, d]

private lemma observed_le_margin_overlap {k : ℕ} (P : Fin k → Fin k → ℝ)
    (hP : IsTable P) : observed P ≤ ∑ i, min (rowMargin P i) (colMargin P i) := by
  apply Finset.sum_le_sum
  intro i _
  exact le_min
    (Finset.single_le_sum (fun j _ => hP.1 i j) (Finset.mem_univ i))
    (Finset.single_le_sum (fun j _ => hP.1 j i) (Finset.mem_univ i))

/-- **The maximum kappa for fixed margins** (Cohen 1960; derived): let `P` be a joint probability
table with chance agreement `p_e < 1`. Then (1) `κ(P) ≤ κ_max(P)`; (2) every joint probability
table `Q` with the same row and column margins as `P` has `κ(Q) ≤ κ_max(P)`; and (3) the bound is
attained: some joint probability table `Q` with the same row and column margins as `P` has
`κ(Q) = κ_max(P)`. So `κ_max(P)` is the maximum of `κ` over the tables with the margins of `P`.

Source: Cohen (1960). -/
public theorem kappa_le_kappaMax {k : ℕ} (P : Fin k → Fin k → ℝ) (hP : IsTable P)
    (he : chance P < 1) :
    kappa P ≤ kappaMax P ∧
      (∀ Q : Fin k → Fin k → ℝ, IsTable Q → (∀ i, rowMargin Q i = rowMargin P i) →
        (∀ j, colMargin Q j = colMargin P j) → kappa Q ≤ kappaMax P) ∧
      ∃ Q : Fin k → Fin k → ℝ, IsTable Q ∧ (∀ i, rowMargin Q i = rowMargin P i) ∧
        (∀ j, colMargin Q j = colMargin P j) ∧ kappa Q = kappaMax P
    := by
  have hbound : ∀ Q : Fin k → Fin k → ℝ, IsTable Q →
      (∀ i, rowMargin Q i = rowMargin P i) →
      (∀ j, colMargin Q j = colMargin P j) → kappa Q ≤ kappaMax P := by
    intro Q hQ hr hc
    have heq : chance Q = chance P := by simp only [chance, hr, hc]
    have ho := observed_le_margin_overlap Q hQ
    simp only [hr, hc] at ho
    unfold kappa kappaMax
    rw [heq]
    exact div_le_div_of_nonneg_right (sub_le_sub_right ho _) (sub_pos.mpr he).le
  refine ⟨hbound P hP (fun _ => rfl) (fun _ => rfl), hbound, ?_⟩
  have hr : ∀ i, 0 ≤ rowMargin P i :=
    fun i => Finset.sum_nonneg (fun j _ => hP.1 i j)
  have hc : ∀ j, 0 ≤ colMargin P j :=
    fun j => Finset.sum_nonneg (fun i _ => hP.1 i j)
  have hs : ∑ i, rowMargin P i = ∑ j, colMargin P j := Finset.sum_comm
  obtain ⟨Q, hQ, hrow, hcol, hdiag⟩ :=
    exists_table_with_diagonal (rowMargin P) (colMargin P) hr hc hs
  refine ⟨Q, ⟨hQ, ?_⟩, hrow, hcol, ?_⟩
  · change ∑ i, rowMargin Q i = 1
    simp only [hrow]
    exact hP.2
  · simp only [kappa, kappaMax, observed, hdiag, chance, hrow, hcol]

end WantedExt.Biology.StatisticalGenetics.CohenKappaWanted
