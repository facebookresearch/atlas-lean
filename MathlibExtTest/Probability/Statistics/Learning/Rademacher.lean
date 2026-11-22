/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.BigOperators
public import MathlibExt.Probability.Statistics.Learning.Rademacher

/-! # Tests for `MathlibExt.Probability.Statistics.Learning.Rademacher` -/

@[expose] public section

open Finset ProbabilityTheory

namespace MathlibExtTest.Probability.Statistics.Learning.Rademacher

/-- Zero-function class: complexity `0`. -/
example (n : ℕ) : empiricalRademacher ({0} : Finset (Fin n → ℝ)) = 0 := by
  exact empiricalRademacher_singleton _

/-- One-sided convention: a single nonzero vector has complexity `0`; the absolute-value
convention would give `1` here. -/
example : empiricalRademacher ({fun _ => 1} : Finset (Fin 1 → ℝ)) = 0 := by
  exact empiricalRademacher_singleton _

/-- Two-vector class (registry positive check): the value is `1 / 4`. The absolute-value
convention gives `1 / 2`, and dropping the `1 / n` factor also gives `1 / 2`. -/
example : empiricalRademacher ({![1, 0], ![0, 1]} : Finset (Fin 2 → ℝ)) = 1 / 4 := by
  rw [empiricalRademacher_eq_sup' (Finset.insert_nonempty _ _),
    ← Equiv.sum_comp (piFinTwoEquiv fun _ => Bool).symm _]
  simp [Fintype.sum_prod_type, piFinTwoEquiv_symm_apply,
    Fin.cons_zero, Fin.cons_one, Fin.sum_univ_two, Finset.sup'_insert,
    Finset.sup'_singleton]
  norm_num

/-- Empty class: complexity `0`. -/
example : empiricalRademacher (∅ : Finset (Fin 3 → ℝ)) = 0 := by
  exact empiricalRademacher_empty

/-- Boundary `n = 0`: the `(n : ℝ)⁻¹` factor is `0`, so every class has complexity `0`. -/
example (A : Finset (Fin 0 → ℝ)) : empiricalRademacher A = 0 := by
  by_cases hA : A.Nonempty
  · rw [empiricalRademacher_eq_sup' hA]
    simp [Finset.sup'_const]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hA, empiricalRademacher_empty]

/-- Negative scaling multiplies by `|c|`, not by `c`. -/
example (n : ℕ) (A : Finset (Fin n → ℝ)) :
    empiricalRademacher (A.image fun a => (-3 : ℝ) • a) = 3 * empiricalRademacher A := by
  rw [empiricalRademacher_image_smul]
  norm_num

/-- Boolean consumer shape: the left side of `rademacher_finite_class` for the constant
classifier on one sample point is `0`. -/
example :
    (∑ σ : Fin 1 → Bool,
      ({fun _ => true} : Finset (Fin 1 → Bool)).sup' (Finset.singleton_nonempty _)
        (fun h => ∑ i, (if σ i then (1 : ℝ) else -1) *
          (if h i then (1 : ℝ) else -1))) / 2 ^ 1 / ((1 : ℕ) : ℝ) = 0 := by
  rw [← empiricalRademacher_image_sign (Finset.singleton_nonempty (fun _ => true))]
  rw [Finset.image_singleton _ _]
  exact empiricalRademacher_singleton _

/-- Function-class consumer shape: a finite class `F` evaluated on a sample `S`. -/
example {Z : Type*} {n : ℕ} (F : Finset (Z → ℝ)) (S : Fin n → Z) :
    0 ≤ empiricalRademacher (F.image fun f i => f (S i)) := by
  exact empiricalRademacher_nonneg _

/-- Singleton boundary: `|A| = 1` gives `log 1 = 0`, so the bound is `0`; it holds only
because the one-sided convention gives a singleton complexity `0`. -/
theorem empiricalRademacher_le_massart_singleton {n : ℕ} (a : Fin n → ℝ) :
    empiricalRademacher ({a} : Finset (Fin n → ℝ)) ≤ 0 := by
  simpa using empiricalRademacher_le_massart (Finset.singleton_nonempty a)

/-- Boundary `n = 0`: the `/ n` factor makes the bound `0` without a `0 < n` hypothesis. -/
theorem empiricalRademacher_le_massart_fin_zero {A : Finset (Fin 0 → ℝ)} (hA : A.Nonempty) :
    empiricalRademacher A ≤ 0 := by
  simpa using empiricalRademacher_le_massart hA

/-- Zero function in the class: adding `0` to `{a}` leaves the radius `√(∑ aᵢ²)` unchanged
but makes `|A| = 2`. -/
theorem empiricalRademacher_le_massart_zero_pair {n : ℕ} {a : Fin n → ℝ} (ha : a ≠ 0) :
    empiricalRademacher ({0, a} : Finset (Fin n → ℝ)) ≤
      Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (2 * Real.log 2) / n := by
  have hA : ({0, a} : Finset (Fin n → ℝ)).Nonempty := Finset.insert_nonempty 0 {a}
  have h := empiricalRademacher_le_massart hA
  rw [Finset.card_pair (Ne.symm ha),
    Finset.sup'_insert (Finset.singleton_nonempty a), Finset.sup'_singleton] at h
  have hz : Real.sqrt (∑ i, (0 : Fin n → ℝ) i ^ 2) = 0 := by simp
  simp only [hz, sup_of_le_right (Real.sqrt_nonneg _), Nat.cast_ofNat] at h
  exact h

/-- Two standard basis vectors in `ℝ²` (complexity `1 / 4`): radius `1`, `|A| = 2`. -/
theorem empiricalRademacher_le_massart_basis_two :
    empiricalRademacher ({![1, 0], ![0, 1]} : Finset (Fin 2 → ℝ)) ≤
      Real.sqrt (2 * Real.log 2) / 2 := by
  have hA : ({![1, 0], ![0, 1]} : Finset (Fin 2 → ℝ)).Nonempty :=
    Finset.insert_nonempty _ _
  have h := empiricalRademacher_le_massart hA
  have hne : (![1, 0] : Fin 2 → ℝ) ≠ ![0, 1] := by
    intro hcon
    have h0 := congrFun hcon 0
    simp at h0
  rw [Finset.card_pair hne,
    Finset.sup'_insert (Finset.singleton_nonempty _), Finset.sup'_singleton] at h
  have e1 : Real.sqrt (∑ i, (![1, 0] : Fin 2 → ℝ) i ^ 2) = 1 := by
    simp [Fin.sum_univ_two]
  have e2 : Real.sqrt (∑ i, (![0, 1] : Fin 2 → ℝ) i ^ 2) = 1 := by
    simp [Fin.sum_univ_two]
  simp only [e1, e2, sup_idem, one_mul, Nat.cast_ofNat] at h
  exact h

/-- Scale linearity: the bound for `c • A` is `|c|` times the bound for `A`. -/
theorem empiricalRademacher_image_smul_le_massart {n : ℕ} {A : Finset (Fin n → ℝ)}
    (hA : A.Nonempty) (c : ℝ) :
    empiricalRademacher (A.image fun a => c • a) ≤
      |c| * (A.sup' hA (fun v => Real.sqrt (∑ i, v i ^ 2)) *
        Real.sqrt (2 * Real.log A.card) / n) := by
  rw [empiricalRademacher_image_smul]
  exact mul_le_mul_of_nonneg_left (empiricalRademacher_le_massart hA) (abs_nonneg c)

end MathlibExtTest.Probability.Statistics.Learning.Rademacher
