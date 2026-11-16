/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.PurificationOverlap
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt.Quantum.ClassicalFuchsVanDeGraaf MathlibExt.Quantum.PurificationOverlap

namespace MathlibExtTest.Quantum.PurificationOverlap

/-! ### The upper bound on a two-point system with a three-point environment -/

/-- Amplitudes with row weights `(1/2, 1/2)`. -/
noncomputable def A₁ : Fin 2 → Fin 3 → ℂ := ![![1 / 2, 1 / 2, 0], ![0, 1 / 2, 1 / 2]]

/-- Amplitudes with row weights `(1, 0)`. -/
noncomputable def B₁ : Fin 2 → Fin 3 → ℂ := ![![1, 0, 0], ![0, 0, 0]]

theorem rowWeights_A₁ : ∀ x, ∑ e, Complex.normSq (A₁ x e) = ![(1 / 2 : ℝ), 1 / 2] x := by
  intro x
  fin_cases x <;> norm_num [A₁, Fin.sum_univ_three]

theorem rowWeights_B₁ : ∀ x, ∑ e, Complex.normSq (B₁ x e) = ![(1 : ℝ), 0] x := by
  intro x
  fin_cases x <;> norm_num [B₁, Fin.sum_univ_three]

/-- The overlap of `A₁` and `B₁` is `1/2`. -/
theorem overlap_A₁_B₁ : ∑ x, ∑ e, (starRingEnd ℂ) (A₁ x e) * B₁ x e = 1 / 2 := by
  norm_num [A₁, B₁, Fin.sum_univ_two, Fin.sum_univ_three, map_ofNat]

/-- The Bhattacharyya coefficient of the row weights of `A₁` and `B₁` is `√(1/2)`. -/
theorem bhattacharyyaCoeff_p₁_q₁ :
    bhattacharyyaCoeff ![(1 / 2 : ℝ), 1 / 2] ![1, 0] = Real.sqrt (1 / 2) := by
  norm_num [bhattacharyyaCoeff, Fin.sum_univ_two]

/-- The bound applied to `A₁` and `B₁`: the overlap `1/2` (`overlap_A₁_B₁`) is at most the
coefficient `√(1/2)` (`bhattacharyyaCoeff_p₁_q₁`). -/
example : ‖∑ x, ∑ e, (starRingEnd ℂ) (A₁ x e) * B₁ x e‖
    ≤ bhattacharyyaCoeff ![(1 / 2 : ℝ), 1 / 2] ![1, 0] :=
  purification_overlap_le A₁ B₁ _ _ rowWeights_A₁ rowWeights_B₁

/-! ### Attainment -/

/-- The attaining arrays satisfy the hypotheses of `purification_overlap_le`, so they meet the
bound with equality. -/
example {X : Type*} [Fintype X] (p q : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) :
    ∃ A B : X → X → ℂ,
      ‖∑ x, ∑ e, (starRingEnd ℂ) (A x e) * B x e‖ ≤ bhattacharyyaCoeff p q ∧
      bhattacharyyaCoeff p q ≤ ‖∑ x, ∑ e, (starRingEnd ℂ) (A x e) * B x e‖ := by
  obtain ⟨A, B, hA, hB, -, -, h⟩ := exists_overlap_eq_bhattacharyyaCoeff p q hp0 hq0
  exact ⟨A, B, purification_overlap_le A B p q hA hB, h.ge⟩

/-- Without normalization the attaining arrays need not be unit vectors: for `p = q = 2` on a
point, the bound `2` is attained. -/
example : ∃ A B : Fin 1 → Fin 1 → ℂ,
    (∀ x, ∑ e, Complex.normSq (A x e) = 2) ∧ (∀ x, ∑ e, Complex.normSq (B x e) = 2) ∧
    ‖∑ x, ∑ e, (starRingEnd ℂ) (A x e) * B x e‖ = 2 := by
  obtain ⟨A, B, hA, hB, -, -, h⟩ :=
    exists_overlap_eq_bhattacharyyaCoeff (fun _ : Fin 1 => (2 : ℝ)) (fun _ => 2)
      (fun _ => by norm_num) (fun _ => by norm_num)
  refine ⟨A, B, hA, hB, h.trans ?_⟩
  rw [bhattacharyyaCoeff, Fin.sum_univ_one]
  exact Real.sqrt_mul_self (by norm_num)

/-- The Bhattacharyya coefficient of `p = (1/4, 3/4)` and `q = (1, 0)` is `√(1/4) = 1/2`. -/
theorem bhattacharyyaCoeff_p₂_q₂ :
    bhattacharyyaCoeff ![(1 / 4 : ℝ), 3 / 4] ![1, 0] = 1 / 2 := by
  rw [bhattacharyyaCoeff, Fin.sum_univ_two]
  have h0 : Real.sqrt (![(1 / 4 : ℝ), 3 / 4] 0 * ![(1 : ℝ), 0] 0) = 1 / 2 := by
    rw [show ![(1 / 4 : ℝ), 3 / 4] 0 * ![(1 : ℝ), 0] 0 = (1 / 2) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have h1 : Real.sqrt (![(1 / 4 : ℝ), 3 / 4] 1 * ![(1 : ℝ), 0] 1) = 0 := by simp
  rw [h0, h1, add_zero]

/-- For the probability vectors `p = (1/4, 3/4)` and `q = (1, 0)`, unit-vector purifications of
`diag p` and `diag q` reach overlap `1/2`, the largest value the bound allows. -/
example : ∃ A B : Fin 2 → Fin 2 → ℂ,
    (∀ x, ∑ e, Complex.normSq (A x e) = ![(1 / 4 : ℝ), 3 / 4] x) ∧
    (∀ x, ∑ e, Complex.normSq (B x e) = ![(1 : ℝ), 0] x) ∧
    (∀ x y, x ≠ y → ∑ e, A x e * (starRingEnd ℂ) (A y e) = 0) ∧
    (∀ x y, x ≠ y → ∑ e, B x e * (starRingEnd ℂ) (B y e) = 0) ∧
    ∑ x, ∑ e, Complex.normSq (A x e) = 1 ∧ ∑ x, ∑ e, Complex.normSq (B x e) = 1 ∧
    ‖∑ x, ∑ e, (starRingEnd ℂ) (A x e) * B x e‖ = 1 / 2 := by
  obtain ⟨A, B, hA, hB, hA', hB', hA1, hB1, h⟩ := exists_purification_overlap_eq
    ![(1 / 4 : ℝ), 3 / 4] ![1, 0] (by intro x; fin_cases x <;> norm_num)
    (by intro x; fin_cases x <;> norm_num) (by norm_num [Fin.sum_univ_two])
    (by norm_num [Fin.sum_univ_two])
  exact ⟨A, B, hA, hB, hA', hB', hA1, hB1, h.trans bhattacharyyaCoeff_p₂_q₂⟩

end MathlibExtTest.Quantum.PurificationOverlap

end
