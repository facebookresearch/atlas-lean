/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Ecology.BoundaryESSStabilityIsESSIffIsLocallySuperior
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for ESS ⇔ local superiority

On the two-strategy coordination game with payoff matrix `A = [[2, 0], [0, 1]]`, the pure
strategy `p = (1, 0)` is an ESS, hence locally superior. On `B = [[0, 3], [1, 2]]`, the pure
strategy `r = (1, 0)` is beaten by `(0, 1)`, so it is not an ESS and hence not locally
superior. As a corollary, a locally superior state is a symmetric Nash equilibrium.
-/

@[expose] public section

open Matrix WantedExt.Biology.Ecology.BoundaryESSStabilityWanted

namespace DomainsTest.Biology.Ecology.BoundaryESSStabilityIsESSIffIsLocallySuperior

/-- The pure strategy `(1, 0)` is a mixed strategy. -/
private lemma mem_p : (![1, 0] : Fin 2 → ℝ) ∈ simplex (Fin 2) := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp
  · simp [Fin.sum_univ_two]

/-- The pure strategy `(0, 1)` is a mixed strategy. -/
private lemma mem_q : (![0, 1] : Fin 2 → ℝ) ∈ simplex (Fin 2) := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp
  · simp [Fin.sum_univ_two]

/-- The two pure strategies differ. -/
private lemma ne_pq : (![0, 1] : Fin 2 → ℝ) ≠ ![1, 0] := by
  intro h
  have h0 := congrFun h 0
  simp only [Matrix.cons_val_zero] at h0
  exact zero_ne_one h0

/-- First column of the coordination payoff matrix. -/
private lemma mulVec_A : !![2, 0; 0, 1] *ᵥ (![1, 0] : Fin 2 → ℝ) = ![2, 0] := by
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

/-- `(1, 0)` is an ESS of the coordination game `[[2, 0], [0, 1]]`. -/
private lemma ess_p : IsESS !![2, 0; 0, 1] ![1, 0] := by
  refine ⟨mem_p, fun q hq hqp => Or.inl ?_⟩
  obtain ⟨hq0, hq1⟩ := hq
  have hsum : q 0 + q 1 = 1 := by
    have h := hq1
    rwa [Fin.sum_univ_two] at h
  have hq0le : q 0 ≤ 1 := by linarith [hq0 0, hq0 1, hsum]
  have hq0ne : q 0 ≠ 1 := by
    intro hcon
    apply hqp
    have hq1eq : q 1 = 0 := by linarith [hsum, hcon]
    ext i
    fin_cases i
    · simpa using hcon
    · simpa using hq1eq
  have hlt : q 0 < 1 := lt_of_le_of_ne hq0le hq0ne
  rw [mulVec_A]
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num
  linarith [hlt]

/-- `(1, 0)` is locally superior for the coordination game `[[2, 0], [0, 1]]`. -/
example : IsLocallySuperior !![2, 0; 0, 1] ![1, 0] :=
  (isESS_iff_isLocallySuperior _ _).mp ess_p

/-- First column of the second payoff matrix. -/
private lemma mulVec_B : !![0, 3; 1, 2] *ᵥ (![1, 0] : Fin 2 → ℝ) = ![0, 1] := by
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

/-- `(1, 0)` is not an ESS of `[[0, 3], [1, 2]]`: it is beaten by `(0, 1)`. -/
private lemma not_ess_r : ¬ IsESS !![0, 3; 1, 2] ![1, 0] := by
  rintro ⟨-, hESS⟩
  have hq := hESS ![0, 1] mem_q ne_pq
  rw [mulVec_B] at hq
  norm_num [dotProduct, Fin.sum_univ_two] at hq

/-- `(1, 0)` is not locally superior for `[[0, 3], [1, 2]]`. -/
example : ¬ IsLocallySuperior !![0, 3; 1, 2] ![1, 0] :=
  (isESS_iff_isLocallySuperior _ _).not.mp not_ess_r

/-- A locally superior state is a symmetric Nash equilibrium. -/
example {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} {p : ι → ℝ}
    (h : IsLocallySuperior A p) (q : ι → ℝ) (hq : q ∈ simplex ι) :
    q ⬝ᵥ A *ᵥ p ≤ p ⬝ᵥ A *ᵥ p := by
  obtain ⟨-, hESS⟩ := (isESS_iff_isLocallySuperior A p).mpr h
  by_cases hqp : q = p
  · rw [hqp]
  · rcases hESS q hq hqp with hlt | ⟨heq, -⟩
    · exact hlt.le
    · exact heq.le

end DomainsTest.Biology.Ecology.BoundaryESSStabilityIsESSIffIsLocallySuperior
