/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Mechanics.HarmonicMechanics

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Checks for classical balance laws and harmonic mechanics

Exact compiling checks for `PhyslibExt.Mechanics.HarmonicMechanics`:
oscillator frequency, energy derivative and conservation along the explicit
solution, force/moment balance and work examples (including
`isEquilibrated_iff`, `moment2D_add`, `totalWork_add`), the fixed-end two-mass
chain with normal modes, every spring-network theorem applied to that chain,
the empty node type (the kernel identity is trivial there and positive
definiteness vacuous), and `#print axioms` for every public lemma.
-/

@[expose] public section

open scoped Matrix
open scoped BigOperators

open PhyslibExt.Mechanics.HarmonicMechanics

namespace PhyslibExtTest.Mechanics.HarmonicMechanics

/-! ## Oscillator checks: m = 1, k = 4 gives ω = 2, energy 2 * A ^ 2. -/

/-- Frequency check: `Real.sqrt (4 / 1) = 2`. -/
example : (2 : ℝ) = Real.sqrt ((4 : ℝ) / 1) := by
  have h4 : (4 : ℝ) / 1 = 2 ^ 2 := by norm_num
  rw [h4]
  exact (Real.sqrt_sq (by norm_num)).symm

/-- Explicit solution with `A = 1` has constant energy `2` at `t = 0`. -/
example : oscillatorEnergy 1 4 (1 * Real.cos (2 * 0))
    (-1 * 2 * Real.sin (2 * 0)) = 2 := by
  have hω : (2 : ℝ) = Real.sqrt ((4 : ℝ) / 1) := by
    have h4 : (4 : ℝ) / 1 = 2 ^ 2 := by norm_num
    rw [h4]
    exact (Real.sqrt_sq (by norm_num)).symm
  have hE := (oscillator_explicit_solution 1 4 1 2 0 zero_lt_one
    (by norm_num) hω).2.2
  rw [hE]
  norm_num

/-- Explicit solution with `A = 1` has constant energy `2` at `t = π / 4`. -/
example : oscillatorEnergy 1 4 (1 * Real.cos (2 * (Real.pi / 4)))
    (-1 * 2 * Real.sin (2 * (Real.pi / 4))) = 2 := by
  have hω : (2 : ℝ) = Real.sqrt ((4 : ℝ) / 1) := by
    have h4 : (4 : ℝ) / 1 = 2 ^ 2 := by norm_num
    rw [h4]
    exact (Real.sqrt_sq (by norm_num)).symm
  have hE := (oscillator_explicit_solution 1 4 1 2 (Real.pi / 4) zero_lt_one
    (by norm_num) hω).2.2
  rw [hE]
  norm_num

/-- Positive example: constant energy `2 * A ^ 2` for general `A`. -/
example (A : ℝ) : oscillatorEnergy 1 4 (A * Real.cos (2 * 0))
    (-A * 2 * Real.sin (2 * 0)) = 2 * A ^ 2 := by
  have hω : (2 : ℝ) = Real.sqrt ((4 : ℝ) / 1) := by
    have h4 : (4 : ℝ) / 1 = 2 ^ 2 := by norm_num
    rw [h4]
    exact (Real.sqrt_sq (by norm_num)).symm
  have hE := (oscillator_explicit_solution 1 4 A 2 0 zero_lt_one
    (by norm_num) hω).2.2
  rw [hE]
  ring

/-- Zero-displacement/zero-velocity boundary: energy at `x = 0, v = 0`
is `0`. -/
example (m k : ℝ) : oscillatorEnergy m k 0 0 = 0 := by
  unfold oscillatorEnergy
  ring

/-- `ω = 2` is `Real.sqrt (k / m)` for `m = 1`, `k = 4`. -/
private lemma two_eq_sqrt : (2 : ℝ) = Real.sqrt ((4 : ℝ) / 1) := by
  have h4 : (4 : ℝ) / 1 = 2 ^ 2 := by norm_num
  rw [h4]
  exact (Real.sqrt_sq (by norm_num)).symm

/-- Energy derivative at `t = 0` along the explicit solution (`m = 1`, `k = 4`, `A = 1`),
from the derivative hypotheses at `t = 0` alone. -/
example : HasDerivAt (fun t => oscillatorEnergy 1 4 (1 * Real.cos (2 * t))
    (-1 * 2 * Real.sin (2 * t))) 0 0 :=
  hasDerivAt_oscillatorEnergy 1 4 (fun t => 1 * Real.cos (2 * t))
    (fun t => -1 * 2 * Real.sin (2 * t)) 0 one_ne_zero
    (oscillator_explicit_solution 1 4 1 2 0 zero_lt_one (by norm_num) two_eq_sqrt).1
    (oscillator_explicit_solution 1 4 1 2 0 zero_lt_one (by norm_num) two_eq_sqrt).2.1

/-- Energy conservation along the explicit solution (`m = 1`, `k = 4`, `A = 1`): its derivative
hypotheses hold at every time, so the energy at `t = 0` equals the energy at `t = 1`. -/
example : oscillatorEnergy 1 4 (1 * Real.cos (2 * 0)) (-1 * 2 * Real.sin (2 * 0)) =
    oscillatorEnergy 1 4 (1 * Real.cos (2 * 1)) (-1 * 2 * Real.sin (2 * 1)) :=
  oscillatorEnergy_const 1 4 (fun t => 1 * Real.cos (2 * t))
    (fun t => -1 * 2 * Real.sin (2 * t)) one_ne_zero
    (fun t => (oscillator_explicit_solution 1 4 1 2 t zero_lt_one (by norm_num)
      two_eq_sqrt).1)
    (fun t => (oscillator_explicit_solution 1 4 1 2 t zero_lt_one (by norm_num)
      two_eq_sqrt).2.1) 0 1

/-- Newton's equation is needed for conservation: `x t = t`, `v t = 1` has `x' = v` at every
time, but with `m = k = 1` its energy is `1 / 2` at `t = 0` and `1` at `t = 1`. -/
example : (∀ t, HasDerivAt (fun t : ℝ => t) ((fun _ : ℝ => (1 : ℝ)) t) t) ∧
    oscillatorEnergy 1 1 ((fun t : ℝ => t) 0) ((fun _ : ℝ => (1 : ℝ)) 0) ≠
      oscillatorEnergy 1 1 ((fun t : ℝ => t) 1) ((fun _ : ℝ => (1 : ℝ)) 1) :=
  ⟨fun t => hasDerivAt_id' t, by norm_num [oscillatorEnergy]⟩

/-! ## Balance checks: 3-force equilibrium, pairs, and non-equilibrium. -/

/-- Exact 3-force example in 2D: zero resultant. -/
example : resultantForce (![![(1 : ℝ), 1], ![(-1), 0], ![0, (-1)]] :
    Fin 3 → (Fin 2 → ℝ)) = ![0, 0] := by
  funext i
  fin_cases i
  · simp only [resultantForce]
    rw [Fin.sum_univ_three]
    show ((1 : ℝ) + (-1)) + 0 = 0
    norm_num
  · simp only [resultantForce]
    rw [Fin.sum_univ_three]
    show ((1 : ℝ) + 0) + (-1) = 0
    norm_num

/-- Exact 3-force example in 2D: zero moment. -/
example : moment2D (![![(1 : ℝ), 0], ![0, 1], ![2, 1]] :
    Fin 3 → (Fin 2 → ℝ))
    (![![1, 1], ![(-1), 0], ![0, (-1)]] : Fin 3 → (Fin 2 → ℝ)) = 0 := by
  simp only [moment2D]
  rw [Fin.sum_univ_three]
  show ((1 * 1 - 0 * 1) + (0 * 0 - 1 * (-1))) + (2 * (-1) - 1 * 0) = (0 : ℝ)
  norm_num

/-- Action-reaction cancellation for vector-valued difference families,
via the real-valued lemma applied pointwise. -/
example (G : Fin 2 → (Fin 2 → ℝ)) :
    ∑ p : Fin 2 × Fin 2, (G p.2 - G p.1) = 0 := by
  funext k
  simp only [Finset.sum_apply, Pi.zero_apply]
  apply sum_pairwise_antisymmetric_eq_zero
  intro i j
  show (G i - G j) k = -((G j - G i) k)
  simp only [Pi.sub_apply]
  ring

/-- Action-reaction pair values: `F (0, 1) = ![-1, 1]`. -/
example : ((![![(1 : ℝ), 0], ![0, 1]] : Fin 2 → (Fin 2 → ℝ)) 1 -
    (![![1, 0], ![0, 1]] : Fin 2 → (Fin 2 → ℝ)) 0) = ![(-1), 1] := by
  funext i
  fin_cases i
  · show (0 : ℝ) - 1 = (-1)
    norm_num
  · show (1 : ℝ) - 0 = 1
    norm_num

/-- Action-reaction pair values: `F (1, 0) = ![1, -1]`, cancelling
the above. -/
example : ((![![(1 : ℝ), 0], ![0, 1]] : Fin 2 → (Fin 2 → ℝ)) 0 -
    (![![1, 0], ![0, 1]] : Fin 2 → (Fin 2 → ℝ)) 1) = ![1, (-1)] := by
  funext i
  fin_cases i
  · show (1 : ℝ) - 0 = 1
    norm_num
  · show (0 : ℝ) - 1 = (-1)
    norm_num

/-- One central pair (stiffness scalar `c = 2`) about `o = ![1, 1]` has
zero moment; the inferred type is the zero-moment equation. -/
example := central_pair_moment_eq_zero (![0, 0] : Fin 2 → ℝ) ![3, 4] ![1, 1] 2

/-- Non-equilibrium example: the resultant is `![1, 1]`. -/
example : resultantForce (![![(1 : ℝ), 0], ![0, 1]] :
    Fin 2 → (Fin 2 → ℝ)) = ![1, 1] := by
  funext i
  fin_cases i
  · simp only [resultantForce]
    rw [Fin.sum_univ_two]
    show (1 : ℝ) + 0 = 1
    norm_num
  · simp only [resultantForce]
    rw [Fin.sum_univ_two]
    show (0 : ℝ) + 1 = 1
    norm_num

/-- Non-equilibrium example: the failing quantity is the nonzero
resultant. -/
example : resultantForce (![![(1 : ℝ), 0], ![0, 1]] :
    Fin 2 → (Fin 2 → ℝ)) ≠ 0 := by
  have h : resultantForce (![![(1 : ℝ), 0], ![0, 1]] :
      Fin 2 → (Fin 2 → ℝ)) = ![1, 1] := by
    funext i
    fin_cases i
    · simp only [resultantForce]
      rw [Fin.sum_univ_two]
      show (1 : ℝ) + 0 = 1
      norm_num
    · simp only [resultantForce]
      rw [Fin.sum_univ_two]
      show (0 : ℝ) + 1 = 1
      norm_num
  rw [h]
  intro hcon
  have h0 := congrFun hcon 0
  simp at h0

/-- An action-reaction pair `(-1, 1)`, `(1, -1)` is in equilibrium, through
`isEquilibrated_iff`. -/
example : IsEquilibrated (![![(-1 : ℝ), 1], ![1, -1]] : Fin 2 → (Fin 2 → ℝ)) := by
  rw [isEquilibrated_iff, Fin.sum_univ_two]
  funext i
  fin_cases i <;> norm_num

/-- `moment2D_add`: at positions `(1, 0)` and `(0, 1)` the force families
`((0, 1), (0, 0))` and `((0, 0), (-1, 0))` each have moment `1`, so their sum has moment `2`. -/
example : moment2D (![![(1 : ℝ), 0], ![0, 1]] : Fin 2 → (Fin 2 → ℝ))
    (fun i => (![![0, 1], ![0, 0]] : Fin 2 → (Fin 2 → ℝ)) i + ![![0, 0], ![-1, 0]] i) = 2 := by
  rw [moment2D_add]
  simp only [moment2D, Fin.sum_univ_two]
  norm_num

/-- `totalWork_add`: under the displacement `(3, 4)` the forces `(1, 0)` and `(0, 1)` do work
`3` and `4`, so their sum does work `7`. -/
example : totalWork (fun r => (![![(1 : ℝ), 0]] : Fin 1 → (Fin 2 → ℝ)) r + ![![0, 1]] r)
    ![3, 4] = 7 := by
  rw [totalWork_add]
  simp only [totalWork, Fin.sum_univ_one, Fin.sum_univ_two]
  norm_num

/-! ## Spring checks: fixed-end two-mass chain, modes, free countermodel. -/

/-- Fixed-end two-mass chain stiffness: `K = [[2, -1], [-1, 2]]`. -/
private lemma chain_stiffness :
    stiffnessMatrix (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ)
      (![1, 1] : Fin 2 → ℝ) = Matrix.of
      ![((![2, (-1)] : Fin 2 → ℝ)), (((![(-1), 2] : Fin 2 → ℝ)))] := by
  funext i j
  fin_cases i <;> fin_cases j
  · rw [stiffnessMatrix_apply_diag]
    simp only [Fin.sum_univ_two]
    show ((0 : ℝ) + 1) + 1 = 2
    norm_num
  · rw [stiffnessMatrix_apply_offdiag]
    show (-1 : ℝ) = -1
    norm_num
    decide
  · rw [stiffnessMatrix_apply_offdiag]
    show (-1 : ℝ) = -1
    norm_num
    decide
  · rw [stiffnessMatrix_apply_diag]
    simp only [Fin.sum_univ_two]
    show ((1 : ℝ) + 0) + 1 = 2
    norm_num

/-- Energy of `(1, 1)` is `1` (wall springs only; coupling unstretched). -/
example : springEnergy (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ)
    (![1, 1] : Fin 2 → ℝ) (![1, 1] : Fin 2 → ℝ) = 1 := by
  simp only [springEnergy, Fin.sum_univ_two]
  show (1 / 4 : ℝ) * ((0 * (1 - 1) ^ 2 + 1 * (1 - 1) ^ 2) +
    (1 * (1 - 1) ^ 2 + 0 * (1 - 1) ^ 2)) +
    (1 / 2) * ((1 * 1 ^ 2) + (1 * 1 ^ 2)) = 1
  norm_num

/-- Energy of `(1, -1)` is `3` (coupling contributes `2`, walls `1`). -/
example : springEnergy (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ)
    (![1, 1] : Fin 2 → ℝ) (![1, (-1)] : Fin 2 → ℝ) = 3 := by
  simp only [springEnergy, Fin.sum_univ_two]
  show (1 / 4 : ℝ) * ((0 * (1 - 1) ^ 2 + 1 * ((-1) - 1) ^ 2) +
    (1 * (1 - (-1)) ^ 2 + 0 * ((-1) - (-1)) ^ 2)) +
    (1 / 2) * ((1 * 1 ^ 2) + (1 * (-1) ^ 2)) = 3
  norm_num

/-- Mode equation `K *ᵥ (1, 1) = 1 • (1, 1)`, frequency `1`. -/
example : stiffnessMatrix (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ)
    (![1, 1] : Fin 2 → ℝ) *ᵥ ![1, 1] = (1 : ℝ) • (![1, 1] : Fin 2 → ℝ) := by
  rw [chain_stiffness]
  funext i
  fin_cases i
  · simp only [Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    show (2 : ℝ) * 1 + (-1) * 1 = 1 * 1
    norm_num
  · simp only [Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    show (-1 : ℝ) * 1 + 2 * 1 = 1 * 1
    norm_num

/-- Mode equation `K *ᵥ (1, -1) = 3 • (1, -1)`,
frequency `Real.sqrt 3`. -/
example : stiffnessMatrix (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ)
    (![1, 1] : Fin 2 → ℝ) *ᵥ ![1, (-1)] = (3 : ℝ) • (![1, (-1)] : Fin 2 → ℝ) := by
  rw [chain_stiffness]
  funext i
  fin_cases i
  · simp only [Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    show (2 : ℝ) * 1 + (-1) * (-1) = 3 * 1
    norm_num
  · simp only [Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    show (-1 : ℝ) * 1 + 2 * (-1) = 3 * (-1)
    norm_num

/-- Mass-orthogonality of the two chain modes (unit masses). -/
example : innerProductM (![1, 1] : Fin 2 → ℝ) (![1, 1] : Fin 2 → ℝ)
    (![1, (-1)] : Fin 2 → ℝ) = 0 := by
  simp only [innerProductM, Fin.sum_univ_two]
  show (1 : ℝ) * 1 * 1 + 1 * 1 * (-1) = 0
  norm_num

/-- Free-network stiffness: `K = [[1, -1], [-1, 1]]`. -/
private lemma chain_stiffness_free :
    stiffnessMatrix (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ)
      (0 : Fin 2 → ℝ) = Matrix.of
      ![((![1, (-1)] : Fin 2 → ℝ)), (((![(-1), 1] : Fin 2 → ℝ)))] := by
  funext i j
  fin_cases i <;> fin_cases j
  · rw [stiffnessMatrix_apply_diag]
    simp only [Fin.sum_univ_two]
    show ((0 : ℝ) + 1) + 0 = 1
    norm_num
  · rw [stiffnessMatrix_apply_offdiag]
    show (-1 : ℝ) = -1
    norm_num
    decide
  · rw [stiffnessMatrix_apply_offdiag]
    show (-1 : ℝ) = -1
    norm_num
    decide
  · rw [stiffnessMatrix_apply_diag]
    simp only [Fin.sum_univ_two]
    show ((1 : ℝ) + 0) + 0 = 1
    norm_num

/-- Free-network countermodel: `K *ᵥ (1, 1) = 0`. -/
example : stiffnessMatrix (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ)
    (0 : Fin 2 → ℝ) *ᵥ ![1, 1] = 0 := by
  rw [chain_stiffness_free]
  funext i
  fin_cases i
  · simp only [Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Pi.zero_apply]
    show (1 : ℝ) * 1 + (-1) * 1 = 0
    norm_num
  · simp only [Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Pi.zero_apply]
    show (-1 : ℝ) * 1 + 1 * 1 = 0
    norm_num

/-- The free-network stiffness matrix is not `0`, so its zero mode `(1, 1)` is not
the trivial case `K = 0`. -/
example : stiffnessMatrix (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ)
    (0 : Fin 2 → ℝ) ≠ 0 := by
  rw [chain_stiffness_free]
  intro hcon
  have h00 := congrFun (congrFun hcon 0) 0
  simp at h00

/-! ## Spring theorems applied to the two-mass chain. -/

/-- The chain's pair stiffness is symmetric. -/
private lemma chain_symm : ∀ i j, (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ) i j =
    (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ) j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The chain has no self-springs. -/
private lemma chain_diag : ∀ i, (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ) i i = 0 := by
  intro i
  fin_cases i <;> rfl

/-- The chain's pair stiffnesses are nonnegative. -/
private lemma chain_nonneg : ∀ i j, 0 ≤ (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ) i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- The unit wall stiffnesses (and unit masses) are positive. -/
private lemma ones_pos : ∀ i, 0 < (![1, 1] : Fin 2 → ℝ) i := by
  intro i
  fin_cases i <;> norm_num

/-- Mode `(1, 1)` with eigenvalue `1` and unit masses, in the form of `innerProductM_eq_zero_of_ne`
and `rayleigh_nonneg`. -/
private lemma chain_mode_one :
    stiffnessMatrix (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ) ![1, 1] *ᵥ ![1, 1] =
      (1 : ℝ) • (fun i => (![1, 1] : Fin 2 → ℝ) i * (![1, 1] : Fin 2 → ℝ) i) := by
  rw [chain_stiffness]
  funext i
  fin_cases i
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    show (2 : ℝ) * 1 + (-1) * 1 = 1 * (1 * 1)
    norm_num
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    show (-1 : ℝ) * 1 + 2 * 1 = 1 * (1 * 1)
    norm_num

/-- Mode `(1, -1)` with eigenvalue `3` and unit masses. -/
private lemma chain_mode_three :
    stiffnessMatrix (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ) ![1, 1] *ᵥ ![1, -1] =
      (3 : ℝ) • (fun i => (![1, 1] : Fin 2 → ℝ) i * (![1, -1] : Fin 2 → ℝ) i) := by
  rw [chain_stiffness]
  funext i
  fin_cases i
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    show (2 : ℝ) * 1 + (-1) * (-1) = 3 * (1 * 1)
    norm_num
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    show (-1 : ℝ) * 1 + 2 * (-1) = 3 * (1 * (-1))
    norm_num

/-- `springEnergy_eq_quadForm`: half the stiffness quadratic form at `(1, -1)` is the
energy `3` computed above. -/
example : (1 / 2 : ℝ) * dotProduct ![1, -1]
    (stiffnessMatrix (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ) ![1, 1] *ᵥ ![1, -1]) =
      3 := by
  rw [← springEnergy_eq_quadForm _ _ _ chain_symm chain_diag]
  simp only [springEnergy, Fin.sum_univ_two]
  show (1 / 4 : ℝ) * ((0 * (1 - 1) ^ 2 + 1 * ((-1) - 1) ^ 2) +
    (1 * (1 - (-1)) ^ 2 + 0 * ((-1) - (-1)) ^ 2)) +
    (1 / 2) * ((1 * 1 ^ 2) + (1 * (-1) ^ 2)) = 3
  norm_num

/-- `springEnergy_nonneg`: every displacement of the fixed-end chain has nonnegative energy. -/
example (u : Fin 2 → ℝ) :
    0 ≤ springEnergy (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ) ![1, 1] u :=
  springEnergy_nonneg _ _ u chain_nonneg fun i => (ones_pos i).le

/-- `stiffnessMatrix_transpose`: the chain's stiffness matrix is symmetric. -/
example : (stiffnessMatrix (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ) ![1, 1])ᵀ =
    stiffnessMatrix (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ) ![1, 1] :=
  stiffnessMatrix_transpose _ _ chain_symm

/-- `stiffnessMatrix_mulVec_one`: the row sums of the fixed-end chain are its wall
stiffnesses `(1, 1)`. -/
example : stiffnessMatrix (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ) ![1, 1] *ᵥ
    (fun _ => 1) = ![1, 1] :=
  stiffnessMatrix_mulVec_one _ _ chain_diag

/-- `stiffnessMatrix_fixedEnds_rowNonzero`: with a wall spring at node `0`, the translation
`(1, 1)` is not a zero mode. -/
example : (stiffnessMatrix (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ) ![1, 1] *ᵥ
    (fun _ => 1)) 0 ≠ 0 :=
  stiffnessMatrix_fixedEnds_rowNonzero _ _ 0 chain_diag (ones_pos 0)

/-- `stiffnessMatrix_free_zeroMode`: without walls the translation is a zero mode. -/
example : stiffnessMatrix (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ) 0 *ᵥ
    (fun _ => 1) = 0 :=
  stiffnessMatrix_free_zeroMode _ chain_diag

/-- `stiffnessMatrix_free_not_posDef`: the free chain's stiffness matrix `[[1, -1], [-1, 1]]` is
not positive definite. -/
example : ¬ (stiffnessMatrix (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ) 0).PosDef :=
  stiffnessMatrix_free_not_posDef _ chain_diag

/-- `springEnergy_free_const`: a translation of the free chain stores no energy. -/
example : springEnergy (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ) 0 (fun _ => 5) = 0 :=
  springEnergy_free_const _ 5

/-- `innerProductM_eq_zero_of_ne`: the chain modes `(1, 1)` and `(1, -1)` have the distinct
eigenvalues `1` and `3`, so they are orthogonal for the unit masses. -/
example : innerProductM (![1, 1] : Fin 2 → ℝ) ![1, 1] ![1, -1] = 0 :=
  innerProductM_eq_zero_of_ne _ _ _ _ 1 3 (by norm_num)
    (stiffnessMatrix_transpose _ _ chain_symm) chain_mode_one chain_mode_three

/-- `rayleigh_nonneg`: every generalized eigenvalue of the fixed-end chain with unit masses is
nonnegative. -/
example (lam : ℝ) (v : Fin 2 → ℝ) (hv : v ≠ 0)
    (heig : stiffnessMatrix (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ) ![1, 1] *ᵥ v =
      lam • (fun i => (![1, 1] : Fin 2 → ℝ) i * v i)) :
    0 ≤ lam :=
  rayleigh_nonneg _ _ _ v lam chain_symm chain_diag chain_nonneg (fun i => (ones_pos i).le)
    ones_pos hv heig

/-! ## Boundary: the empty node type. -/

/-- `stiffnessMatrix_free_zeroMode` on the empty node type `Fin 0`: the kernel identity still
holds. -/
example (k : Fin 0 → Fin 0 → ℝ) : stiffnessMatrix k 0 *ᵥ (fun _ => (1 : ℝ)) = 0 :=
  stiffnessMatrix_free_zeroMode k fun i => i.elim0

/-- On `Fin 0` the all-ones vector is the zero vector, so that kernel identity is trivial. -/
example : (fun _ : Fin 0 => (1 : ℝ)) = 0 :=
  Subsingleton.elim _ _

/-- `[Nonempty ι]` is needed in `stiffnessMatrix_free_not_posDef`: on `Fin 0` the free stiffness
matrix is positive definite, vacuously, since its only vector is `0`. -/
example (k : Fin 0 → Fin 0 → ℝ) : (stiffnessMatrix k 0).PosDef :=
  Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.IsHermitian.ext fun i => i.elim0)
    fun x hx => (hx (Subsingleton.elim x 0)).elim

/-! ## Axiom audits for every public lemma. -/

#print axioms PhyslibExt.Mechanics.HarmonicMechanics.hasDerivAt_oscillatorEnergy
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.oscillatorEnergy_const
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.oscillator_explicit_solution
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.isEquilibrated_iff
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.sum_pairwise_antisymmetric_eq_zero
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.moment2D_add
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.central_pair_moment_eq_zero
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.totalWork_add
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.stiffnessMatrix_apply_diag
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.stiffnessMatrix_apply_offdiag
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.springEnergy_eq_quadForm
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.springEnergy_nonneg
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.stiffnessMatrix_transpose
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.stiffnessMatrix_mulVec_one
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.stiffnessMatrix_free_zeroMode
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.stiffnessMatrix_free_not_posDef
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.springEnergy_free_const
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.stiffnessMatrix_fixedEnds_rowNonzero
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.innerProductM_eq_zero_of_ne
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.rayleigh_nonneg

end PhyslibExtTest.Mechanics.HarmonicMechanics
