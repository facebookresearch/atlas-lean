/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Mechanics.HarmonicMechanics
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Checks for classical balance laws, harmonic mechanics, continuum bookkeeping

Exact compiling checks for `PhyslibExt.Mechanics.HarmonicMechanics`:
oscillator frequency and constant energy, force/moment balance examples, the
fixed-end two-mass chain with normal modes, continuum traction/strain
conversion, and `#print axioms` for every public lemma.
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

/-- Free-network countermodel: `K ≠ 0`, so `K` is not positive definite. -/
example : stiffnessMatrix (![![(0 : ℝ), 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ)
    (0 : Fin 2 → ℝ) ≠ 0 := by
  rw [chain_stiffness_free]
  intro hcon
  have h00 := congrFun (congrFun hcon 0) 0
  simp at h00

/-! ## Continuum checks: hydrostatic traction, faces, strain conversion. -/

/-- Test displacement gradient: `H 0 1 = 1 / 2`, `H 1 0 = 0`, else `0`. -/
private noncomputable def strainH : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![(0 : ℝ), 1 / 2, 0], ![0, 0, 0], ![0, 0, 0]]

/-- Hydrostatic tension: `σ = 2 • I`, `n = ![0, 0, 1]` gives
`![0, 0, 2]`. -/
example : traction ((2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ))
    (![0, 0, 1] : Fin 3 → ℝ) = ![0, 0, 2] := by
  have h := traction_hydrostatic (show (0 : ℝ) < 2 by norm_num)
    (![0, 0, 1] : Fin 3 → ℝ)
  rw [h]
  funext i
  fin_cases i
  · show (2 : ℝ) * 0 = 0
    norm_num
  · show (2 : ℝ) * 0 = 0
    norm_num
  · show (2 : ℝ) * 1 = 2
    norm_num

/-- Opposite-face check: traction on `-n` is `![0, 0, -2]`. -/
example : traction ((2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ))
    (-(![0, 0, 1] : Fin 3 → ℝ)) = ![0, 0, (-2)] := by
  have hrec := traction_reciprocity ((2 : ℝ) • 1) (![0, 0, 1] : Fin 3 → ℝ)
  have hhyd := traction_hydrostatic (show (0 : ℝ) < 2 by norm_num)
    (![0, 0, 1] : Fin 3 → ℝ)
  rw [hrec, hhyd]
  funext i
  fin_cases i
  · show (-((2 : ℝ) * 0)) = 0
    norm_num
  · show (-((2 : ℝ) * 0)) = 0
    norm_num
  · show (-((2 : ℝ) * 1)) = (-2)
    norm_num

/-- Tensor shear conversion: `(infStrain H) 0 1 = 1 / 4`. -/
example : infStrain strainH 0 1 = 1 / 4 := by
  rw [infStrain_offdiag _ 0 1 (show (0 : Fin 3) ≠ 1 by decide)]
  show (((1 / 2 : ℝ)) + 0) / 2 = 1 / 4
  norm_num

/-- Engineering shear conversion: `engShear H 0 1 = 1 / 2`. -/
example : engShear strainH 0 1 = 1 / 2 := by
  rw [engShear_eq _ 0 1 (show (0 : Fin 3) ≠ 1 by decide)]
  show ((1 / 2 : ℝ)) + 0 = 1 / 2
  norm_num

/-- Diagonal strain agrees with `H` on the explicit example. -/
example : infStrain strainH 0 0 = strainH 0 0 := by
  rw [infStrain_diag]

/-- Countermodel: asymmetric `H` shows tensor shear differs from
`H 0 1`. -/
example : infStrain strainH 0 1 ≠ strainH 0 1 := by
  rw [infStrain_offdiag _ 0 1 (show (0 : Fin 3) ≠ 1 by decide)]
  show (((1 / 2 : ℝ)) + 0) / 2 ≠ (1 / 2 : ℝ)
  norm_num

/-! ## Axiom audits for every public lemma. -/

#print axioms PhyslibExt.Mechanics.HarmonicMechanics.oscillatorEnergy_conserved
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
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.springEnergy_free_const
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.stiffnessMatrix_fixedEnds_rowNonzero
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.innerProductM_eq_zero_of_ne
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.rayleigh_nonneg
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.det_volume_pos
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.det_composition
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.traction_hydrostatic
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.traction_reciprocity
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.infStrain_symmetric
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.infStrain_diag
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.infStrain_offdiag
#print axioms PhyslibExt.Mechanics.HarmonicMechanics.engShear_eq

end PhyslibExtTest.Mechanics.HarmonicMechanics
