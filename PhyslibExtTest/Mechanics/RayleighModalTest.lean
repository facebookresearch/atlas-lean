/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.RayleighModal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# Rayleigh damping and modal participation checks

Consumers of `PhyslibExt.Mechanics.RayleighModal`: stiffness- and
mass-proportional specializations, a rational repeated-mode witness,
invalid-basis and nonproportional-damping controls, and two-mass and
ring-of-three participation checks through the canonical modal basis.

## i. Overview

These are elaboration, non-vacuity and boundary checks, not new results.
The rational witness has modal values `(0, 3, 3)`, so it covers a rigid
mode and a repeated eigenvalue. The controls show that mass
orthonormality inside a repeated eigenspace and proportionality of the
damping are both needed.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Rayleigh damping checks
- B. Participation and effective-mass checks

## iv. References

- `PhyslibExt.Mechanics.RayleighModal`
- `PhyslibExt.Mechanics.ModalResponse`
-/

open Matrix

/-! ## A. Rayleigh damping checks -/

/-- Stiffness-proportional specialization of the damping definition. -/
example {n : Type*} [Fintype n] [DecidableEq n] (β : ℝ)
    (M K : Matrix n n ℝ) :
    PhyslibExt.Mechanics.RayleighModal.rayleighDamping 0 β M K = β • K := by
  simp [PhyslibExt.Mechanics.RayleighModal.rayleighDamping]

/-- Mass-proportional specialization of the damping definition. -/
example {n : Type*} [Fintype n] [DecidableEq n] (α : ℝ)
    (M K : Matrix n n ℝ) :
    PhyslibExt.Mechanics.RayleighModal.rayleighDamping α 0 M K = α • M := by
  simp [PhyslibExt.Mechanics.RayleighModal.rayleighDamping]

/-- Stiffness-proportional damping transform. -/
example {n : Type*} [Fintype n] [DecidableEq n] {M K Φ : Matrix n n ℝ}
    {μ : n → ℝ} (hMΦ : Φᵀ * M * Φ = 1) (hKΦ : Φᵀ * K * Φ = diagonal μ)
    (β : ℝ) :
    Φᵀ * PhyslibExt.Mechanics.RayleighModal.rayleighDamping 0 β M K * Φ
      = diagonal fun j => β * μ j := by
  simpa using
    PhyslibExt.Mechanics.RayleighModal.transpose_mul_rayleighDamping_mul
      hMΦ hKΦ 0 β

/-- Mass-proportional damping transform. -/
example {n : Type*} [Fintype n] [DecidableEq n] {M K Φ : Matrix n n ℝ}
    {μ : n → ℝ} (hMΦ : Φᵀ * M * Φ = 1) (hKΦ : Φᵀ * K * Φ = diagonal μ)
    (α : ℝ) :
    Φᵀ * PhyslibExt.Mechanics.RayleighModal.rayleighDamping α 0 M K * Φ
      = diagonal fun _ => α := by
  simpa using
    PhyslibExt.Mechanics.RayleighModal.transpose_mul_rayleighDamping_mul
      hMΦ hKΦ α 0

/-- Stiffness-proportional decoupling instance. -/
example {n : Type*} [Fintype n] [DecidableEq n] {M K Φ : Matrix n n ℝ}
    {μ : n → ℝ} (hMΦ : Φᵀ * M * Φ = 1) (hKΦ : Φᵀ * K * Φ = diagonal μ)
    (β : ℝ) (x f : ℝ → n → ℝ) (t : ℝ) :=
  PhyslibExt.Mechanics.RayleighModal.rayleigh_modal_decoupling
    hMΦ hKΦ 0 β x f t

/-- Mass-proportional decoupling instance. -/
example {n : Type*} [Fintype n] [DecidableEq n] {M K Φ : Matrix n n ℝ}
    {μ : n → ℝ} (hMΦ : Φᵀ * M * Φ = 1) (hKΦ : Φᵀ * K * Φ = diagonal μ)
    (α : ℝ) (x f : ℝ → n → ℝ) (t : ℝ) :=
  PhyslibExt.Mechanics.RayleighModal.rayleigh_modal_decoupling
    hMΦ hKΦ α 0 x f t

/-- Rational witness mass matrix. -/
private def witnessM3 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![3, -2, 1; -2, 2, -1; 1, -1, 1]

/-- Rational witness stiffness matrix. -/
private def witnessK3 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![6, -6, 3; -6, 6, -3; 3, -3, 3]

/-- Rational witness modal matrix. -/
private def witnessPhi3 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 1, 1, 0; 0, 1, 1]

/-- Rational witness modal values: one rigid mode and a repeated pair. -/
private def witnessMu3 : Fin 3 → ℝ := ![0, 3, 3]

/-- The witness basis is mass-orthonormal. -/
private lemma witnessM3_orthonormal :
    witnessPhi3ᵀ * witnessM3 * witnessPhi3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessM3, witnessPhi3, Matrix.mul_apply, Fin.sum_univ_three] <;>
    norm_num

/-- The witness basis diagonalizes the stiffness. -/
private lemma witnessK3_diagonal :
    witnessPhi3ᵀ * witnessK3 * witnessPhi3 = diagonal witnessMu3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessK3, witnessPhi3, witnessMu3, Matrix.mul_apply,
      Fin.sum_univ_three] <;> norm_num

/-- Repeated modes remain decoupled, with nonzero modal damping. -/
example :
    witnessPhi3ᵀ
        * PhyslibExt.Mechanics.RayleighModal.rayleighDamping
          (1 / 2) (1 / 10) witnessM3 witnessK3 * witnessPhi3
      = diagonal ![1 / 2, 4 / 5, 4 / 5] := by
  rw [PhyslibExt.Mechanics.RayleighModal.transpose_mul_rayleighDamping_mul
    witnessM3_orthonormal witnessK3_diagonal]
  congr 1
  funext j
  fin_cases j <;> simp [witnessMu3] <;> norm_num

/-- Decoupling instance on the repeated-mode witness. -/
example (x f : ℝ → Fin 3 → ℝ) (t : ℝ) :=
  PhyslibExt.Mechanics.RayleighModal.rayleigh_modal_decoupling
    witnessM3_orthonormal witnessK3_diagonal (1 / 2) (1 / 10) x f t

/-- The absolute-value trajectory is not differentiable at `0`. -/
example : ¬ DifferentiableAt ℝ (fun s : ℝ => |s|) 0 :=
  not_differentiableAt_abs_zero

/-- Totalized derivative: the decoupling equivalence still elaborates for
that non-differentiable trajectory. -/
example :=
  PhyslibExt.Mechanics.RayleighModal.rayleigh_modal_decoupling
    witnessM3_orthonormal witnessK3_diagonal 1 1 (fun s => fun _ => |s|)
    (fun _ => 0) 0

/-- A basis choice inside the repeated eigenspace that is not
mass-orthonormal there. -/
private def witnessPsi3 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 1, 1, 1; 0, 1, 2]

/-- Invalid control: distinct-mode orthogonality holds, but the repeated
eigenspace is not mass-orthonormal and the damping stays coupled. -/
example :
    (witnessPsi3ᵀ * witnessM3 * witnessPsi3) 0 1 = 0 ∧
      (witnessPsi3ᵀ * witnessM3 * witnessPsi3) 0 2 = 0 ∧
      (witnessPsi3ᵀ * witnessM3 * witnessPsi3) 1 2 = 1 ∧
      (witnessPsi3ᵀ
        * PhyslibExt.Mechanics.RayleighModal.rayleighDamping
          (1 / 2) (1 / 10) witnessM3 witnessK3 * witnessPsi3) 1 2
        = 4 / 5 := by
  simp [witnessM3, witnessK3, witnessPsi3,
    PhyslibExt.Mechanics.RayleighModal.rayleighDamping, Matrix.mul_apply,
    Fin.sum_univ_three]; norm_num

/-- Nonproportional-control mass matrix. -/
private def nonpropM : Matrix (Fin 2) (Fin 2) ℝ := !![2, -1; -1, 1]

/-- Nonproportional-control stiffness matrix. -/
private def nonpropK : Matrix (Fin 2) (Fin 2) ℝ := !![5, -4; -4, 4]

/-- Nonproportional-control modal matrix. -/
private def nonpropPhi : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, 1]

/-- Exclusion control: a valid modal basis does not diagonalize the
nonproportional damping `diagonal ![0, 1]`. -/
example :
    nonpropPhiᵀ * nonpropM * nonpropPhi = 1 ∧
      nonpropPhiᵀ * nonpropK * nonpropPhi
        = diagonal (![1, 4] : Fin 2 → ℝ) ∧
      (nonpropPhiᵀ * diagonal (![0, 1] : Fin 2 → ℝ) * nonpropPhi) 0 1
        = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [nonpropM, nonpropPhi, Matrix.mul_apply, Fin.sum_univ_two]
    norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [nonpropK, nonpropPhi, Matrix.mul_apply, Fin.sum_univ_two]
    norm_num
  · simp [nonpropPhi, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## B. Participation and effective-mass checks -/

/-- Public shape of effective-mass completeness. -/
example {n : Type*} [Fintype n] [DecidableEq n] {M Φ : Matrix n n ℝ}
    (hMΦ : Φᵀ * M * Φ = 1) (r : n → ℝ) :
    ∑ j, PhyslibExt.Mechanics.RayleighModal.participation M Φ r j ^ 2
      = r ⬝ᵥ (M *ᵥ r) :=
  PhyslibExt.Mechanics.RayleighModal.participation_sq_sum hMΦ r

/-- Public shape of the modal expansion of `r`. -/
example {n : Type*} [Fintype n] [DecidableEq n] {M Φ : Matrix n n ℝ}
    (hMΦ : Φᵀ * M * Φ = 1) (r : n → ℝ) :
    Φ *ᵥ PhyslibExt.Mechanics.RayleighModal.participation M Φ r = r :=
  PhyslibExt.Mechanics.RayleighModal.mulVec_participation hMΦ r

/-- Public shape of strict truncation loss. -/
example {n : Type*} [Fintype n] [DecidableEq n] {M Φ : Matrix n n ℝ}
    (hMΦ : Φᵀ * M * Φ = 1) (r : n → ℝ) (s : Finset n) {j : n}
    (hj : j ∉ s)
    (hΓ : PhyslibExt.Mechanics.RayleighModal.participation M Φ r j ≠ 0) :
    ∑ i ∈ s, PhyslibExt.Mechanics.RayleighModal.participation M Φ r i ^ 2
      < r ⬝ᵥ (M *ᵥ r) :=
  PhyslibExt.Mechanics.RayleighModal.sum_participation_sq_lt_of_not_mem
    hMΦ r s hj hΓ

/-- Two equal masses between two walls: mass matrix. -/
private def twoMassM : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, 2]

/-- Two equal masses between two walls: stiffness matrix. -/
private def twoMassK : Matrix (Fin 2) (Fin 2) ℝ := !![2, -1; -1, 2]

/-- Two equal masses: symmetric and antisymmetric modal matrix. -/
private noncomputable def twoMassPhi : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / 2, 1 / 2; 1 / 2, -1 / 2]

/-- The two-mass matrices are positive definite and the displayed modes
form a complete modal basis with unit modal masses. -/
private lemma twoMass_modalBasis :
    twoMassM.PosDef ∧ twoMassK.PosDef ∧
      twoMassPhiᵀ * twoMassM * twoMassPhi = 1 ∧
      twoMassPhiᵀ * twoMassK * twoMassPhi = diagonal ![1 / 2, 3 / 2] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [twoMassM]
    · intro x hx
      have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
        by_contra h
        push Not at h
        exact hx (by ext i; fin_cases i <;> simp [h.1, h.2])
      simp [twoMassM, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      rcases hne with h | h
      · have hpos := sq_pos_of_ne_zero h
        nlinarith [sq_nonneg (x 1)]
      · have hpos := sq_pos_of_ne_zero h
        nlinarith [sq_nonneg (x 0)]
  · refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [twoMassK]
    · intro x hx
      have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
        by_contra h
        push Not at h
        exact hx (by ext i; fin_cases i <;> simp [h.1, h.2])
      simp [twoMassK, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      rcases hne with h | h
      · have hpos := sq_pos_of_ne_zero h
        nlinarith [sq_nonneg (x 1), sq_nonneg (x 0 - x 1)]
      · have hpos := sq_pos_of_ne_zero h
        nlinarith [sq_nonneg (x 0), sq_nonneg (x 0 - x 1)]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [twoMassM, twoMassPhi, Matrix.mul_apply, Fin.sum_univ_two] <;>
      norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [twoMassK, twoMassPhi, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.diagonal] <;> norm_num

/-- Owner-basis bridge on the two-mass system: the canonical basis
satisfies effective-mass completeness for every influence vector. -/
example :
    ∃ Φ : Matrix (Fin 2) (Fin 2) ℝ, Φᵀ * twoMassM * Φ = 1 ∧
      ∀ r : Fin 2 → ℝ,
        ∑ j, PhyslibExt.Mechanics.RayleighModal.participation
            twoMassM Φ r j ^ 2
          = r ⬝ᵥ (twoMassM *ᵥ r) := by
  obtain ⟨hM, hK, -, -⟩ := twoMass_modalBasis
  obtain ⟨C, -, hMC, -, -, -⟩ :=
    PhyslibExt.Mechanics.ModalResponse.exists_modalBasis hM hK.posSemidef
  exact ⟨C, hMC, fun r =>
    PhyslibExt.Mechanics.RayleighModal.participation_sq_sum hMC r⟩

/-- Physical bridge on the two-mass system: some canonical basis has
nonnegative modal values and nonnegative Rayleigh modal damping. -/
example :
    ∃ (Φ : Matrix (Fin 2) (Fin 2) ℝ) (μ : Fin 2 → ℝ), IsUnit Φ ∧
      Φᵀ * twoMassM * Φ = 1 ∧ Φᵀ * twoMassK * Φ = diagonal μ ∧
      ∀ j, 0 ≤ μ j ∧ 0 ≤ 1 / 2 + 1 / 10 * μ j := by
  obtain ⟨hM, hK, -, -⟩ := twoMass_modalBasis
  obtain ⟨Φ, μ, hΦ, hMΦ, hKΦ, hμ, -⟩ :=
    PhyslibExt.Mechanics.RayleighModal.exists_rayleigh_modal_decoupling
      (α := 1 / 2) (β := 1 / 10) hM hK.posSemidef (by norm_num)
      (by norm_num)
  exact ⟨Φ, μ, hΦ, hMΦ, hKΦ, hμ⟩

/-- Ring of three unit masses joined pairwise by unit springs. -/
private def ringStiffness : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2, -1, -1; -1, 2, -1; -1, -1, 2]

/-- The ring stiffness is positive semidefinite. -/
private lemma ringStiffness_posSemidef : ringStiffness.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ringStiffness]
  · simp [ringStiffness, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2),
      sq_nonneg (x 0 - x 2)]

/-- Owner-basis bridge on the ring of three, whose modal values include
a rigid mode and a repeated pair. -/
example :
    ∃ (Φ : Matrix (Fin 3) (Fin 3) ℝ) (μ : Fin 3 → ℝ),
      Φᵀ * (1 : Matrix (Fin 3) (Fin 3) ℝ) * Φ = 1 ∧
        Φᵀ * ringStiffness * Φ = diagonal μ ∧ (∀ i, 0 ≤ μ i) ∧
        ∀ r : Fin 3 → ℝ,
          ∑ j, PhyslibExt.Mechanics.RayleighModal.participation
              (1 : Matrix (Fin 3) (Fin 3) ℝ) Φ r j ^ 2
            = r ⬝ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ r) := by
  obtain ⟨C, -, hMC, μ, hKC, hμ⟩ :=
    PhyslibExt.Mechanics.ModalResponse.exists_modalBasis
      (M := (1 : Matrix (Fin 3) (Fin 3) ℝ)) (K := ringStiffness)
      Matrix.PosDef.one ringStiffness_posSemidef
  exact ⟨C, μ, hMC, hKC, hμ, fun r =>
    PhyslibExt.Mechanics.RayleighModal.participation_sq_sum hMC r⟩

/-- Zero-participation mode: under uniform base motion the antisymmetric
mode does not participate, and one mode already recovers the total. -/
example :
    PhyslibExt.Mechanics.RayleighModal.participation twoMassM twoMassPhi
        ![1, 1] = ![2, 0] ∧
      ∑ j ∈ ({0} : Finset (Fin 2)),
          PhyslibExt.Mechanics.RayleighModal.participation twoMassM
            twoMassPhi ![1, 1] j ^ 2
        = ![1, 1] ⬝ᵥ (twoMassM *ᵥ ![1, 1]) := by
  refine ⟨?_, ?_⟩
  · ext i
    fin_cases i <;>
      simp [PhyslibExt.Mechanics.RayleighModal.participation, twoMassM,
        twoMassPhi, Matrix.mulVec, dotProduct, Matrix.mul_apply,
        Fin.sum_univ_two]
    norm_num
  · simp [PhyslibExt.Mechanics.RayleighModal.participation, twoMassM,
      twoMassPhi, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_two]
    norm_num

/-- Truncation: under a one-sided base vector both modes participate,
and dropping one strictly loses effective mass. -/
example :
    PhyslibExt.Mechanics.RayleighModal.participation twoMassM twoMassPhi
        ![1, 0] = ![1, 1] ∧
      ∑ j ∈ ({0} : Finset (Fin 2)),
          PhyslibExt.Mechanics.RayleighModal.participation twoMassM
            twoMassPhi ![1, 0] j ^ 2
        < ![1, 0] ⬝ᵥ (twoMassM *ᵥ ![1, 0]) := by
  refine ⟨?_, ?_⟩
  · ext i
    fin_cases i <;>
      simp [PhyslibExt.Mechanics.RayleighModal.participation, twoMassM,
        twoMassPhi, Matrix.mulVec, dotProduct, Matrix.mul_apply,
        Fin.sum_univ_two]
  · simp [PhyslibExt.Mechanics.RayleighModal.participation, twoMassM,
      twoMassPhi, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- Unit modal masses are needed: with the unnormalized identity basis
the participation squares do not sum to the total mass. -/
example :
    ∑ j, PhyslibExt.Mechanics.RayleighModal.participation twoMassM 1
        ![1, 1] j ^ 2
      ≠ ![1, 1] ⬝ᵥ (twoMassM *ᵥ ![1, 1]) := by
  simp [PhyslibExt.Mechanics.RayleighModal.participation, twoMassM,
    Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num
