/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.RayleighModal
import PhyslibExt.ClassicalMechanics.RelativeOscillator
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Order.Compact
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
invalid-basis and nonproportional-damping controls, two-mass and
ring-of-three participation checks through the canonical modal basis,
and finite-horizon peak-bound checks: the base-excitation modal load as
an instance of decoupling, a reference oscillator from rest, equality,
cancellation and SRSS comparisons, and edge and premise controls.

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
- C. Finite-horizon peak-bound checks

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


/-! ## C. Finite-horizon peak-bound checks -/

open PhyslibExt.Mechanics.RayleighModal

/-- nonnegativity, all `T`, all `u` (totalized sSup). -/
example (T : ℝ) (u : ℝ → ℝ) : 0 ≤ spectralDisplacement T u :=
  Real.sSup_nonneg fun _ ⟨_, _, h⟩ => h ▸ abs_nonneg _

/-- empty horizon `T < 0`: junk value 0. -/
example (u : ℝ → ℝ) : spectralDisplacement (-1) u = 0 := by
  unfold spectralDisplacement
  rw [Set.Icc_eq_empty (by norm_num), Set.image_empty, Real.sSup_empty]

/-- `T = 0`: the value at 0. -/
example (u : ℝ → ℝ) : spectralDisplacement 0 u = |u 0| := by
  unfold spectralDisplacement
  rw [Set.Icc_self, Set.image_singleton, csSup_singleton]

/-- attainment H1. -/
example (T : ℝ) (hT : 0 ≤ T) (u : ℝ → ℝ) (hu : ContinuousOn u (Set.Icc 0 T)) :
    ∃ t₀ ∈ Set.Icc 0 T, |u t₀| = spectralDisplacement T u ∧
      ∀ t ∈ Set.Icc 0 T, |u t| ≤ spectralDisplacement T u := by
  obtain ⟨t₀, ht₀, h⟩ := isCompact_Icc.exists_sSup_image_eq (Set.nonempty_Icc.2 hT) hu.abs
  exact ⟨t₀, ht₀, h.symm, fun t ht =>
    le_csSup (isCompact_Icc.bddAbove_image hu.abs) ⟨t, ht, rfl⟩⟩

/-- Peak of `t ↦ t²` on `[0, 1]` is `1`. -/
private lemma peak_sd_sq : spectralDisplacement 1 (fun t => t ^ 2) = 1 := by
  unfold spectralDisplacement
  apply IsGreatest.csSup_eq
  refine ⟨⟨1, ⟨zero_le_one, le_rfl⟩, by norm_num⟩, ?_⟩
  rintro _ ⟨t, ⟨h0, h1⟩, rfl⟩
  simp only [abs_pow, sq_abs]
  nlinarith

/-- One-mode participation with `M = Φ = 1`, `r = 2` is `Γ = 2`. -/
private lemma peak_part1 :
    participation (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 (fun _ => 2) = fun _ => 2 := by
  funext j; simp [participation]

/-- Two-mode participation with `M = Φ = 1`, `r = 1` is `Γ = (1, 1)`. -/
private lemma peak_part2 :
    participation (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 (fun _ => 1) = fun _ => 1 := by
  funext j; simp [participation]

/-- W1: one mode, nonzero equality at the peak `t = T = 1`. -/
example :
    |∑ j : Fin 1, (fun _ => (3 : ℝ)) j * (fun _ (t : ℝ) => 2 * t ^ 2) j 1| = 6 ∧
    ∑ j : Fin 1, |(fun _ => (3 : ℝ)) j * participation 1 1 (fun _ => (2 : ℝ)) j| *
      spectralDisplacement 1 ((fun _ (t : ℝ) => t ^ 2) j) = 6 ∧
    |∑ j : Fin 1, (fun _ => (3 : ℝ)) j * (fun _ (t : ℝ) => 2 * t ^ 2) j 1| ≤
    ∑ j : Fin 1, |(fun _ => (3 : ℝ)) j * participation 1 1 (fun _ => (2 : ℝ)) j| *
      spectralDisplacement 1 ((fun _ (t : ℝ) => t ^ 2) j) := by
  refine ⟨by norm_num, by simp [peak_part1, peak_sd_sq]; norm_num, ?_⟩
  exact abs_modal_combination_le (M := 1) (Φ := 1) (r := fun _ => 2) (T := 1)
    (u := fun _ t => t ^ 2) (q := fun _ t => 2 * t ^ 2) (fun _ => 3)
    (fun _ => (continuous_pow 2).continuousOn)
    (fun j t _ => by simp [peak_part1]) ⟨zero_le_one, le_rfl⟩

/-- W2: opposite-sign modes cancel exactly; bound is 2. -/
example (t : ℝ) :
    ∑ j : Fin 2, ![(1 : ℝ), -1] j * (fun _ (s : ℝ) => s ^ 2) j t = 0 ∧
    ∑ j : Fin 2, |![(1 : ℝ), -1] j * participation 1 1 (fun _ => (1 : ℝ)) j| *
      spectralDisplacement 1 ((fun _ (s : ℝ) => s ^ 2) j) = 2 := by
  refine ⟨by simp [Fin.sum_univ_two], ?_⟩
  simp [Fin.sum_univ_two, peak_part2, peak_sd_sq]; norm_num

/-- W3: aligned peaks, ABSSUM = 2 = |r(1)| > SRSS = √2. -/
example :
    |∑ j : Fin 2, ![(1 : ℝ), 1] j * (fun _ (s : ℝ) => s ^ 2) j 1| = 2 ∧
    ∑ j : Fin 2, |![(1 : ℝ), 1] j * participation 1 1 (fun _ => (1 : ℝ)) j| *
      spectralDisplacement 1 ((fun _ (s : ℝ) => s ^ 2) j) = 2 ∧
    Real.sqrt (∑ j : Fin 2, (![(1 : ℝ), 1] j * participation 1 1 (fun _ => (1 : ℝ)) j *
      spectralDisplacement 1 ((fun _ (s : ℝ) => s ^ 2) j)) ^ 2) < 2 := by
  refine ⟨by norm_num [Fin.sum_univ_two],
    by simp [Fin.sum_univ_two, peak_part2, peak_sd_sq]; norm_num, ?_⟩
  simp only [Fin.sum_univ_two, peak_part2, peak_sd_sq]
  norm_num

/-- empty mode index: both sides 0. -/
example (c : Fin 0 → ℝ) (q u : Fin 0 → ℝ → ℝ) (M Φ : Matrix (Fin 0) (Fin 0) ℝ) (r : Fin 0 → ℝ)
    (T t : ℝ) :
    |∑ j, c j * q j t| = 0 ∧
      ∑ j, |c j * participation M Φ r j| * spectralDisplacement T (u j) = 0 := by
  simp

/-- C1: correspondence broken (`q ≡ 5`, `u ≡ 1`, `Γ = 1`): conclusion false. -/
example : ¬ (|∑ j : Fin 1, (fun _ => (2 : ℝ)) j * (fun _ (_ : ℝ) => (5 : ℝ)) j 0| ≤
    ∑ j : Fin 1, |(fun _ => (2 : ℝ)) j * participation 1 1 (fun _ => (1 : ℝ)) j| *
      spectralDisplacement 1 ((fun _ (_ : ℝ) => (1 : ℝ)) j)) := by
  have hsd : spectralDisplacement 1 (fun _ => (1 : ℝ)) = 1 := by
    unfold spectralDisplacement
    rw [(Set.nonempty_Icc.2 zero_le_one).image_const]; simp
  have hp : participation (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 (fun _ => 1) = fun _ => 1 := by
    funext j; simp [participation]
  simp [hp, hsd]

/-- C2: discontinuous `u t = t⁻¹` (`u 0 = 0`): unbounded, sSup junk 0, bound fails at 1/2.
The totalized spectral displacement of `t ↦ t⁻¹` on `[0, 1]` is `0`. -/
private lemma peak_sd_inv : spectralDisplacement 1 (fun t => t⁻¹) = 0 := by
  unfold spectralDisplacement
  apply Real.sSup_of_not_bddAbove
  rintro ⟨B, hB⟩
  set b := max B 1 + 1
  have hb : 1 < b := by have := le_max_right B 1; linarith
  have hmem : |b⁻¹⁻¹| ∈ (fun t => |t⁻¹|) '' Set.Icc (0 : ℝ) 1 :=
    ⟨b⁻¹, ⟨by positivity, inv_le_one_of_one_le₀ hb.le⟩, rfl⟩
  have := hB hmem
  rw [inv_inv, abs_of_pos (by linarith)] at this
  have := le_max_left B 1
  linarith

example : ¬ (|∑ j : Fin 1, (fun _ => (1 : ℝ)) j * (fun _ (t : ℝ) => t⁻¹) j (1 / 2)| ≤
    ∑ j : Fin 1, |(fun _ => (1 : ℝ)) j * participation 1 1 (fun _ => (1 : ℝ)) j| *
      spectralDisplacement 1 ((fun _ (t : ℝ) => t⁻¹) j)) := by
  simp [peak_sd_inv]

/-- C4: `ht` dropped: `t = 2 ∉ [0,1]`, `u t = t`: `2 ≤ 1` false. -/
example : ¬ (|∑ j : Fin 1, (fun _ => (1 : ℝ)) j * (fun _ (t : ℝ) => t) j 2| ≤
    ∑ j : Fin 1, |(fun _ => (1 : ℝ)) j * participation 1 1 (fun _ => (1 : ℝ)) j| *
      spectralDisplacement 1 ((fun _ (t : ℝ) => t) j)) := by
  have hsd : spectralDisplacement 1 (fun t => t) = 1 := by
    unfold spectralDisplacement
    apply IsGreatest.csSup_eq
    refine ⟨⟨1, ⟨zero_le_one, le_rfl⟩, by norm_num⟩, ?_⟩
    rintro _ ⟨t, ⟨h0, h1⟩, rfl⟩
    simp only; rw [abs_of_nonneg h0]; exact h1
  have hp : participation (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 (fun _ => 1) = fun _ => 1 := by
    funext j; simp [participation]
  simp [hp, hsd]

/-- Base-excitation modal load: the decoupling equivalence with load
`-ag t • (M *ᵥ r)`, whose modal right-hand side is `-(Γ j * ag t)`. -/
example {n : Type*} [Fintype n] [DecidableEq n] {M K Φ : Matrix n n ℝ} {μ : n → ℝ}
    (hMΦ : Φᵀ * M * Φ = 1) (hKΦ : Φᵀ * K * Φ = diagonal μ) (α β : ℝ)
    (r : n → ℝ) (ag : ℝ → ℝ) (x : ℝ → n → ℝ) (t : ℝ) :
    M *ᵥ deriv (deriv x) t + rayleighDamping α β M K *ᵥ deriv x t + K *ᵥ x t =
        -ag t • (M *ᵥ r) ↔
      ∀ j, deriv (deriv fun s => (Φᵀ * M) *ᵥ x s) t j +
          (α + β * μ j) * deriv (fun s => (Φᵀ * M) *ᵥ x s) t j +
          μ j * ((Φᵀ * M) *ᵥ x t) j = -(participation M Φ r j * ag t) := by
  have hrw : ∀ j, (Φᵀ *ᵥ (-ag t • (M *ᵥ r))) j =
      -(participation M Φ r j * ag t) := by
    intro j
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Pi.smul_apply, smul_eq_mul, neg_mul,
      mul_comm (ag t)]
    rfl
  exact (rayleigh_modal_decoupling hMΦ hKΦ α β x (fun s => -ag s • (M *ᵥ r)) t).trans
    (forall_congr' fun j => by rw [hrw j])

/-- Mass-weighting witness matrix: the scalar `4`. -/
private def peakM4 : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => 4

/-- Mass-weighting witness modal matrix: the scalar `1 / 2`. -/
private noncomputable def peakPhi : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => 1 / 2

/-- The witness basis is mass-orthonormal. -/
private lemma peak_hMPhi : peakPhiᵀ * peakM4 * peakPhi = 1 := by
  ext i j; fin_cases i; fin_cases j
  simp [peakM4, peakPhi, Matrix.mul_apply, -Matrix.transpose_of]; norm_num

/-- The witness basis diagonalizes the (equal) stiffness with modal value `1`. -/
private lemma peak_hKPhi : peakPhiᵀ * peakM4 * peakPhi = diagonal (fun _ => 1) := by
  ext i j; fin_cases i; fin_cases j
  simp [peakM4, peakPhi, Matrix.mul_apply, -Matrix.transpose_of]; norm_num

/-- Mass-weighted participation of the witness is `Γ = 2`. -/
private lemma peak_part4 : participation peakM4 peakPhi (fun _ => 1) = fun _ => 2 := by
  funext j; simp [participation, peakM4, peakPhi, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, -Matrix.transpose_of]; norm_num

/-- Mass weighting matters: with a nonzero base load the modal load is
`-(Γ * ag)` with `Γ = 2`; the unweighted transport `Φᵀ r` is `1 / 2`, and
the sign-flipped modal load is refuted. -/
example :
    peakM4 *ᵥ deriv (deriv fun _ : ℝ => (fun _ => (1 : ℝ) : Fin 1 → ℝ)) 0 +
        rayleighDamping 1 1 peakM4 peakM4 *ᵥ
          deriv (fun _ : ℝ => (fun _ => (1 : ℝ) : Fin 1 → ℝ)) 0 +
        peakM4 *ᵥ (fun _ => (1 : ℝ)) = -(-1 : ℝ) • (peakM4 *ᵥ fun _ => (1 : ℝ)) ∧
    (∀ j, deriv (deriv fun _s : ℝ => (peakPhiᵀ * peakM4) *ᵥ (fun _ => (1 : ℝ) : Fin 1 → ℝ)) 0 j +
          (1 + 1 * (fun _ => (1 : ℝ)) j) *
            deriv (fun _s : ℝ => (peakPhiᵀ * peakM4) *ᵥ (fun _ => (1 : ℝ) : Fin 1 → ℝ)) 0 j +
          (fun _ => (1 : ℝ)) j * ((peakPhiᵀ * peakM4) *ᵥ (fun _ => (1 : ℝ) : Fin 1 → ℝ)) j =
        -(participation peakM4 peakPhi (fun _ => 1) j * -1)) ∧
    (peakPhiᵀ *ᵥ (fun _ => (1 : ℝ))) 0 = 1 / 2 ∧
    ¬ (∀ j, deriv (deriv fun _s : ℝ => (peakPhiᵀ * peakM4) *ᵥ (fun _ => (1 : ℝ) : Fin 1 → ℝ)) 0 j +
          (1 + 1 * (fun _ => (1 : ℝ)) j) *
            deriv (fun _s : ℝ => (peakPhiᵀ * peakM4) *ᵥ (fun _ => (1 : ℝ) : Fin 1 → ℝ)) 0 j +
          (fun _ => (1 : ℝ)) j * ((peakPhiᵀ * peakM4) *ᵥ (fun _ => (1 : ℝ) : Fin 1 → ℝ)) j =
        participation peakM4 peakPhi (fun _ => 1) j * -1) := by
  have hphys : peakM4 *ᵥ deriv (deriv fun _ : ℝ => (fun _ => (1 : ℝ) : Fin 1 → ℝ)) 0 +
        rayleighDamping 1 1 peakM4 peakM4 *ᵥ
          deriv (fun _ : ℝ => (fun _ => (1 : ℝ) : Fin 1 → ℝ)) 0 +
        peakM4 *ᵥ (fun _ => (1 : ℝ)) = -(-1 : ℝ) • (peakM4 *ᵥ fun _ => (1 : ℝ)) := by
    simp [rayleighDamping, peakM4]
  have hdec := (rayleigh_modal_decoupling peak_hMPhi peak_hKPhi 1 1
    (fun _ => fun _ => (1 : ℝ)) (fun _ => -(-1 : ℝ) • (peakM4 *ᵥ fun _ => (1 : ℝ))) 0).1 hphys
  have hmodal : ∀ j, deriv (deriv fun _s : ℝ =>
        (peakPhiᵀ * peakM4) *ᵥ (fun _ => (1 : ℝ) : Fin 1 → ℝ)) 0 j +
          (1 + 1 * (fun _ => (1 : ℝ)) j) *
            deriv (fun _s : ℝ => (peakPhiᵀ * peakM4) *ᵥ (fun _ => (1 : ℝ) : Fin 1 → ℝ)) 0 j +
          (fun _ => (1 : ℝ)) j * ((peakPhiᵀ * peakM4) *ᵥ (fun _ => (1 : ℝ) : Fin 1 → ℝ)) j =
        -(participation peakM4 peakPhi (fun _ => 1) j * -1) := by
    intro j
    have h := hdec j
    rwa [show (peakPhiᵀ *ᵥ (-(-1 : ℝ) • (peakM4 *ᵥ fun _ => (1 : ℝ)))) j =
        -(participation peakM4 peakPhi (fun _ => 1) j * -1) by
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Pi.smul_apply, smul_eq_mul, neg_mul,
        mul_comm]; rfl] at h
  refine ⟨hphys, hmodal, by simp [peakPhi, Matrix.mulVec, dotProduct], ?_⟩
  intro h
  have h1 := h 0
  have h2 := hmodal 0
  rw [peak_part4] at h1 h2
  linarith

/-- Invalid-basis control: with `Φ = 0` the physical base-excitation
equation is false while every modal equation holds, so decoupling cannot
be dropped. -/
example : ¬ ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ deriv (deriv fun _ : ℝ => (0 : Fin 1 → ℝ)) 0 +
        rayleighDamping 0 0 1 1 *ᵥ deriv (fun _ : ℝ => (0 : Fin 1 → ℝ)) 0 +
        (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ 0 =
          -(1 : ℝ) • ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ fun _ => 1)) ∧
    (∀ j : Fin 1, deriv (deriv fun _s : ℝ =>
          ((0 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1) *ᵥ (0 : Fin 1 → ℝ)) 0 j +
          (0 + 0 * (1 : ℝ)) *
            deriv (fun _s : ℝ => ((0 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1) *ᵥ (0 : Fin 1 → ℝ)) 0 j +
          (1 : ℝ) * (((0 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1) *ᵥ (0 : Fin 1 → ℝ)) j =
        -(participation 1 0 (fun _ => 1) j * 1)) := by
  refine ⟨?_, ?_⟩
  · intro h; have := congrFun h 0; simp at this
  · intro j; simp [participation]

/-- Reference response from rest: `u t = t²` solves
`u'' + (1 + 1 * 1) u' + u = -ag` with `ag s = -(2 + 4s + s²)`, through
`RelativeOscillator.relative_equation_and_energy` at unit mass and zero
applied force; its continuity comes from that package's `HasDerivAt`
component, and the peak bound applies to it. -/
example :
    |∑ j : Fin 1, (fun _ => (1 : ℝ)) j * (fun _ (t : ℝ) => t ^ 2) j 1| ≤
      ∑ j : Fin 1, |(fun _ => (1 : ℝ)) j * participation 1 1 (fun _ => (1 : ℝ)) j| *
        spectralDisplacement 1 ((fun _ (t : ℝ) => t ^ 2) j) ∧
    ∀ s : ℝ, (2 : ℝ) + (1 + 1 * 1) * (2 * s) + s ^ 2 = - (-(2 + 4 * s + s ^ 2)) := by
  have hpkg : ∀ s : ℝ, HasDerivAt (fun t : ℝ => t ^ 2) (2 * s) s ∧
      (2 : ℝ) + (1 + 1 * 1) * (2 * s) + s ^ 2 = - (-(2 + 4 * s + s ^ 2)) := by
    intro s
    set A : ℝ := -(2 + 4 * s + s ^ 2) with hA
    have hy : HasDerivAt (fun τ : ℝ => A / 2 * (τ - s) ^ 2) (A * (s - s)) s := by
      simpa using (((hasDerivAt_id s).sub_const s).pow 2).const_mul (A / 2)
    have hu2 : HasDerivAt (fun τ : ℝ => τ ^ 2) (2 * s) s := by
      have hval : (2 : ℝ) * s = ((2 : ℕ) : ℝ) * s ^ (2 - 1) := by simp
      rw [hval]
      exact hasDerivAt_pow 2 s
    have hx : HasDerivAt (fun τ : ℝ => A / 2 * (τ - s) ^ 2 + τ ^ 2) (A * (s - s) + 2 * s) s :=
      hy.fun_add hu2
    have hyv : HasDerivAt (fun τ : ℝ => A * (τ - s)) A s := by
      simpa using ((hasDerivAt_id s).sub_const s).const_mul A
    have hxv : HasDerivAt (fun τ : ℝ => A * (τ - s) + 2 * τ) (A + 2) s := by
      have h := hyv.fun_add ((hasDerivAt_id' s).const_mul (2 : ℝ))
      have hval : A + 2 * (1 : ℝ) = A + 2 := by ring
      rwa [hval] at h
    obtain ⟨h1, -, h3, -⟩ := RelativeOscillator.relative_equation_and_energy
      (m := (1 : ℝ)) (c := 1 + 1 * 1) (k := (1 : ℝ))
      (x := fun τ : ℝ => A / 2 * (τ - s) ^ 2 + τ ^ 2)
      (y := fun τ : ℝ => A / 2 * (τ - s) ^ 2)
      (u := fun τ : ℝ => τ ^ 2)
      (xv := fun τ : ℝ => A * (τ - s) + 2 * τ)
      (yv := fun τ : ℝ => A * (τ - s))
      (xa := fun _ : ℝ => A + 2)
      (ya := fun _ : ℝ => A)
      (pf := fun _ : ℝ => 0)
      (fun τ => by ring) s hx hy hxv hyv
      (by show (1 : ℝ) * (A + 2) + (1 + 1 * 1) * ((A * (s - s) + 2 * s) - A * (s - s)) +
            (1 : ℝ) * ((A / 2 * (s - s) ^ 2 + s ^ 2) - A / 2 * (s - s) ^ 2) = 0
          rw [hA]; ring)
    have h1' : HasDerivAt (fun t : ℝ => t ^ 2) (2 * s) s := by simpa using h1
    have h3' : (2 : ℝ) + (1 + 1 * 1) * (2 * s) + s ^ 2 = - (-(2 + 4 * s + s ^ 2)) := by
      rw [hA] at h3
      linear_combination h3
    exact ⟨h1', h3'⟩
  have hp1 : participation (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 (fun _ => (1 : ℝ)) =
      fun _ => 1 := by
    funext j; simp [participation]
  have hcont : ∀ j : Fin 1, ContinuousOn ((fun _ (t : ℝ) => t ^ 2) j) (Set.Icc 0 1) :=
    fun _ => DifferentiableOn.continuousOn
      (fun s _ => (hpkg s).1.differentiableAt.differentiableWithinAt)
  exact ⟨abs_modal_combination_le (M := 1) (Φ := 1) (r := fun _ => 1) (T := 1)
    (u := fun _ t => t ^ 2) (q := fun _ t => t ^ 2) (fun _ => 1) hcont
    (fun j t _ => by simp [hp1]) ⟨zero_le_one, le_rfl⟩,
    fun s => (hpkg s).2⟩
