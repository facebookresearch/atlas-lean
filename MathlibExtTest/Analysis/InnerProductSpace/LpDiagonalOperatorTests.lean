/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.LpDiagonalOperatorSpectrum
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Normed.Algebra.Spectrum

import Mathlib.Tactic.NormNum

/-!
# Tests for diagonal operators on `ℓ²`

Concrete instances of the diagonal-operator API: the norm, adjoint,
self-adjointness, compactness and spectrum theorems of
`LpDiagonalOperator.lean` and `LpDiagonalOperatorSpectrum.lean`.
-/

open Topology Filter Set
open MathlibExt.Analysis.InnerProductSpace.LpDiagonalOperator
open MathlibExt.Analysis.InnerProductSpace.LpDiagonalOperatorSpectrum

namespace MathlibExtTest.Analysis.InnerProductSpace.LpDiagonalOperatorTests

/-- The constant diagonal operator with coefficient `2` has norm `2`. -/
example : ‖diagonalCLM (fun _ : ℕ => (2 : ℂ)) ⟨‖(2 : ℂ)‖, fun _ => le_refl _⟩‖ = 2 := by
  rw [norm_diagonalCLM, ciSup_const]
  simp

/-- The constant diagonal operator with coefficient `2` has spectrum `{2}`. -/
example : spectrum ℂ (diagonalCLM (fun _ : ℕ => (2 : ℂ))
    ⟨‖(2 : ℂ)‖, fun _ => le_refl _⟩) = {2} := by
  rw [spectrum_diagonalCLM]
  simp

/-- The constant diagonal operator with a real coefficient is self-adjoint. -/
example : IsSelfAdjoint (diagonalCLM (fun _ : ℕ => (2 : ℝ))
    ⟨‖(2 : ℝ)‖, fun _ => le_refl _⟩) := by
  rw [isSelfAdjoint_diagonalCLM_iff]
  simp

/-- The diagonal operator with coefficients `(n + 1)⁻¹` is compact, since the
coefficients vanish at infinity. -/
example : IsCompactOperator (diagonalCLM (fun n : ℕ => ((n + 1 : ℝ))⁻¹)
    ⟨1, fun n => by
      rw [norm_inv, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (show (1 : ℝ) ≤ (n : ℝ) + 1 by
        have _h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)⟩) := by
  rw [isCompactOperator_diagonalCLM_iff, Nat.cofinite_eq_atTop]
  simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)


@[expose] public section

open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace

namespace CanonicalRegression

/-- Distinct real and nonreal coefficients exercise the two coordinate actions. -/
def pairCoeff (i : Bool) : ℂ :=
  match i with
  | false => 2
  | true => Complex.I

theorem pairCoeff_le_two (i : Bool) : ‖pairCoeff i‖ ≤ 2 := by
  cases i <;> norm_num [pairCoeff]

theorem pairBound : ∃ C, ∀ i, ‖pairCoeff i‖ ≤ C :=
  ⟨2, pairCoeff_le_two⟩

noncomputable def pairVector : ℓ²(Bool, ℂ) :=
  lp.single 2 false (1 : ℂ) + lp.single 2 true (3 : ℂ)

theorem pair_coordinate_actions :
    diagonalCLM pairCoeff pairBound pairVector false = (2 : ℂ) ∧
    diagonalCLM pairCoeff pairBound pairVector true = Complex.I * (3 : ℂ) := by
  constructor <;> simp [diagonalCLM_apply, pairCoeff, pairVector, lp.single_apply]

theorem pair_adjoint_action :
    ((diagonalCLM pairCoeff pairBound)†) pairVector true = -Complex.I * (3 : ℂ) := by
  rw [adjoint_diagonalCLM, diagonalCLM_apply]
  simp [pairCoeff, pairVector, lp.single_apply]

theorem pair_not_selfAdjoint : ¬ IsSelfAdjoint (diagonalCLM pairCoeff pairBound) := by
  intro h
  have hc := (isSelfAdjoint_diagonalCLM_iff pairCoeff pairBound).mp h true
  have hi := congrArg Complex.im hc
  norm_num [pairCoeff] at hi

theorem pair_norm : ‖diagonalCLM pairCoeff pairBound‖ = 2 := by
  apply le_antisymm
  · exact norm_diagonalCLM_le pairCoeff pairBound (by norm_num) pairCoeff_le_two
  · have h := (diagonalCLM pairCoeff pairBound).le_opNorm (lp.single 2 false (1 : ℂ))
    rw [diagonalCLM_single, norm_smul] at h
    simp only [lp.norm_single (p := 2) (by norm_num), norm_one, mul_one] at h
    simpa [pairCoeff] using h

theorem pair_spectrum :
    spectrum ℂ (diagonalCLM pairCoeff pairBound) = ({2, Complex.I} : Set ℂ) := by
  have hrange : Set.range pairCoeff = ({2, Complex.I} : Set ℂ) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      cases i <;> simp [pairCoeff]
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with h | h
      · exact ⟨false, h.symm⟩
      · exact ⟨true, h.symm⟩
  rw [spectrum_diagonalCLM, hrange]
  simp

/-- The empty coefficient family admits a negative existential bound. -/
def emptyCoeff : Empty → ℂ := fun i => i.elim

theorem emptyBound : ∃ C : ℝ, ∀ i, ‖emptyCoeff i‖ ≤ C :=
  ⟨-7, fun i => i.elim⟩

theorem empty_operator_zero : diagonalCLM emptyCoeff emptyBound = 0 := by
  ext x i
  cases i

theorem empty_norm : ‖diagonalCLM emptyCoeff emptyBound‖ = 0 := by
  rw [empty_operator_zero, norm_zero]

theorem empty_spectrum : spectrum ℂ (diagonalCLM emptyCoeff emptyBound) = ∅ := by
  rw [spectrum_diagonalCLM]
  simp
  exact ⟨fun i => i.elim⟩

theorem empty_compact : IsCompactOperator (diagonalCLM emptyCoeff emptyBound) := by
  rw [empty_operator_zero]
  exact isCompactOperator_zero

/-- The canonical constructor also accepts the explicit negative empty-family bound. -/
theorem canonical_empty_negative_bound_zero :
    MathlibExt.Analysis.InnerProductSpace.HilbertBasisDiagonal.diagonalOperator
      (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (ℓ²(Empty, ℂ)))) emptyCoeff
      (C := -7) (fun i => i.elim) = 0 := by
  ext x i
  cases i

/-- Nonzero constant coefficients do not vanish at infinity. -/
theorem constant_two_not_compact :
    ¬ IsCompactOperator (diagonalCLM (fun _ : ℕ => (2 : ℝ))
      ⟨‖(2 : ℝ)‖, fun _ => le_refl _⟩) := by
  rw [isCompactOperator_diagonalCLM_iff, Nat.cofinite_eq_atTop, tendsto_const_nhds_iff]
  norm_num

end CanonicalRegression

end

end MathlibExtTest.Analysis.InnerProductSpace.LpDiagonalOperatorTests
