/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactSpatialPhysicalGeneric

/-! Ungated source bindings. All matrices come from the actual spatial constructors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The integer matrix of a genuine Golay code sign. -/
def generatedTenthSpatialPhysicalSign (c : golayCode) : Matrix (Fin 24) (Fin 24) ℤ :=
  Matrix.diagonal (fun i => if c.val i = 0 then 1 else -1)

/-- Column convention: a forward physical coordinate image gives row f(j), column j. -/
def generatedTenthSpatialPhysicalPermutation (f : Fin 24 → Fin 24) :
    Matrix (Fin 24) (Fin 24) ℤ := fun i j => if i = f j then 1 else 0

/-- The actual standard permutation's complete frozen forward-coordinate table. -/
def generatedTenthSpatialPhysicalStandardForward : Fin 24 → Fin 24 :=
  ![5, 6, 12, 15, 16, 21, 17, 23, 11, 1, 8, 2,
    14, 7, 4, 13, 0, 3, 9, 10, 22, 19, 18, 20]

/-- The genuine standard permutation numerator, with its positive forward orientation. -/
def generatedTenthSpatialPhysicalStandardPermutation : Matrix (Fin 24) (Fin 24) ℤ :=
  generatedTenthSpatialPhysicalPermutation generatedTenthSpatialPhysicalStandardForward

/-- Transport is T inverse times P, so its integer numerator is N transpose times P. -/
def generatedTenthSpatialPhysicalTransportNumerator : Matrix (Fin 24) (Fin 24) ℤ :=
  generatedTenthE7Numerator.transpose * generatedTenthSpatialPhysicalStandardPermutation

/-- Standard-coordinate source denominators: only the Xi letter has denominator two. -/
def generatedTenthSpatialPhysicalSourceDenominator (g : Fin 11) : ℕ :=
  if g.val < 9 then 1 else if g.val = 9 then 2 else 1

/-- Complete genuine standard source numerator for all eleven retained constructors. -/
def generatedTenthSpatialPhysicalSourceNumerator (g : Fin 11) :
    Matrix (Fin 24) (Fin 24) ℤ :=
  if h : g.val < 7 then
    generatedTenthSpatialPhysicalSign (generatedTenthAxisLowerRecoveryCode
      (generatedTenthAxisLowerRecoverySignBasis ⟨g.val, h⟩))
  else if h' : g.val < 9 then
    generatedTenthSpatialPhysicalSign (generatedTenthAxisLowerRecoveryCode
      (generatedTenthAxisLowerRecoveryPermutationCodeLabel ⟨g.val - 7, by omega⟩)) *
    generatedTenthSpatialPhysicalPermutation
      (generatedTenthAxisLowerRecoveryPermutationForward ⟨g.val - 7, by omega⟩)
  else generatedTenthE7OrbitLetterNumerator ⟨g.val - 9, by omega⟩

/-- Every diagonal integer sign is the actual real Golay sign isometry. -/
theorem generatedTenth_spatial_physical_sign_actual (c : golayCode) :
    leechIsomMatrix (golaySignIsometry c) =
      (generatedTenthSpatialPhysicalSign c).map (Int.castRingHom ℝ) := by
  ext i j
  by_cases hc : c.val i = 0 <;> by_cases hij : i = j <;>
    simp [generatedTenthSpatialPhysicalSign, leechIsomMatrix, golaySignIsometry,
      golayRealSign_apply, qSign, hc, hij, eq_comm]

/-- Exact forward coordinates symbolically determine a genuine permutation's real matrix. -/
theorem generatedTenth_spatial_physical_permutation_actual
    (p : golayAutomorphismSubgroup) (f : Fin 24 → Fin 24)
    (hf : ∀ j, p.val j = f j) :
    leechIsomMatrix (golayPermutationIsometry p) =
      (generatedTenthSpatialPhysicalPermutation f).map (Int.castRingHom ℝ) := by
  ext i j
  have he : p.val.symm i = j ↔ i = f j := by
    rw [Equiv.symm_apply_eq, hf]
  simp only [leechIsomMatrix, golayPermutationIsometry, golayRealPermute_apply,
    Pi.single_apply, generatedTenthSpatialPhysicalPermutation, Matrix.map_apply]
  by_cases hij : i = f j
  · rw [ite_eq_left (he.mpr hij), ite_eq_left hij, map_one]
  · have hji : p.val.symm i ≠ j := fun h => hij (he.mp h)
    rw [ite_eq_right hji, ite_eq_right hij, map_zero]

/-- T has its frozen complete physical numerator divided by two. -/
theorem generatedTenth_spatial_physical_T_actual :
    leechIsomMatrix generatedTenthE7Isometry =
      (2 : ℝ)⁻¹ • generatedTenthE7Numerator.map (Int.castRingHom ℝ) := by
  ext i j
  change generatedTenthE7Isometry.val (Pi.single j 1) i = _
  rw [generatedTenth_e7_isometry_apply]
  simp [generatedTenthE7Matrix, generatedTwelfthCertifiedRealMatrix]

/-- P retains its actual frozen forward-coordinate word, not an inverse convention. -/
theorem generatedTenth_spatial_physical_P_actual :
    leechIsomMatrix (golayPermutationIsometry generatedTenthE8StandardPermutation) =
      generatedTenthSpatialPhysicalStandardPermutation.map (Int.castRingHom ℝ) := by
  apply generatedTenth_spatial_physical_permutation_actual
  intro j
  exact generatedTenth_e7_standard_transport_forward j

/-- The original transport's entire real matrix is exactly N transpose times P over two. -/
theorem generatedTenth_spatial_physical_transport_actual :
    leechIsomMatrix generatedTenthE7OrbitTransport =
      (2 : ℝ)⁻¹ • generatedTenthSpatialPhysicalTransportNumerator.map (Int.castRingHom ℝ) := by
  unfold generatedTenthE7OrbitTransport generatedTenthSpatialPhysicalTransportNumerator
  rw [generatedTenth_spatial_physical_matrix_mul,
    generatedTenth_spatial_physical_matrix_inv, generatedTenth_spatial_physical_T_actual,
    generatedTenth_spatial_physical_P_actual]
  simp only [Matrix.transpose_smul, Matrix.transpose_map, Matrix.smul_mul, Matrix.map_mul]

/-- The genuine Xi root letter has the frozen complete denominator-two numerator. -/
theorem generatedTenth_spatial_physical_xi_actual :
    leechIsomMatrix generatedTenthE7XiCorrection =
      (2 : ℝ)⁻¹ • generatedTenthE7XiCorrectedNumerator.map (Int.castRingHom ℝ) := by
  ext i j
  change generatedTenthE7XiCorrection.val (Pi.single j 1) i = _
  rw [generatedTenth_e7_xi_correction_apply]
  simp only [Matrix.mulVec_single_one, Pi.smul_apply, Matrix.smul_apply, one_div]
  rfl

/-- The genuine monomial root letter has its full frozen integer source matrix. -/
theorem generatedTenth_spatial_physical_mono_actual :
    leechIsomMatrix generatedTenthE7OrbitMonoSpatial =
      generatedTenthE7OrbitMonoMatrix.map (Int.castRingHom ℝ) := by
  ext i j
  change generatedTenthE7OrbitMonoSpatial.val (Pi.single j 1) i = _
  rw [generatedTenth_e7_orbit_mono_apply, Matrix.mulVec_single_one]
  rfl

/-- Every one of the eleven standard constructors has its complete genuine source numerator. -/
theorem generatedTenth_spatial_physical_source_actual (g : Fin 11) :
    leechIsomMatrix (generatedTenthAxisLowerRecoveryCompactStandardSpatial g) =
      (generatedTenthSpatialPhysicalSourceDenominator g : ℝ)⁻¹ •
        (generatedTenthSpatialPhysicalSourceNumerator g).map (Int.castRingHom ℝ) := by
  by_cases h7 : g.val < 7
  · have h9 : g.val < 9 := by omega
    simp only [generatedTenthAxisLowerRecoveryCompactStandardSpatial,
      generatedTenthSpatialPhysicalSourceNumerator,
      generatedTenthSpatialPhysicalSourceDenominator,
      h7, h9, ↓reduceDIte, ↓reduceIte, Nat.cast_one, inv_one, one_smul]
    exact generatedTenth_spatial_physical_sign_actual _
  · by_cases h9 : g.val < 9
    · simp only [generatedTenthAxisLowerRecoveryCompactStandardSpatial,
        generatedTenthSpatialPhysicalSourceNumerator,
      generatedTenthSpatialPhysicalSourceDenominator,
        h7, h9, ↓reduceDIte, ↓reduceIte, Nat.cast_one, inv_one, one_smul]
      unfold generatedTenthAxisLowerRecoverySignedPermutationSpatial golayMonomialPair
      rw [generatedTenth_spatial_physical_matrix_mul,
        generatedTenth_spatial_physical_sign_actual,
        generatedTenth_spatial_physical_permutation_actual _ _
          (generatedTenth_axis_lower_recovery_source_forward _), Matrix.map_mul]
    · have hg : g.val = 9 ∨ g.val = 10 := by omega
      rcases hg with hg | hg
      · have he : g = 9 := Fin.ext hg
        subst g
        simpa [generatedTenthAxisLowerRecoveryCompactStandardSpatial,
          generatedTenthSpatialPhysicalSourceNumerator,
      generatedTenthSpatialPhysicalSourceDenominator,
          generatedTenthE7OrbitSpatialLetter, generatedTenthE7OrbitLetterNumerator] using
          generatedTenth_spatial_physical_xi_actual
      · have he : g = 10 := Fin.ext hg
        subst g
        simpa [generatedTenthAxisLowerRecoveryCompactStandardSpatial,
          generatedTenthSpatialPhysicalSourceNumerator,
      generatedTenthSpatialPhysicalSourceDenominator,
          generatedTenthE7OrbitSpatialLetter, generatedTenthE7OrbitLetterNumerator] using
          generatedTenth_spatial_physical_mono_actual

/-- Every source denominator is positive; prospective finite kernel certificate. -/
theorem generatedTenth_spatial_physical_source_denominator :
    ∀ g : Fin 11, generatedTenthSpatialPhysicalSourceDenominator g ≠ 0 := by
  decide +kernel

/-- The exact finite integer transport obligation for a complete original source generator. -/
def GeneratedTenthCompactSpatialPhysicalIntegerCondition (g : Fin 11) : Prop :=
  generatedTenthAxisLowerRecoveryCompactSpatialDenominator g •
      (generatedTenthSpatialPhysicalTransportNumerator *
        generatedTenthSpatialPhysicalSourceNumerator g *
          generatedTenthSpatialPhysicalTransportNumerator.transpose) =
    (4 * generatedTenthSpatialPhysicalSourceDenominator g) •
      generatedTenthAxisLowerRecoveryCompactSpatialNumerator g

/-- A complete finite transport certificate gives the actual retained physical condition. -/
theorem generatedTenth_spatial_physical_of_integer (g : Fin 11)
    (h : GeneratedTenthCompactSpatialPhysicalIntegerCondition g) :
    generatedTenthAxisLowerRecoveryCompactPhysicalCondition g := by
  unfold generatedTenthAxisLowerRecoveryCompactPhysicalCondition
    generatedTenthAxisLowerRecoveryCompactSpatial generatedTenthE7OrbitConjugation
  apply generatedTenth_spatial_physical_conjugate _ _ _ _ _ 2
    (generatedTenthSpatialPhysicalSourceDenominator g)
    (generatedTenthAxisLowerRecoveryCompactSpatialDenominator g) (by decide)
    (generatedTenth_spatial_physical_source_denominator g)
    generatedTenth_spatial_physical_transport_actual
    (generatedTenth_spatial_physical_source_actual g)
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
