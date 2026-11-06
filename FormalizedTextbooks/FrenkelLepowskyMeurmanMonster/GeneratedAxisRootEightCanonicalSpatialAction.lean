/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalSpatialData

/-! Every full spatial frame column is bound to the genuine original positive canonical word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

private theorem monomial_step (k : Fin 3) (u : leechIntegral) (v w : Fin 24 → ℤ)
    (hu : u.val = v) (hw : generatedFifthRootEightCanonicalMonomialInteger k v = w) :
    (leechIntegralAction (generatedFifthRootEightCanonicalMonomial k) u).val = w := by
  rw [generatedFifthRootEight_canonical_monomial_coordinates, hu, hw]

private theorem xi_step (u : leechIntegral) (v w : Fin 24 → ℤ) (hu : u.val = v)
    (hw : co1XiNumerator *ᵥ v = (2 : ℕ) • w) :
    (leechIntegralAction co1XiIsometry u).val = w := by
  funext i
  have he := congrFun (co1Xi_integral_double u) i
  rw [hu, hw] at he
  simp only [Pi.smul_apply, nsmul_eq_mul] at he
  omega

/-- All six genuine action stages carry every original Leech coordinate frame column. -/
theorem generatedRootEight_canonical_spatial_frame (j : Fin 24) :
    (leechIntegralAction generatedFifthRootEightCanonicalTransport
      (leechCoordinateFrameLattice j)).val = generatedRootEightCanonicalSpatialStages 6 j := by
  let u := leechCoordinateFrameLattice j
  have h0 : u.val = generatedRootEightCanonicalSpatialStages 0 j := by
    change leechCoordinateFrameVector j = generatedRootEightCanonicalSpatialStages 0 j
    exact (generatedRootEight_canonical_spatial_initial j).symm
  obtain ⟨hm0, hm1, hm2⟩ := generatedRootEight_canonical_spatial_monomials j
  obtain ⟨hx0, hx1, hx2⟩ := generatedRootEight_canonical_spatial_xi j
  let u1 := leechIntegralAction (generatedFifthRootEightCanonicalMonomial 0) u
  have h1 : u1.val = generatedRootEightCanonicalSpatialStages 1 j :=
    monomial_step 0 u _ _ h0 hm0
  let u2 := leechIntegralAction co1XiIsometry u1
  have h2 : u2.val = generatedRootEightCanonicalSpatialStages 2 j := xi_step u1 _ _ h1 hx0
  let u3 := leechIntegralAction (generatedFifthRootEightCanonicalMonomial 1) u2
  have h3 : u3.val = generatedRootEightCanonicalSpatialStages 3 j :=
    monomial_step 1 u2 _ _ h2 hm1
  let u4 := leechIntegralAction co1XiIsometry u3
  have h4 : u4.val = generatedRootEightCanonicalSpatialStages 4 j := xi_step u3 _ _ h3 hx1
  let u5 := leechIntegralAction co1XiIsometry u4
  have h5 : u5.val = generatedRootEightCanonicalSpatialStages 5 j := xi_step u4 _ _ h4 hx2
  have h6 := monomial_step 2 u5 _ _ h5 hm2
  simpa only [generatedFifthRootEightCanonicalTransport, map_mul, LinearEquiv.mul_apply]
    using h6

set_option maxHeartbeats 8000000 in
-- Retain the complete original canonical word while comparing all real matrix coordinates.
/-- The entire genuine positive canonical matrix has the exact original rational numerator. -/
theorem generatedRootEight_canonical_spatial_matrix (i j : Fin 24) :
    leechIsomMatrix generatedFifthRootEightCanonicalTransport i j =
      (generatedRootEightCanonicalSpatialNumerator i j : ℝ) / 4 := by
  have h := congrArg leechCoordinateEmbedding (generatedRootEight_canonical_spatial_frame j)
  rw [leechIntegralAction_embedding] at h
  have hf : leechCoordinateEmbedding (leechCoordinateFrameLattice j).val =
      (8 / Real.sqrt 8 : ℝ) • Pi.single j 1 := by
    funext l
    by_cases hl : l = j <;>
      simp [leechCoordinateEmbedding, leechCoordinateFrameLattice, leechCoordinateFrameVector, hl]
  rw [hf, map_smul] at h
  have hi := congrFun h i
  change (8 / Real.sqrt 8 : ℝ) * leechIsomMatrix generatedFifthRootEightCanonicalTransport i j =
      (generatedRootEightCanonicalSpatialStages 6 j i : ℝ) / Real.sqrt 8 at hi
  rw [generatedRootEight_canonical_spatial_final, Int.cast_mul, Int.cast_ofNat] at hi
  have hs : Real.sqrt 8 ≠ 0 := by positivity
  field_simp [hs] at hi
  linarith

/-- Every original physical unit vector follows the genuine positive canonical matrix. -/
theorem generatedRootEight_canonical_spatial_unit (j i : Fin 24) :
    generatedFifthRootEightCanonicalTransport.val (Pi.single j 1) i =
      (generatedRootEightCanonicalSpatialNumerator i j : ℝ) / 4 := by
  exact generatedRootEight_canonical_spatial_matrix i j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
