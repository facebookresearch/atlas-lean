/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SignedAnchorEnumeration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionPairOrbit

/-! Actual full-axis projection and the central-sign factor for the complete original matrix. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine Conway quotient image of the entire actual matrix stabilizer. -/
def generatedTenthCo1SpatialStabilizer : Subgroup Co1 :=
  generatedTenthE7OriginalMatrixGroup.map (QuotientGroup.mk' signsSubgroup)

/-- The original full local stabilizer of the actual tenth word image. -/
def generatedTenthLocalAxisStabilizer : Subgroup H := MulAction.stabilizer H generatedTenthAxis

/-- The genuine restricted Conway projection of the actual full-axis stabilizer. -/
def generatedTenthLocalAxisProjection : generatedTenthLocalAxisStabilizer →* Co1 :=
  projH.comp generatedTenthLocalAxisStabilizer.subtype

/-- Only projection values attained by genuine full-axis fixers are included. -/
def generatedTenthProjectedAxisStabilizer : Subgroup Co1 :=
  generatedTenthLocalAxisProjection.range

/-- Every original full-axis fixer preserves the entire actual matrix. -/
theorem generatedTenth_local_fiber_spatial_mem (f : localFiberSubgroup)
    (hf : rhoLocal (localFiberIntoH f) generatedTenthAxis = generatedTenthAxis) :
    f.val.2 ∈ generatedTenthE7OriginalMatrixGroup := by
  have hm := congrArg (fun x : GriessSpace => (griessConwayEncode x).1) hf
  rw [generatedFourth_local_matrix] at hm
  exact hm

/-- Each actual full-axis projection lies in the genuine matrix-stabilizer quotient. -/
theorem generatedTenthProjectedAxisStabilizer_le_spatial :
    generatedTenthProjectedAxisStabilizer ≤ generatedTenthCo1SpatialStabilizer := by
  rintro c ⟨h, rfl⟩
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hfix : rhoLocal (localFiberIntoH f) generatedTenthAxis = generatedTenthAxis := by
    rw [hf]
    exact h.property
  refine ⟨f.val.2, generatedTenth_local_fiber_spatial_mem f hfix, ?_⟩
  change QuotientGroup.mk' signsSubgroup f.val.2 = projH h.val
  rw [← hf]
  rfl

/-- Both genuine central lattice signs preserve every entry of the original actual matrix. -/
theorem generatedTenth_signs_le_spatial : signsSubgroup ≤ generatedTenthE7OriginalMatrixGroup := by
  intro g hg
  rcases hg with hg | hg
  · have he : g = 1 := Subtype.ext hg
    subst g
    exact generatedTenthE7OriginalMatrixGroup.one_mem
  · have hm : leechIsomMatrix g = -(1 : Matrix (Fin 24) (Fin 24) ℝ) := by
      ext i j
      change g.val (Pi.single j 1) i = _
      rw [hg]
      simp [Pi.single_apply, Matrix.neg_apply, Matrix.one_apply]
    change conwayMatrixAction g _ = _
    rw [conwayMatrixAction_eq_conjugate, hm, Matrix.transpose_neg,
      Matrix.transpose_one, Matrix.neg_mul, Matrix.one_mul,
      Matrix.mul_neg, Matrix.mul_one, neg_neg]

/-- Passing to the genuine central-sign quotient preserves the actual matrix-stabilizer index. -/
theorem generatedTenthCo1SpatialStabilizer_index :
    generatedTenthCo1SpatialStabilizer.index = generatedTenthE7OriginalMatrixGroup.index := by
  change (generatedTenthE7OriginalMatrixGroup.map (QuotientGroup.mk' signsSubgroup)).index = _
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective signsSubgroup)]
  rw [QuotientGroup.ker_mk']
  exact generatedTenth_signs_le_spatial

/-- The entire actual matrix stabilizer has exactly two lattice signs per Conway value. -/
theorem generatedTenth_spatial_card_twice_Co1 :
    Nat.card generatedTenthE7OriginalMatrixGroup =
      2 * Nat.card generatedTenthCo1SpatialStabilizer := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  have h0 := generatedTenthE7OriginalMatrixGroup.card_mul_index
  have h1 := generatedTenthCo1SpatialStabilizer.card_mul_index
  rw [generatedTenthCo1SpatialStabilizer_index, co1_card_exact] at h1
  rw [co0_card_exact] at h0
  apply Nat.eq_of_mul_eq_mul_right
    (Nat.pos_of_ne_zero generatedTenthE7OriginalMatrixGroup.index_ne_zero_of_finite)
  rw [Nat.mul_assoc, h1]
  exact h0.trans (by decide)

/-- Genuine full-axis Conway projection values are bounded by the actual spatial quotient. -/
theorem generatedTenth_projected_card_le_spatial :
    Nat.card generatedTenthProjectedAxisStabilizer ≤
      Nat.card generatedTenthCo1SpatialStabilizer := by
  let : Finite Co1 := co1_finite
  exact Subgroup.card_le_of_le generatedTenthProjectedAxisStabilizer_le_spatial

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
