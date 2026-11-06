/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthMonomialFlag
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderExact

/-! Exact actual Co0 and Co1 matrix stabilizers of the eighth prototype. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual lattice isometries fixing the whole actual eighth matrix. -/
def generatedEighthSpatialStabilizer : Subgroup leechIsomSubgroup where
  carrier := {g | conwayMatrixAction g (griessConwayEncode generatedEighthAxis).1 =
    (griessConwayEncode generatedEighthAxis).1}
  one_mem' := by
    change conwayMatrixAction 1 _ = _
    rw [map_one]
    rfl
  mul_mem' := by
    intro g h hg hh
    change conwayMatrixAction (g * h) _ = _
    rw [map_mul]
    change conwayMatrixAction g (conwayMatrixAction h _) = _
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    change conwayMatrixAction g⁻¹ _ = _
    rw [map_inv]
    change (conwayMatrixAction g).symm _ = _
    exact (conwayMatrixAction g).symm_apply_eq.mpr hg.symm

/-- All actual matrix stabilizer elements are genuine signed Golay permutations. -/
theorem generatedEighthSpatialStabilizer_le_monomial :
    generatedEighthSpatialStabilizer ≤ golayMonomialSubgroup := by
  intro g hg
  exact generatedEighth_matrix_fixed_monomial g hg

/-- Original codeword signs and original flag permutations enumerate actual matrix fixers. -/
def generatedEighthSpatialEnumeration
    (a : golayCode × generatedEighthPermutationFlagStabilizer) :
    generatedEighthSpatialStabilizer :=
  ⟨golayMonomialPair (a.1, a.2.val),
    (generatedEighth_monomial_matrix_fix_iff a.1 a.2.val).mpr a.2.property⟩

/-- This enumeration covers every actual matrix fixer exactly once. -/
theorem generatedEighthSpatialEnumeration_bijective :
    Function.Bijective generatedEighthSpatialEnumeration := by
  constructor
  · rintro ⟨c, p⟩ ⟨d, q⟩ h
    have he := golayMonomialPair_injective (congrArg Subtype.val h)
    apply Prod.ext
    · exact congrArg (fun a : golayCode × golayAutomorphismSubgroup => a.1) he
    · exact Subtype.ext (congrArg (fun a : golayCode × golayAutomorphismSubgroup => a.2) he)
  · rintro ⟨g, hg⟩
    obtain ⟨c, p, hp⟩ := generatedEighthSpatialStabilizer_le_monomial hg
    have hfix : conwayMatrixAction (golayMonomialPair (c, p))
        (griessConwayEncode generatedEighthAxis).1 =
          (griessConwayEncode generatedEighthAxis).1 := by
      change conwayMatrixAction (golaySignIsometry c * golayPermutationIsometry p) _ = _
      rw [← hp]
      exact hg
    have hperm := (generatedEighth_monomial_matrix_fix_iff c p).mp hfix
    exact ⟨(c, ⟨p, hperm⟩), Subtype.ext hp.symm⟩

/-- The whole actual matrix stabilizer has order32440320 in Co0. -/
theorem generatedEighthSpatialStabilizer_card :
    Nat.card generatedEighthSpatialStabilizer = 32440320 := by
  rw [← Nat.card_congr (Equiv.ofBijective generatedEighthSpatialEnumeration
    generatedEighthSpatialEnumeration_bijective), Nat.card_prod,
    golayCode_card, generatedEighthPermutationFlagStabilizer_card]

/-- Both central lattice signs fix the actual eighth matrix. -/
theorem generatedEighth_signs_le_spatial : signsSubgroup ≤ generatedEighthSpatialStabilizer := by
  intro g hg
  rcases hg with hg | hg
  · have he : g = 1 := Subtype.ext hg
    subst g
    exact generatedEighthSpatialStabilizer.one_mem
  · have hm : leechIsomMatrix g = -(1 : Matrix (Fin 24) (Fin 24) ℝ) := by
      ext i j
      change g.val (Pi.single j 1) i = _
      rw [hg]
      simp [Pi.single_apply, Matrix.neg_apply, Matrix.one_apply]
    change conwayMatrixAction g _ = _
    rw [conwayMatrixAction_eq_conjugate, hm, Matrix.transpose_neg,
      Matrix.transpose_one, Matrix.neg_mul, Matrix.one_mul,
      Matrix.mul_neg, Matrix.mul_one, neg_neg]

/-- The whole actual eighth matrix stabilizer in the genuine central-sign quotient. -/
def generatedEighthCo1SpatialStabilizer : Subgroup Co1 :=
  generatedEighthSpatialStabilizer.map (QuotientGroup.mk' signsSubgroup)

/-- The original matrix stabilizer has index256333896000 in Co0. -/
theorem generatedEighthSpatialStabilizer_index :
    generatedEighthSpatialStabilizer.index = 256333896000 := by
  have h := generatedEighthSpatialStabilizer.card_mul_index
  rw [generatedEighthSpatialStabilizer_card, co0_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 32440320)
    (h.trans (by decide : 8315553613086720000 = 32440320 * 256333896000))

/-- The genuine central-sign quotient preserves the matrix stabilizer index. -/
theorem generatedEighthCo1SpatialStabilizer_index :
    generatedEighthCo1SpatialStabilizer.index = 256333896000 := by
  change (generatedEighthSpatialStabilizer.map (QuotientGroup.mk' signsSubgroup)).index = _
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective signsSubgroup)]
  · exact generatedEighthSpatialStabilizer_index
  · rw [QuotientGroup.ker_mk']
    exact generatedEighth_signs_le_spatial

/-- The whole actual eighth matrix stabilizer has order16220160 in Co1. -/
theorem generatedEighthCo1SpatialStabilizer_card :
    Nat.card generatedEighthCo1SpatialStabilizer = 16220160 := by
  have h := generatedEighthCo1SpatialStabilizer.card_mul_index
  rw [generatedEighthCo1SpatialStabilizer_index, co1_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 256333896000)
    (h.trans (by decide : 4157776806543360000 = 16220160 * 256333896000))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
