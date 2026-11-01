/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhSignParameterBinding

/-! The actual original Golay signs form a 1024-element subgroup
of the seventh matrix stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The ten-parameter code inclusion uses the original faithful Golay encoder. -/
def generatedSeventhSpatialSignCode : generatedSeventhSignParameterSpace →+ golayCode where
  toFun v := ⟨golayEncoder v.val, ⟨v.val, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero golayEncoder)
  map_add' v w := Subtype.ext (map_add golayEncoder v.val w.val)

/-- The actual sign isometry homomorphism from the genuine ten-parameter code space. -/
def generatedSeventhSpatialSignHom : Multiplicative generatedSeventhSignParameterSpace →*
    leechIsomSubgroup := golaySignHom.comp generatedSeventhSpatialSignCode.toMultiplicative

/-- Distinct original sign parameters give distinct actual spatial isometries. -/
theorem generatedSeventhSpatialSignHom_injective :
    Function.Injective generatedSeventhSpatialSignHom := by
  intro v w h
  have hc := golaySignHom_injective h
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  apply golayEncoder_injective
  exact congrArg (fun c : Multiplicative golayCode => c.toAdd.val) hc

/-- Every included actual sign isometry fixes the entire original seventh matrix. -/
theorem generatedSeventhSpatialSignHom_mem (v : Multiplicative generatedSeventhSignParameterSpace) :
    generatedSeventhSpatialSignHom v ∈ generatedSeventhSpatialStabilizer := by
  let a := sourceCodeLabelEquiv.symm v.toAdd.val
  have ha : golayLabelCoefficients a = v.toAdd.val := sourceCodeLabelEquiv.apply_symm_apply _
  have hc : generatedSeventhSpatialSignCode v.toAdd = sourceGeneratedSignCode a := by
    apply Subtype.ext
    change golayEncoder v.toAdd.val = golayEncoder (golayLabelCoefficients a)
    rw [ha]
  change golaySignIsometry (generatedSeventhSpatialSignCode v.toAdd) ∈ _
  rw [hc, generatedSeventh_sign_spatial_mem_iff, ha]
  exact (generatedSeventhSignParameter_mem_iff _).mp v.toAdd.property

/-- The genuine actual ten-parameter Golay sign subgroup. -/
def generatedSeventhSpatialSignSubgroup : Subgroup leechIsomSubgroup :=
  generatedSeventhSpatialSignHom.range

/-- This entire actual sign subgroup lies in the original seventh matrix stabilizer. -/
theorem generatedSeventhSpatialSignSubgroup_le :
    generatedSeventhSpatialSignSubgroup ≤ generatedSeventhSpatialStabilizer := by
  rintro g ⟨v, rfl⟩
  exact generatedSeventhSpatialSignHom_mem v

/-- The actual original sign subgroup has exactly 1024 spatial isometries. -/
theorem generatedSeventhSpatialSignSubgroup_card :
    Nat.card generatedSeventhSpatialSignSubgroup = 1024 := by
  rw [generatedSeventhSpatialSignSubgroup,
    ← Nat.card_congr (MonoidHom.ofInjective generatedSeventhSpatialSignHom_injective).toEquiv]
  exact generatedSeventhSignParameterSpace_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
