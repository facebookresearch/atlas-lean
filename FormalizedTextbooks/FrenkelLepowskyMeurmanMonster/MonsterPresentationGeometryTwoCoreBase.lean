/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The intrinsic O₂ of the actual distinguished centralizer is its embedded extraspecial group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryTwoCoreLocal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryPoints

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The already proved full-centralizer identification as an actual group isomorphism. -/
noncomputable def monsterGeometryLocalCentralizerEquiv : H ≃* generatedCentralizer :=
  MulEquiv.ofBijective generatedLocalIntoCentralizer ⟨
    fun h k he => localIntoGenerated_injective (congrArg Subtype.val he),
    fun g => by
      obtain ⟨h, he⟩ := generatedCentralizer_element_local g
      exact ⟨h, he.symm⟩⟩

/-- The actual base-point centralizer projects onto the actual Conway quotient. -/
noncomputable def monsterGeometryBaseProjection : generatedCentralizer →* Co1 :=
  projH.comp monsterGeometryLocalCentralizerEquiv.symm.toMonoidHom

/-- The actual centralizer projection is onto. -/
theorem monsterGeometryBaseProjection_surjective :
    Function.Surjective monsterGeometryBaseProjection :=
  projH_surjective.comp monsterGeometryLocalCentralizerEquiv.symm.surjective

/-- The actual base projection kernel is exactly the transported local kernel. -/
theorem monsterGeometryBaseProjection_kernel :
    monsterGeometryBaseProjection.ker =
      projH.ker.map monsterGeometryLocalCentralizerEquiv.toMonoidHom := by
  unfold monsterGeometryBaseProjection
  simp only [MulEquiv.toMonoidHom_eq_coe]
  rw [MonoidHom.ker_comp_mulEquiv projH monsterGeometryLocalCentralizerEquiv.symm]
  simp only [MulEquiv.symm_symm]

/-- Its actual kernel is a two-group, transported from the checked extraspecial kernel. -/
theorem monsterGeometryBaseProjection_kernel_isTwoGroup :
    IsPGroup 2 monsterGeometryBaseProjection.ker :=
  (congrArg (fun S : Subgroup generatedCentralizer => IsPGroup 2 S)
    monsterGeometryBaseProjection_kernel).mpr
      (monsterGeometryLocalKernel_isTwoGroup.map
        monsterGeometryLocalCentralizerEquiv.toMonoidHom)

/-- The intrinsic O₂(C_G(z)) equals its actual extraspecial subgroup. -/
theorem monsterGeometryBaseTwoCore_eq_Q :
    monsterGeometryTwoCore generatedCentralizer =
      inclQ.range.map monsterGeometryLocalCentralizerEquiv.toMonoidHom := by
  have ht := monsterGeometryTwoCore_eq_kernel monsterGeometryBaseProjection
    monsterGeometryBaseProjection_surjective monsterGeometryBaseProjection_kernel_isTwoGroup
    (fun P hnormal hP => by
      have : P.Normal := hnormal
      exact co1_normal_two_subgroup_eq_bot P hP)
  rw [ht, monsterGeometryBaseProjection_kernel, ← inclQ_range_eq_projH_ker]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
