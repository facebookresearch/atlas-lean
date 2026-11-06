/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Intrinsic normal two-cores of all actual point centralizers. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryTwoCoreBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryCentralizers

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every actual point centralizer has the actual Conway quotient, with a genuine conjugator. -/
noncomputable def monsterGeometryPointProjection (p : MonsterGeometryPoint) (g : G)
    (hg : g * generatedCentralInvolution * g⁻¹ = p.val) :
    monsterGeometryPointCentralizer p →* Co1 :=
  monsterGeometryBaseProjection.comp
    (monsterGeometryCentralizerConjugation p g hg).symm.toMonoidHom

/-- Conjugating a point transports its full actual projection kernel. -/
theorem monsterGeometryPointProjection_kernel (p : MonsterGeometryPoint) (g : G)
    (hg : g * generatedCentralInvolution * g⁻¹ = p.val) :
    (monsterGeometryPointProjection p g hg).ker = monsterGeometryBaseProjection.ker.map
      (monsterGeometryCentralizerConjugation p g hg).toMonoidHom := by
  unfold monsterGeometryPointProjection
  simp only [MulEquiv.toMonoidHom_eq_coe]
  rw [MonoidHom.ker_comp_mulEquiv monsterGeometryBaseProjection
    (monsterGeometryCentralizerConjugation p g hg).symm]
  simp only [MulEquiv.symm_symm]

/-- The intrinsic O₂ of each full point centralizer is the conjugate of the actual base O₂. -/
theorem monsterGeometryPointTwoCore_eq_conjugate (p : MonsterGeometryPoint) (g : G)
    (hg : g * generatedCentralInvolution * g⁻¹ = p.val) :
    monsterGeometryTwoCore (monsterGeometryPointCentralizer p) =
      (monsterGeometryTwoCore generatedCentralizer).map
        (monsterGeometryCentralizerConjugation p g hg).toMonoidHom := by
  let f := monsterGeometryPointProjection p g hg
  have hs : Function.Surjective f := monsterGeometryBaseProjection_surjective.comp
    (monsterGeometryCentralizerConjugation p g hg).symm.surjective
  have hk : IsPGroup 2 f.ker := by
    exact (congrArg (fun S : Subgroup (monsterGeometryPointCentralizer p) => IsPGroup 2 S)
      (monsterGeometryPointProjection_kernel p g hg)).mpr
        (monsterGeometryBaseProjection_kernel_isTwoGroup.map
          (monsterGeometryCentralizerConjugation p g hg).toMonoidHom)
  have ht := monsterGeometryTwoCore_eq_kernel f hs hk
    (fun P hnormal hP => by
      have : P.Normal := hnormal
      exact co1_normal_two_subgroup_eq_bot P hP)
  have hb := monsterGeometryTwoCore_eq_kernel monsterGeometryBaseProjection
    monsterGeometryBaseProjection_surjective monsterGeometryBaseProjection_kernel_isTwoGroup
    (fun P hnormal hP => by
      have : P.Normal := hnormal
      exact co1_normal_two_subgroup_eq_bot P hP)
  rw [ht, hb]
  exact monsterGeometryPointProjection_kernel p g hg

/-- The point's intrinsic O₂ has exactly its original extraspecial subgroup inside G. -/
theorem monsterGeometryPointTwoCore_image_eq_Q (p : MonsterGeometryPoint) (g : G)
    (hg : g * generatedCentralInvolution * g⁻¹ = p.val) :
    (monsterGeometryTwoCore (monsterGeometryPointCentralizer p)).map
      (monsterGeometryPointCentralizer p).subtype =
      qIntoGenerated.range.map (MulAut.conj g).toMonoidHom := by
  rw [monsterGeometryPointTwoCore_eq_conjugate p g hg, monsterGeometryBaseTwoCore_eq_Q,
    Subgroup.map_map, Subgroup.map_map]
  have he : ((monsterGeometryPointCentralizer p).subtype.comp
      (monsterGeometryCentralizerConjugation p g hg).toMonoidHom).comp
        monsterGeometryLocalCentralizerEquiv.toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp localIntoGenerated := by
    ext h
    rfl
  rw [he, ← Subgroup.map_map]
  rw [← MonoidHom.range_comp]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
