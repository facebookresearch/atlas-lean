/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Data
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKAllSourceLocality

/-!
# Native I and K classes for stable model recognition

The full native level-I right class consists of K-right Omega-test
equivalences. Every native K-left map is a projective cofibration and
an Omega-test equivalence when the actual index Hom objects are cofibrant.
These follow from the original level model and the proved all-source
K-local Hom argument; no stable model or localization record is an input.

The reverse right-class inclusion uses the chosen-fiber recognition
argument separately. These lemmas retain the full original I and K
families and apply to arrows with arbitrary original endpoints.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.MorphismProperty HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- Every original level-I right arrow has full K lifting and all original Omega-target tests. -/
theorem levelI_right_le_KRight_omegaTests :
    (levelI (I := I)).rlp ≤ (generators s).rlp ⊓ omegaTests s := by
  intro X Y p hp
  have hLevel : trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) p :=
    Native.Data.generatorsI_rlp.le p hp
  exact ⟨levelTrivialFibrations_le_right s p hLevel,
    levelWeak_le_omegaTests s p hLevel.2⟩

/-- The entire original K-left class lies in the original projective cofibrations
and the all-source Omega-target test class. -/
theorem left_le_levelCofibrations_and_omegaTests
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) :
    (generators s).rlp.llp ≤
      cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) ⊓ omegaTests s :=
  le_inf (left_le_cofibrations s) (originalKLeft_le_localTests s hHom)

/-- Both original K generator summands satisfy the same complete stable source classes. -/
theorem generators_le_levelCofibrations_and_omegaTests
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) :
    generators s ≤
      cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) ⊓ omegaTests s :=
  (generators s).le_llp_rlp.trans (left_le_levelCofibrations_and_omegaTests s hHom)

/-- An original K-right arrow into an Omega object has Omega source,
using the whole original mapping-corner pullback and its first projection. -/
theorem right_source_isOmega
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (p : X ⟶ Y)
    (hp : (generators s).rlp p) (hY : IsOmega s Y) : IsOmega s X := by
  intro l
  let c := PointedCGWH.NativeMappingCorner.square (cylinderSource s l) p
  have hFst : trivialFibrations PointedCGWH.{u, v} c.fst :=
    MorphismProperty.of_isPullback c.isPullback.flip
      (cylinderSource_mapping_trivialFibration s l Y hY)
  have hComp := (trivialFibrations PointedCGWH.{u, v}).comp_mem c.π c.fst
    (((lifting_iff s p).mp hp).2 l) hFst
  rw [PointedCGWH.NativeMappingCorner.square_first] at hComp
  exact (stabilization_mapping_weak_iff s l X).mp
    ((cylinderSource_weak_iff s l X).mp hComp.2)

/-- Between original native Omega objects the full K-right class is precisely
 the actual native level-fibration class. No stable model is assumed. -/
theorem right_iff_levelFibration_of_isOmega
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (p : X ⟶ Y)
    (hX : IsOmega s X) (hY : IsOmega s Y) :
    (generators s).rlp p ↔ fibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) p := by
  constructor
  · intro h
    exact ((lifting_iff s p).mp h).1
  · intro h
    apply (lifting_iff s p).mpr
    refine ⟨h, fun l => ?_⟩
    let c := PointedCGWH.NativeMappingCorner.square (cylinderSource s l) p
    have hFst : trivialFibrations PointedCGWH.{u, v} c.fst :=
      MorphismProperty.of_isPullback c.isPullback.flip
        (cylinderSource_mapping_trivialFibration s l Y hY)
    have hFib : fibrations PointedCGWH.{u, v} c.π :=
      Native.CurrentMappingSM7.fibration (cylinderSource s l) p
        ((HomotopicalAlgebra.cofibration_iff _).mp (cylinderSource_cofibration s l)) h c
    have hComp : weakEquivalences PointedCGWH.{u, v} (c.π ≫ c.fst) := by
      rw [PointedCGWH.NativeMappingCorner.square_first]
      exact (cylinderSource_mapping_trivialFibration s l X hX).2
    exact ⟨hFib, (weakEquivalences PointedCGWH.{u, v}).of_postcomp _ _ hFst.2 hComp⟩

/-- Over an original Omega target, an original K-right map satisfies the
Omega Hom tests exactly when it is a native level trivial fibration. -/
theorem right_omegaTests_iff_levelTrivialFibration_of_target_isOmega
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (p : X ⟶ Y)
    (hp : (generators s).rlp p) (hY : IsOmega s Y) :
    omegaTests s p ↔ trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) p := by
  have hX := right_source_isOmega s p hp hY
  rw [omegaTests_iff_levelWeak_of_isOmega s p hX hY]
  have hFib := ((lifting_iff s p).mp hp).1
  change weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) p ↔
    fibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) p ∧
      weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) p
  exact ⟨fun h => ⟨hFib, h⟩, fun h => h.2⟩

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
