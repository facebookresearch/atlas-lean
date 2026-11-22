/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneFunctorCoreCompatibility

/-!
# The one-fold universal comparison for every scalar mapping space

Every scalar source is retained in a bifunctor. The original groupoidal-source
derived mapping space, the computed original core, the native first-JT core,
and the original Q/R end have natural weak comparisons using their actual
units, counits and common-core injections. Independently fixed scalar factors
are retained. Localization inverts these proved legs, rather than selecting
a strict reverse map or replacing the original factors.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite NatIso
open scoped SSet.modelCategoryQuillen
open SimplicialPresheaf.InjectiveKan SimplicialPresheaf.OriginalLocalDerived

namespace SimplicialPresheaf.OrderedJFS.OneFunctor.Core

private local instance sourceLocallySmall : LocallySmall.{u} (FinitePowerSite.Source 1) :=
  @CategoryTheory.locallySmall_of_univLE _ _ UnivLE.zero

private def precomposeObject (A : Original.{u} 1) :
    (Original.{u} 1 ⥤ SSet.{u}) ⥤ (Original.{u} 1 ⥤ SSet.{u}) :=
  (Functor.whiskeringLeft (Original.{u} 1) (Original.{u} 1) SSet.{u}).obj (objectFunctor A)

/-- The original derived mapping spaces from all baseline groupoidal sources into the entire functor object. -/
def originalMappingSpaces (A : Original.{u} 1) : SSet.{u}ᵒᵖ ⥤ LocalTargets.{u} ⥤ SSet.{u} :=
  SimplicialPresheaf.CoreUniversalMapping.groupoidalMapping family.{u} ⋙ precomposeObject A ⋙
    SimplicialPresheaf.CoreUniversalMapping.restrictTargets family.{u}

/-- All scalar mappings into the literal original zero core, with the chosen scalar Q/R. -/
def rawScalarSpaces (A : Original.{u} 1) (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    SSet.{u}ᵒᵖ ⥤ LocalTargets.{u} ⥤ SSet.{u} :=
  ScalarCoreReplacementSpans.mapping e.Q (rawCoreFunctor A ⋙ e.R) ⋙
    SimplicialPresheaf.CoreUniversalMapping.restrictTargets family.{u}

/-- All scalar mappings into the actual original replaced core. -/
def computedScalarSpaces (A : Original.{u} 1) (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    SSet.{u}ᵒᵖ ⥤ LocalTargets.{u} ⥤ SSet.{u} :=
  ScalarCoreReplacementSpans.mapping e.Q (coreFunctor A ⋙ e.R) ⋙
    SimplicialPresheaf.CoreUniversalMapping.restrictTargets family.{u}

/-- All scalar mappings into the actual first-JT native core. -/
def nativeScalarSpaces (A : Original.{u} 1) (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    SSet.{u}ᵒᵖ ⥤ LocalTargets.{u} ⥤ SSet.{u} :=
  ScalarCoreReplacementSpans.mapping e.Q (nativeCoreFunctor A ⋙ e.R) ⋙
    SimplicialPresheaf.CoreUniversalMapping.restrictTargets family.{u}

/-- All scalar mappings into the original Q/R-derived end. -/
def derivedScalarSpaces (A : Original.{u} 1) (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    SSet.{u}ᵒᵖ ⥤ LocalTargets.{u} ⥤ SSet.{u} :=
  ScalarCoreReplacementSpans.mapping e.Q ((localDerivedEnd family.{u}).obj (op A) ⋙ e.R) ⋙
    SimplicialPresheaf.CoreUniversalMapping.restrictTargets family.{u}

/-- The original baseline/scalar common mapping space keeps its actual pullback and pushout factors. -/
def originalCommonSpaces (A : Original.{u} 1)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    SSet.{u}ᵒᵖ ⥤ LocalTargets.{u} ⥤ SSet.{u} :=
  ScalarCoreReplacementSpans.commonMapping family.{u} (ConstantEvaluation.zeroTuple 1) e ⋙
    precomposeObject A ⋙ SimplicialPresheaf.CoreUniversalMapping.restrictTargets family.{u}

/-- The actual original groupoidal-source leg is natural in every scalar and original target. -/
def originalMappingLeg (A : Original.{u} 1)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    originalMappingSpaces A ⟶ originalCommonSpaces A e :=
  Functor.whiskerRight
    (SimplicialPresheaf.CoreUniversalMapping.toCommon family.{u} (ConstantEvaluation.zeroTuple 1) e)
    (precomposeObject A ⋙ SimplicialPresheaf.CoreUniversalMapping.restrictTargets family.{u})

/-- The fixed scalar leg into the same original common space retains all scalar factor maps. -/
def rawOriginalMappingLeg (A : Original.{u} 1)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    rawScalarSpaces A e ⟶ originalCommonSpaces A e :=
  Functor.whiskerRight
    (ScalarCoreReplacementSpans.fixedToCommon family.{u} (ConstantEvaluation.zeroTuple 1) e)
    (precomposeObject A ⋙ SimplicialPresheaf.CoreUniversalMapping.restrictTargets family.{u})

/-- The computed-core scalar leg is the original R-unit under the same scalar factors. -/
def computedMappingLeg (A : Original.{u} 1)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    rawScalarSpaces A e ⟶ computedScalarSpaces A e :=
  Functor.whiskerRight (ScalarCoreReplacementSpans.postLeg e.Q
    (Functor.whiskerRight (coreUnit A) e.R))
      (SimplicialPresheaf.CoreUniversalMapping.restrictTargets family.{u})

/-- The derived scalar leg retains the original raw-end Iso, target R-unit and source Q-counit. -/
def derivedMappingLeg (A : Original.{u} 1)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    rawScalarSpaces A e ⟶ derivedScalarSpaces A e :=
  Functor.whiskerRight (ScalarCoreReplacementSpans.postLeg e.Q
    (Functor.whiskerRight (derivedComparison A) e.R))
      (SimplicialPresheaf.CoreUniversalMapping.restrictTargets family.{u})

/-- The native common mapping spaces use the same completed first-JT/Gamma pushout core. -/
def nativeCommonSpaces (A : Original.{u} 1)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    SSet.{u}ᵒᵖ ⥤ LocalTargets.{u} ⥤ SSet.{u} :=
  ScalarCoreReplacementSpans.mapping e.Q (nativeCommonFunctor A ⋙ e.R) ⋙
    SimplicialPresheaf.CoreUniversalMapping.restrictTargets family.{u}

/-- The original zero-core leg is mapped through the same scalar Q/R to the native common space. -/
def rawNativeMappingLeg (A : Original.{u} 1)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    rawScalarSpaces A e ⟶ nativeCommonSpaces A e :=
  Functor.whiskerRight (ScalarCoreReplacementSpans.postLeg e.Q
    (Functor.whiskerRight (rawNativeLeg A) e.R))
      (SimplicialPresheaf.CoreUniversalMapping.restrictTargets family.{u})

/-- The native core leg uses its original Gamma comparison and common-core injection. -/
def nativeMappingLeg (A : Original.{u} 1)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    nativeScalarSpaces A e ⟶ nativeCommonSpaces A e :=
  Functor.whiskerRight (ScalarCoreReplacementSpans.postLeg e.Q
    (Functor.whiskerRight (nativeCoreLeg A) e.R))
      (SimplicialPresheaf.CoreUniversalMapping.restrictTargets family.{u})

private theorem scalarMap_weak (e : ScalarCoreReplacementSpans.ScalarConventions.{u})
    (K : SSet.{u}) {X Y : SSet.{u}} (f : X ⟶ Y) (hf : SSet.realizationWeakEquivalences f) :
    SSet.realizationWeakEquivalences ((ihom (e.Q.obj K)).map (e.R.map f)) := by
  have hr : SSet.realizationWeakEquivalences (e.R.map f) := by
    have hx : SSet.realizationWeakEquivalences (e.r.app X) := (e.r_trivialCofibration X).2
    have hy : SSet.realizationWeakEquivalences (e.r.app Y) := (e.r_trivialCofibration Y).2
    apply SSet.realizationWeakEquivalences.of_precomp _ _ hx
    have hn : f ≫ e.r.app Y = e.r.app X ≫ e.R.map f := by
      simpa only [Functor.id_map] using e.r.naturality f
    rw [← hn]
    exact SSet.realizationWeakEquivalences.comp_mem _ _ hf hy
  let _ : IsFibrant (e.R.obj X) := e.R_isFibrant X
  let _ : IsFibrant (e.R.obj Y) := e.R_isFibrant Y
  let _ : WeakEquivalence (e.R.map f) := (weakEquivalence_iff _).mpr hr
  let _ : (ihom.adjunction (e.Q.obj K)).IsQuillenAdjunction :=
    ihomAdjunction_isQuillenAdjunction_of_isCofibrant _
  exact (weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
      (adj := ihom.adjunction (e.Q.obj K)) (e.R.map f))

/-- Every original groupoidal-source component is weak, with no comparison premise. -/
theorem originalMappingLeg_weak (A : Original.{u} 1)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (K : SSet.{u}) (Z : LocalTargets.{u}) :
    SSet.realizationWeakEquivalences (((originalMappingLeg A e).app (op K)).app Z) :=
  SimplicialPresheaf.CoreUniversalMapping.toCommon_weak family.{u}
    (ConstantEvaluation.zeroIsTerminal 1) e K (object A Z.obj)

/-- Every fixed scalar component into the original common space is weak from actual target locality. -/
theorem rawOriginalMappingLeg_weak (A : Original.{u} 1)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (K : SSet.{u}) (Z : LocalTargets.{u}) :
    SSet.realizationWeakEquivalences (((rawOriginalMappingLeg A e).app (op K)).app Z) :=
  ScalarCoreReplacementSpans.fixedToCommon_weak family.{u}
    (ConstantEvaluation.zeroIsTerminal 1) e K (object A Z.obj) (object_localFibrant A Z.obj Z.property)

/-- The original R-unit remains weak in every fixed scalar mapping space. -/
theorem computedMappingLeg_weak (A : Original.{u} 1)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (K : SSet.{u}) (Z : LocalTargets.{u}) :
    SSet.realizationWeakEquivalences (((computedMappingLeg A e).app (op K)).app Z) :=
  scalarMap_weak e K ((coreUnit A).app Z.obj) (coreUnit_weak A Z.obj Z.property)

/-- The actual original Q/R end comparison is weak for every scalar source. -/
theorem derivedMappingLeg_weak (A : Original.{u} 1)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (K : SSet.{u}) (Z : LocalTargets.{u}) :
    SSet.realizationWeakEquivalences (((derivedMappingLeg A e).app (op K)).app Z) :=
  scalarMap_weak e K ((derivedComparison A).app Z.obj) (derivedComparison_weak A Z.obj Z.property)

/-- The original zero/native common-core leg remains weak under every scalar mapping convention. -/
theorem rawNativeMappingLeg_weak (A : Original.{u} 1)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (K : SSet.{u}) (Z : LocalTargets.{u}) :
    SSet.realizationWeakEquivalences (((rawNativeMappingLeg A e).app (op K)).app Z) :=
  scalarMap_weak e K (rawToNativeCommon A Z.obj) (rawToNativeCommon_weak A Z.obj Z.property)

/-- The actual native core/common injection remains weak in every scalar mapping space. -/
theorem nativeMappingLeg_weak (A : Original.{u} 1)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (K : SSet.{u}) (Z : LocalTargets.{u}) :
    SSet.realizationWeakEquivalences (((nativeMappingLeg A e).app (op K)).app Z) :=
  scalarMap_weak e K (nativeToCommon A Z.obj) (nativeToCommon_weak A Z.obj Z.property)

private abbrev localize := SimplicialPresheaf.CoreUniversalMapping.localizeValues family.{u}

private def localized {F G : SSet.{u}ᵒᵖ ⥤ LocalTargets.{u} ⥤ SSet.{u}} (t : F ⟶ G) :
    F ⋙ localize.{u} ⟶ G ⋙ localize.{u} := Functor.whiskerRight t localize

private theorem localized_isIso {F G : SSet.{u}ᵒᵖ ⥤ LocalTargets.{u} ⥤ SSet.{u}} (t : F ⟶ G)
    (ht : ∀ (K : SSet.{u}) (Z : LocalTargets.{u}),
      SSet.realizationWeakEquivalences ((t.app (op K)).app Z)) : IsIso (localized t) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro K
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro Z
  exact Localization.inverts scalarHo SSet.realizationWeakEquivalences _ (ht K.unop Z)

/-- The entire universal mapping-space comparison is natural in every scalar and genuine original target. -/
def derivedUniversalNatIso (A : Original.{u} 1)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    originalMappingSpaces A ⋙ localize.{u} ≅ derivedScalarSpaces A e ⋙ localize.{u} := by
  let _ := localized_isIso _ (originalMappingLeg_weak A e)
  let _ := localized_isIso _ (rawOriginalMappingLeg_weak A e)
  let _ := localized_isIso _ (derivedMappingLeg_weak A e)
  exact asIso (localized (originalMappingLeg A e)) ≪≫
    (asIso (localized (rawOriginalMappingLeg A e))).symm ≪≫
      asIso (localized (derivedMappingLeg A e))

/-- Computed original cores and original derived ends use the same raw-core scalar span. -/
def computedDerivedNatIso (A : Original.{u} 1)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    computedScalarSpaces A e ⋙ localize.{u} ≅ derivedScalarSpaces A e ⋙ localize.{u} := by
  let _ := localized_isIso _ (computedMappingLeg_weak A e)
  let _ := localized_isIso _ (derivedMappingLeg_weak A e)
  exact (asIso (localized (computedMappingLeg A e))).symm ≪≫
    asIso (localized (derivedMappingLeg A e))

/-- The native functor core classifies the original derived end for every scalar source. -/
def nativeDerivedNatIso (A : Original.{u} 1)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    nativeScalarSpaces A e ⋙ localize.{u} ≅ derivedScalarSpaces A e ⋙ localize.{u} := by
  let _ := localized_isIso _ (nativeMappingLeg_weak A e)
  let _ := localized_isIso _ (rawNativeMappingLeg_weak A e)
  let _ := localized_isIso _ (derivedMappingLeg_weak A e)
  exact asIso (localized (nativeMappingLeg A e)) ≪≫
    (asIso (localized (rawNativeMappingLeg A e))).symm ≪≫
      asIso (localized (derivedMappingLeg A e))

/-- The entire computed-core triangle keeps the actual original R-unit and Q/R end map. -/
theorem computedDerivedNatIso_triangle (A : Original.{u} 1)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    localized (computedMappingLeg A e) ≫ (computedDerivedNatIso A e).hom =
      localized (derivedMappingLeg A e) := by
  let _ := localized_isIso _ (computedMappingLeg_weak A e)
  change localized (computedMappingLeg A e) ≫
    (inv (localized (computedMappingLeg A e)) ≫ localized (derivedMappingLeg A e)) = _
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

/-- Two fixed scalar presentations retain the same entire original universal mapping-space function. -/
def changeScalarConventionsNatIso (A : Original.{u} 1)
    (e e' : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    derivedScalarSpaces A e ⋙ localize.{u} ≅ derivedScalarSpaces A e' ⋙ localize.{u} :=
  (derivedUniversalNatIso A e).symm ≪≫ derivedUniversalNatIso A e'

/-- Scalar convention changes commute with the same original derived universal map. -/
theorem changeScalarConventionsNatIso_triangle (A : Original.{u} 1)
    (e e' : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    (derivedUniversalNatIso A e).hom ≫ (changeScalarConventionsNatIso A e e').hom =
      (derivedUniversalNatIso A e').hom := by
  change (derivedUniversalNatIso A e).hom ≫
    ((derivedUniversalNatIso A e).inv ≫ (derivedUniversalNatIso A e').hom) = _
  rw [Iso.hom_inv_id_assoc]

end SimplicialPresheaf.OrderedJFS.OneFunctor.Core
