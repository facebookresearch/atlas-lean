/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalFunctorComparison
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneFunctorHoUniversal

/-!
# The same original derived mapping end for native CSS functors

The canonical categorical comparison restricts to its specified weak core
map. The original one-fold carrier counits identify the actual CSS power
with the transported original functor object. The resulting localization
Iso uses precisely the original Q/R end and the checked new scalar-zero
comparison from the original functor-core universal theorem.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalClosed Opposite
open scoped MonoidalCategory SimplicialSpace.Cartesian SSet.modelCategoryQuillen
open SimplicialPresheaf.InjectiveKan SimplicialPresheaf.OriginalLocalDerived

namespace SimplicialSpace.FirstProjection

private abbrev E := SimplicialPresheaf.OrderedJFS.oneDesignatedEquivalence.{u}
private abbrev F := SimplicialPresheaf.OrderedJFS.originalFamily.{u} 1
private abbrev H := SimplicialPresheaf.CoreDerivedAdjunction.scalarHo.{u}

/-- The source and target are the actual one-fold inverse images, with no new replacements. -/
abbrev originalImage (W : SimplicialSpace.{u}) : SimplicialPresheaf.OrderedJFS.Original.{u} 1 :=
  E.{u}.inverse.obj W

/-- Genuine CSS completeness gives the actual original local-fibrant predicate on the inverse image. -/
theorem originalImage_local (V : SimplicialSpace.{u}) (hV : completeSegalSpaces V) :
    isOriginalLocalFibrant F.{u} (originalImage V) := by
  let _ : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  have h : IsFibrant V := (RezkModel.isFibrant_iff_completeSegalSpaces V).mpr hV
  have h' : IsFibrant (E.{u}.functor.obj (originalImage V)) :=
    isFibrant_of_iso (E.{u}.counitIso.app V).symm h
  exact (SimplicialPresheaf.OrderedJFS.one_locality_recognition (originalImage V)).2.2.mpr
    ((RezkModel.isFibrant_iff_completeSegalSpaces _).mp h')

/-- The full original power uses the actual carrier counits at both CSS endpoints. -/
def originalPowerIso (W V : SimplicialSpace.{u}) :
    E.{u}.functor.obj (SimplicialPresheaf.OrderedJFS.OneFunctor.object (originalImage W) (originalImage V)) ≅
      (ihom W).obj V :=
  SimplicialPresheaf.OrderedJFS.OneFunctor.imageIso (originalImage W) (originalImage V) ≪≫
    (MonoidalClosed.internalHom.mapIso (E.{u}.counitIso.app W).symm.op).app
      (E.{u}.functor.obj (originalImage V)) ≪≫ (ihom W).mapIso (E.{u}.counitIso.app V)

/-- Both constructions use the same first-JT native core of the same full power. -/
def originalNativeCoreIso (W V : SimplicialSpace.{u}) :
    (SimplicialPresheaf.OrderedJFS.OneFunctor.Core.nativeCoreFunctor (originalImage W)).obj
      (originalImage V) ≅ SSet.coreFunctor.obj (right.obj ((ihom W).obj V)) :=
  OnefoldCoreComparison.nativeCore.mapIso (originalPowerIso W V)

/-- The native Joyal functor core is the actual equivalence-edge core of the scalar functor object. -/
abbrev functorCore (W V : SimplicialSpace.{u}) : SSet.{u} :=
  SSet.coreFunctor.obj ((ihom (right.obj W)).obj (right.obj V))

/-- The actual CSS power core has precisely the original one-fold Q/R-derived-end interpretation. -/
def cssPowerCoreMappingIso (W V : SimplicialSpace.{u}) (hV : completeSegalSpaces V) :
    H.{u}.obj (SSet.coreFunctor.obj (right.obj ((ihom W).obj V))) ≅
      H.{u}.obj (((localDerivedEnd F.{u}).obj (op (originalImage W))).obj (originalImage V)) :=
  (H.{u}.mapIso (originalNativeCoreIso W V)).symm ≪≫
    SimplicialPresheaf.OrderedJFS.OneFunctor.Core.nativeMappingIso (originalImage W) (originalImage V)
      (originalImage_local V hV)

/-- The arbitrary-fibrant-source native functor core represents that same original derived mapping end. -/
def functorCoreMappingIso (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) :
    H.{u}.obj (functorCore W V) ≅
      H.{u}.obj (((localDerivedEnd F.{u}).obj (op (originalImage W))).obj (originalImage V)) := by
  let _ : IsIso (H.{u}.map (SSet.coreFunctor.map (comparison W V))) :=
    Localization.inverts H.{u} SSet.realizationWeakEquivalences _ (comparison_coreWeak W V hW hV)
  exact (asIso (H.{u}.map (SSet.coreFunctor.map (comparison W V)))).symm ≪≫ cssPowerCoreMappingIso W V hV

/-- The native closed comparison keeps its exact original-core derived-end triangle. -/
theorem functorCoreMappingIso_triangle (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) :
    H.{u}.map (SSet.coreFunctor.map (comparison W V)) ≫ (functorCoreMappingIso W V hW hV).hom =
      (cssPowerCoreMappingIso W V hV).hom := by
  let _ : IsIso (H.{u}.map (SSet.coreFunctor.map (comparison W V))) :=
    Localization.inverts H.{u} SSet.realizationWeakEquivalences _ (comparison_coreWeak W V hW hV)
  change H.{u}.map (SSet.coreFunctor.map (comparison W V)) ≫
    (inv (H.{u}.map (SSet.coreFunctor.map (comparison W V))) ≫ (cssPowerCoreMappingIso W V hV).hom) = _
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

/-- The original carrier identification preserves the already checked new-zero/Q/R core comparison. -/
theorem cssPowerCoreMappingIso_original (W V : SimplicialSpace.{u}) (hV : completeSegalSpaces V) :
    (H.{u}.mapIso (originalNativeCoreIso W V)).hom ≫ (cssPowerCoreMappingIso W V hV).hom =
      (SimplicialPresheaf.OrderedJFS.OneFunctor.Core.nativeMappingIso (originalImage W)
        (originalImage V) (originalImage_local V hV)).hom := by
  change (H.{u}.mapIso (originalNativeCoreIso W V)).hom ≫
    ((H.{u}.mapIso (originalNativeCoreIso W V)).inv ≫ _) = _
  rw [Iso.hom_inv_id_assoc]

end SimplicialSpace.FirstProjection
