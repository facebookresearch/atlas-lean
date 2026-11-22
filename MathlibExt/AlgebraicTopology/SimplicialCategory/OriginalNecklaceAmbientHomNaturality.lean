/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceAmbientVertices
import MathlibExt.CategoryTheory.Enriched.HomEndpointMaps

/-!
# The SAME entire original native Hom and coefficient square

Every whole native necklace map commutes with its actual ambient raw Hom
comparison and full original coefficient direct image. Both actual
source/target equations and all original Hom maps are retained.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceHom

open SSet.OriginalNecklace SimplicialEnrichment OriginalBead

/-- Every actual original native coefficient map retains the SAME full coherent Hom map and endpoints. -/
theorem coefficientMap_endpoint (T U : Data) (f : T ⟶ U) :
    OriginalFlaggedNecklace.coefficientFunctor.{u}.map f =
      (coherentSimplexMap f.operator).map (initial.{u} T.dimension) (terminal.{u} T.dimension) ≫
        EqualityTransport.hom
          (congrArg SimplicialThickening.mk (OriginalBead.OuterOperator.lifted_zero.{u} f.operator f.source))
          (congrArg SimplicialThickening.mk (OriginalBead.OuterOperator.lifted_last.{u} f.operator f.target)) :=
  OriginalBead.OuterOperator.map_coherent f.operator f.source f.target

/-- The SAME whole native raw Hom map and full coefficient map commute exactly. -/
theorem ambientHomMap_native {T U : Data} (f : T ⟶ U) :
    nativeHomMap.{u} f ≫ ambientHomMap U = ambientHomMap T ≫ OriginalFlaggedNecklace.coefficientFunctor.map f := by
  let hx := congrArg SimplicialThickening.mk (OriginalBead.OuterOperator.lifted_zero.{u} f.operator f.source)
  let hy := congrArg SimplicialThickening.mk (OriginalBead.OuterOperator.lifted_last.{u} f.operator f.target)
  have hL := EnrichedFunctor.homMap_comp (realizationMap f.map.{u}) (ambientFunctor U)
    (nativeMap_source f) (nativeMap_target f) (ambientFunctor_source U) (ambientFunctor_target U)
  have hR := EnrichedFunctor.homMap_comp (ambientFunctor T) (coherentSimplexMap f.operator)
    (ambientFunctor_source T) (ambientFunctor_target T) hx hy
  have hM := EnrichedFunctor.homMap_eq (ambientFunctor_native f)
    ((congrArg (ambientFunctor U).obj (nativeMap_source f)).trans (ambientFunctor_source U))
    ((congrArg (ambientFunctor U).obj (nativeMap_target f)).trans (ambientFunctor_target U))
    ((congrArg (coherentSimplexMap f.operator).obj (ambientFunctor_source T)).trans hx)
    ((congrArg (coherentSimplexMap f.operator).obj (ambientFunctor_target T)).trans hy)
  exact hL.trans (hM.trans (hR.symm.trans
    (congrArg (fun e => ambientHomMap T ≫ e) (coefficientMap_endpoint T U f).symm)))

/-- EVERY original ambient square retains its actual full source-to-target interval Hom map. -/
theorem ambientIntervalMap_square (T U : Data) (f : T.object.{u} ⟶ U.object.{u})
    (φ : ⦋T.dimension⦌ ⟶ ⦋U.dimension⦌)
    (hsq : f ≫ (complex.{u} U.joints).ι = (complex.{u} T.joints).ι ≫ SSet.stdSimplex.map φ) :
    pointedHomMap f (nativeVertex_square T U f φ hsq 0)
        (nativeVertex_square T U f φ hsq (Fin.last T.dimension)) ≫
      ambientIntervalMap U (φ.toOrderHom 0) (φ.toOrderHom (Fin.last T.dimension)) =
      ambientHomMap T ≫ (coherentSimplexMap φ).map (OriginalBead.initial.{u} T.dimension)
        (OriginalBead.terminal.{u} T.dimension) := by
  let a := φ.toOrderHom 0
  let b := φ.toOrderHom (Fin.last T.dimension)
  have hL := EnrichedFunctor.homMap_comp (realizationMap f) (ambientFunctor U)
    (nativeVertex_square T U f φ hsq 0) (nativeVertex_square T U f φ hsq (Fin.last T.dimension))
    (ambientFunctor_vertex U a) (ambientFunctor_vertex U b)
  have hR := EnrichedFunctor.homMap_comp (ambientFunctor T) (coherentSimplexMap φ)
    (ambientFunctor_source T) (ambientFunctor_target T) (rfl : (coherentSimplexMap φ).obj
      (initial.{u} T.dimension) = SimplicialThickening.mk (ULift.up.{u} a))
    (rfl : (coherentSimplexMap φ).obj (terminal.{u} T.dimension) = SimplicialThickening.mk (ULift.up.{u} b))
  have hM := EnrichedFunctor.homMap_eq (ambientFunctor_square T U f φ hsq)
    ((congrArg (ambientFunctor U).obj (nativeVertex_square T U f φ hsq 0)).trans
      (ambientFunctor_vertex U a))
    ((congrArg (ambientFunctor U).obj (nativeVertex_square T U f φ hsq (Fin.last T.dimension))).trans
      (ambientFunctor_vertex U b))
    (congrArg (coherentSimplexMap φ).obj (ambientFunctor_source T))
    (congrArg (coherentSimplexMap φ).obj (ambientFunctor_target T))
  have hI : EnrichedFunctor.homMap (coherentSimplexMap φ)
      (rfl : (coherentSimplexMap φ).obj (initial.{u} T.dimension) = SimplicialThickening.mk (ULift.up.{u} a))
      (rfl : (coherentSimplexMap φ).obj (terminal.{u} T.dimension) = SimplicialThickening.mk (ULift.up.{u} b)) =
        (coherentSimplexMap φ).map (initial.{u} T.dimension) (terminal.{u} T.dimension) :=
    Category.comp_id _
  exact hL.trans (hM.trans (hR.symm.trans (congrArg (fun e => ambientHomMap T ≫ e) hI)))

/-- Both SAME original ambient interval endpoints retain their supplied literal ordinal equations. -/
theorem ambientIntervalMap_square_retarget (T U : Data) (f : T.object.{u} ⟶ U.object.{u})
    (φ : ⦋T.dimension⦌ ⟶ ⦋U.dimension⦌)
    (hsq : f ≫ (complex.{u} U.joints).ι = (complex.{u} T.joints).ι ≫ SSet.stdSimplex.map φ)
    (a b : Fin (U.dimension + 1)) (ha : φ.toOrderHom 0 = a)
    (hb : φ.toOrderHom (Fin.last T.dimension) = b) :
    pointedHomMap f
        ((nativeVertex_square T U f φ hsq 0).trans (congrArg (nativeVertex U) ha))
        ((nativeVertex_square T U f φ hsq (Fin.last T.dimension)).trans (congrArg (nativeVertex U) hb)) ≫
      ambientIntervalMap U a b =
      ambientHomMap T ≫ (coherentSimplexMap φ).map (initial.{u} T.dimension) (terminal.{u} T.dimension) ≫
        EqualityTransport.hom
          (congrArg SimplicialThickening.mk (congrArg (ULift.up.{u}) ha))
          (congrArg SimplicialThickening.mk (congrArg (ULift.up.{u}) hb)) := by
  subst a
  subst b
  change _ = (ambientHomMap T ≫ (coherentSimplexMap φ).map
    (initial.{u} T.dimension) (terminal.{u} T.dimension)) ≫ 𝟙 _
  exact (ambientIntervalMap_square T U f φ hsq).trans (Category.comp_id _).symm

end CategoryTheory.CoherentRealization.OriginalNecklaceHom
