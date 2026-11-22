/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceAmbientFunctorNaturality

/-!
# ALL original native ambient vertices and full interval Hom maps

The same complete native inclusion retains EVERY original vertex, not
only its endpoints. Its ambient enriched functor is monic on every
original Hom. Exact vertex equations give the full native interval Hom
maps, and every actual ambient square retains all original vertex maps.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceHom

open SSet.OriginalNecklace SimplicialEnrichment

/-- EVERY SAME original vertex of the complete native necklace. -/
def nativeVertex (T : Data) (i : Fin (T.dimension + 1)) : T.object.{u} _⦋0⦌ :=
  SSet.yonedaEquiv (vertexMap T.joints i)

/-- The same original complete native inclusion retains every original ordinal vertex. -/
theorem inclusion_vertex (T : Data) (i : Fin (T.dimension + 1)) :
    (complex.{u} T.joints).ι.app (op ⦋0⦌) (nativeVertex T i) =
      SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋T.dimension⦌ i) := by
  rw [nativeVertex, ← SSet.yonedaEquiv_comp]
  exact (congrArg SSet.yonedaEquiv (vertexMap_ι.{u} T.joints i)).trans (SSet.yonedaEquiv_map _)

/-- EVERY SAME original ambient vertex is its original individual coherent object. -/
theorem ambientFunctor_vertex (T : Data) (i : Fin (T.dimension + 1)) :
    (ambientFunctor.{u} T).obj (nativeVertex T i) = SimplicialThickening.mk (ULift.up.{u} i) := by
  change (simplexIso.{u} ⦋T.dimension⦌).hom.obj
    ((complex.{u} T.joints).ι.app (op ⦋0⦌) (nativeVertex T i)) = _
  rw [inclusion_vertex]
  exact simplexIso_hom_obj ⦋T.dimension⦌ i

/-- The SAME actual ambient enriched functor is monic on EVERY complete original Hom. -/
theorem ambientFunctor_all_hom_mono (T : Data) (x y : T.object.{u} _⦋0⦌) :
    Mono ((ambientFunctor.{u} T).map x y) := by
  have hL := realizationMap_full_hom_mono (complex.{u} T.joints).ι x y
  let _ : IsIso ((simplexIso.{u} ⦋T.dimension⦌).hom.map
      ((complex.{u} T.joints).ι.app (op ⦋0⦌) x) ((complex.{u} T.joints).ι.app (op ⦋0⦌) y)) :=
    (SimplicialEnrichment.isoHomIso (simplexIso.{u} ⦋T.dimension⦌) _ _).isIso_hom
  exact mono_comp' hL (inferInstance : Mono ((simplexIso.{u} ⦋T.dimension⦌).hom.map
    ((complex.{u} T.joints).ι.app (op ⦋0⦌) x) ((complex.{u} T.joints).ι.app (op ⦋0⦌) y)))

/-- The SAME full original interval Hom map retains both supplied original native vertices. -/
def ambientIntervalMap (T : Data) (a b : Fin (T.dimension + 1)) :
    hom T.object.{u} (nativeVertex T a) (nativeVertex T b) ⟶
      (SimplicialThickening.mk (ULift.up.{u} a) ⟶[SSet.{u}]
        SimplicialThickening.mk (ULift.up.{u} b)) :=
  (ambientFunctor T).map (nativeVertex T a) (nativeVertex T b) ≫
    EqualityTransport.hom (ambientFunctor_vertex T a) (ambientFunctor_vertex T b)

/-- The SAME entire original interval Hom map is genuinely monic at EVERY supplied native vertex pair. -/
theorem ambientIntervalMap_mono (T : Data) (a b : Fin (T.dimension + 1)) :
    Mono (ambientIntervalMap.{u} T a b) := by
  have hE : Mono (EqualityTransport.hom (ambientFunctor_vertex.{u} T a) (ambientFunctor_vertex.{u} T b)) := by
    unfold EqualityTransport.hom
    infer_instance
  exact mono_comp' (ambientFunctor_all_hom_mono T _ _) hE

/-- EVERY SAME whole native ambient square retains its actual complete original vertex maps. -/
theorem nativeVertex_square (T U : Data) (f : T.object.{u} ⟶ U.object.{u})
    (φ : ⦋T.dimension⦌ ⟶ ⦋U.dimension⦌)
    (hsq : f ≫ (complex.{u} U.joints).ι = (complex.{u} T.joints).ι ≫ SSet.stdSimplex.map φ)
    (i : Fin (T.dimension + 1)) :
    f.app (op ⦋0⦌) (nativeVertex T i) = nativeVertex U (φ.toOrderHom i) := by
  have hv : vertexMap.{u} T.joints i ≫ f = vertexMap U.joints (φ.toOrderHom i) := by
    apply (cancel_mono (complex.{u} U.joints).ι).1
    rw [Category.assoc, hsq, ← Category.assoc, vertexMap_ι, vertexMap_ι, ← SSet.stdSimplex.map_comp]
    rfl
  exact (SSet.yonedaEquiv_comp (vertexMap.{u} T.joints i) f).symm.trans (congrArg SSet.yonedaEquiv hv)

/-- The SAME original source-to-target ambient interval retains exactly its earlier whole coefficient map. -/
theorem ambientIntervalMap_source_target (T : Data) :
    ambientIntervalMap.{u} T 0 (Fin.last T.dimension) = ambientHomMap T := rfl

end CategoryTheory.CoherentRealization.OriginalNecklaceHom
