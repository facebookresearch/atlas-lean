/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeBoundarySourceCobaseWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.FilteredColimitStageData
import Mathlib.CategoryTheory.MorphismProperty.RetractArgument

/-!
# Genuine fixed-object cofibrations are monic on every complete original Hom

The SAME native boundary cells are monic at each successor. Full Hom
evaluation retains their actual sequential colimit, so the original
boundary-factorization inclusion is monic. A genuine lifting retract
then proves monicity of every original fixed-object cofibration.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra

namespace CategoryTheory.SimplicialEnrichment.FixedObjects

variable {O : Type u} {C D : FixedObjects O}

/-- The SAME actual native boundary-factorization inclusion is monic on every full original Hom. -/
theorem FreeFactorization.boundary_homMap_mono (p : C ⟶ D) (x y : O) :
    Mono (homMap (FreeFactorization.boundary p).i x y) := by
  let t := (FreeFactorization.sequentialBoundaryCells p).toTransfiniteCompositionOfShape
  let U := FreeFactorization.sequentialBoundaryUnder p
  let V := SequentialSourcePushout.source U
  let c := (Under.forget C).mapCocone t.sourceUnderCocone
  have hc : IsColimit c := isColimitOfPreserves (Under.forget C) t.sourceUnderIsColimit
  have hm : Mono (homMap (t.incl.app 0) x y) :=
    SSet.FilteredColimitStage.cocone_legs_mono_of_maps_mono
      ((evaluation x y).mapCocone c) (isColimitOfPreserves (evaluation x y) hc)
        (fun {_ _} g => SequentialSourcePushout.source_homMap_mono U
          (FreeFactorization.sequentialBoundaryUnderCells p) x y g) 0
  have hb : Mono (homMap t.isoBot.inv x y) :=
    inferInstanceAs (Mono ((evaluation x y).map t.isoBot.inv))
  have he : homMap t.isoBot.inv x y ≫ homMap (t.incl.app 0) x y =
      homMap (FreeFactorization.boundary p).i x y :=
    (homMap_comp _ _ x y).symm.trans (congrArg (fun f => homMap f x y) t.fac)
  exact he ▸ mono_comp' hb hm

/-- Every genuine original fixed-object cofibration is monic on each full original labelled Hom. -/
theorem cofibration_homMap_mono (f : C ⟶ D) (hf : FixedObjectModel.cofibrations O f)
    (x y : O) : Mono (homMap f x y) := by
  let p := FreeFactorization.boundary f
  let _ : HasLiftingProperty f p.p := hf p.p p.hp
  let r := RetractArrow.ofLeftLiftingProperty p.fac
  exact MorphismProperty.of_retract (P := MorphismProperty.monomorphisms SSet.{u})
    (r.map (evaluation x y)) (FreeFactorization.boundary_homMap_mono f x y)

/-- The SAME full original enriched Hom maps of a genuine fixed-object cofibration are monic. -/
theorem cofibration_original_hom_mono (f : C ⟶ D) (hf : FixedObjectModel.cofibrations O f)
    (a b : C.val) : Mono (f.val.map a b) := by
  obtain ⟨x, hx⟩ := (verticesEquiv C).surjective a
  obtain ⟨y, hy⟩ := (verticesEquiv C).surjective b
  change vertex C x = a at hx
  change vertex C y = b at hy
  subst a
  subst b
  let t := congrArg₂ (fun a b : D.val => a ⟶[SSet.{u}] b) (map_vertex f x) (map_vertex f y)
  let _ : Mono (f.val.map (vertex C x) (vertex C y) ≫ eqToHom t) :=
    cofibration_homMap_mono f hf x y
  exact mono_of_mono (f.val.map (vertex C x) (vertex C y)) (eqToHom t)

end CategoryTheory.SimplicialEnrichment.FixedObjects
