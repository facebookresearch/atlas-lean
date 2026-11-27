/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentVertices

/-!
# Independent original object and Hom universes

An actual simplicial enrichment with independent object and Hom universes
has an explicit common-universe lift. Objects are individual `ULift`
vertices and Hom simplices are the original simplices with `ULift` tags.
Identity, composition, all operators and enriched maps retain literal
up/down readback. No original objects are replaced by component classes.
-/

noncomputable section
universe u v w
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment
variable (C : Type v) [EnrichedCategory SSet.{u} C]

/-- The explicit common-universe enrichment of the same individual original objects and Hom
simplices. -/
@[instance_reducible]
def liftedEnrichment : EnrichedCategory SSet.{max u v w} (ULift.{max u w} C) where
  Hom x y := SSet.uliftFunctor.{max v w, u}.obj (x.down ⟶[SSet.{u}] y.down)
  id x := {
    app n := ↾fun _ => ULift.up ((eId SSet.{u} x.down).app n PUnit.unit)
    naturality n m f := by
      ext a
      apply ULift.ext
      exact congr($((eId SSet.{u} x.down).naturality f) PUnit.unit) }
  comp x y z := {
    app n := ↾fun a => ULift.up ((eComp SSet.{u} x.down y.down z.down).app n (a.1.down, a.2.down))
    naturality n m f := by
      ext a
      apply ULift.ext
      exact congr($((eComp SSet.{u} x.down y.down z.down).naturality f) (a.1.down, a.2.down)) }
  id_comp x y := by
    ext n a
    apply ULift.ext
    exact congr($(e_id_comp SSet.{u} x.down y.down).app n a.down)
  comp_id x y := by
    ext n a
    apply ULift.ext
    exact congr($(e_comp_id SSet.{u} x.down y.down).app n a.down)
  assoc a b c d := by
    ext n p
    apply ULift.ext
    exact congr($(e_assoc SSet.{u} a.down b.down c.down d.down).app n
      (p.1.down, p.2.1.down, p.2.2.down))

/-- Bundle the actual common-universe lift for the coherent realization and nerve adjunction. -/
def liftedCarrier : Carrier.{max u v w} := by
  letI := liftedEnrichment.{u, v, w} C
  exact SimplicialEnrichment.of (ULift.{max u w} C)

variable {C} {D : Type v} [EnrichedCategory SSet.{u} D]

/-- A supplied original enriched functor acts on the exact lifted original objects and Hom
simplices. -/
def liftedMap (F : EnrichedFunctor SSet.{u} C D) : liftedCarrier.{u, v,
  w} C ⟶ liftedCarrier.{u, v, w} D where
  obj x := ULift.up (F.obj x.down)
  map x y := {
    app n := ↾fun a => ULift.up ((F.map x.down y.down).app n a.down)
    naturality n m f := by
      ext a
      apply ULift.ext
      exact congr($((F.map x.down y.down).naturality f) a.down) }
  map_id x := by
    ext n a
    apply ULift.ext
    exact congr($(F.map_id x.down).app n PUnit.unit)
  map_comp x y z := by
    ext n a
    apply ULift.ext
    exact congr($(F.map_comp x.down y.down z.down).app n (a.1.down, a.2.down))

/-- Lifted object maps read back the same supplied individual original object map. -/
theorem liftedMap_obj_up (F : EnrichedFunctor SSet.{u} C D) (x : C) :
    (liftedMap.{u, v, w} F).obj (ULift.up x) = ULift.up (F.obj x) := rfl

/-- Every lifted original Hom simplex reads back exactly the supplied actual enriched Hom map. -/
theorem liftedMap_hom_up (F : EnrichedFunctor SSet.{u} C D) (x y : C) (n : SimplexCategoryᵒᵖ)
    (a : (x ⟶[SSet.{u}] y).obj n) :
    (((liftedMap.{u, v, w} F).map (ULift.up x) (ULift.up y)).app n (ULift.up a)).down =
      (F.map x y).app n a := rfl

/-- Coherent-nerve vertices of the explicit common-universe lift are the same individual
original objects. -/
def originalVerticesEquiv (C : Type v) [EnrichedCategory SSet.{u} C] :
    CoherentSimplexIn (liftedCarrier.{u, v, w} C) ⦋0⦌ ≃ C :=
  (verticesEquiv (liftedCarrier C)).trans Equiv.ulift

/-- Original vertex readback commutes with the supplied actual enriched functor in the
independent universes. -/
theorem originalVerticesEquiv_map (F : EnrichedFunctor SSet.{u} C D)
    (σ : CoherentSimplexIn (liftedCarrier.{u, v, w} C) ⦋0⦌) :
    originalVerticesEquiv D ((coherentNerveFunctor.map (liftedMap F)).app (op ⦋0⦌) σ) =
      F.obj (originalVerticesEquiv C σ) := rfl

end CategoryTheory.SimplicialEnrichment
