/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentUnit
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentVertices

/-!
# Actual evaluation counit of coherent realization

Each coherent generator is evaluated by its original enriched simplex
functor. The original endpoint equations determine the equality
transports. All defining relations are proved on these literal maps.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization
open SimplicialEnrichment SimplicialQuiver

/-- Reading a vertex of a coherent-nerve simplex gives exactly its original enriched object. -/
theorem vertexOf_vertex (C : Carrier.{u}) {n : SimplexCategory} (σ : CoherentSimplexIn C n)
    (i : coherentSimplex.{u} n) :
    vertexOf C (vertex (coherentNerveFunctor.obj C) σ i) = σ.obj i := rfl

/-- The actual original object and Hom evaluation of the coherent generating quiver. -/
def counitInterpretation (C : Carrier.{u}) :
    Interpretation (generatingQuiver (coherentNerveFunctor.obj C)) C where
  obj := vertexOf C
  map x y := {
    app q := ↾fun a =>
      ((a.simplex.map a.source a.target) ≫ eqToHom
        (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y)
          (congrArg (vertexOf C) a.source_eq) (congrArg (vertexOf C) a.target_eq))).app q a.hom
    naturality q r f := by
      ext a
      cases a with
      | mk n σ i j hx hy a =>
          let φ := σ.map i j ≫ eqToHom
            (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y)
              (congrArg (vertexOf C) hx) (congrArg (vertexOf C) hy))
          exact congr($(φ.naturality f) a) }

/-- Each generating path is evaluated by its actual original enriched Hom map and endpoint
transports. -/
theorem counit_eval_arrow (C : Carrier.{u}) {n : SimplexCategory} (σ : CoherentSimplexIn C n)
    (i j : coherentSimplex.{u} n) {x y : (coherentNerveFunctor.obj C) _⦋0⦌}
    (hx : vertex (coherentNerveFunctor.obj C) σ i = x)
    (hy : vertex (coherentNerveFunctor.obj C) σ j = y)
    {q : SimplexCategoryᵒᵖ} (a : (i ⟶[SSet.{u}] j).obj q) :
    (counitInterpretation C).evalPath q (arrowPath (coherentNerveFunctor.obj C) σ i j hx hy a) =
      (σ.map i j ≫ eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y)
        (congrArg (vertexOf C) hx) (congrArg (vertexOf C) hy))).app q a :=
  congr($((counitInterpretation C).generator_eval x y).app q
    (arrow (coherentNerveFunctor.obj C) σ i j hx hy a))

/-- Actual evaluation satisfies every defining coherent realization equation. -/
theorem counit_relations (C : Carrier.{u}) (q : SimplexCategoryᵒᵖ)
    (x y : (coherentNerveFunctor.obj C) _⦋0⦌)
    (p r : Path (generatingQuiver (coherentNerveFunctor.obj C)) q x y)
    (h : relations (coherentNerveFunctor.obj C) q x y p r) :
    (counitInterpretation C).evalPath q p = (counitInterpretation C).evalPath q r := by
  cases h with
  | @identity n σ i x hx =>
      subst x
      have ha := counit_eval_arrow C σ i i rfl rfl ((eId SSet.{u} i).app q PUnit.unit)
      change (counitInterpretation C).evalPath q
        (arrowPath (coherentNerveFunctor.obj C) σ i i rfl rfl ((eId SSet.{u} i).app q PUnit.unit)) =
          (σ.map i i).app q ((eId SSet.{u} i).app q PUnit.unit) at ha
      exact ha.trans ((congr($(σ.map_id i).app q PUnit.unit)).trans
        ((counitInterpretation C).evalPath_nil q (vertex (coherentNerveFunctor.obj C) σ i)).symm)
  | @composition n σ i j k x y z hx hy hz a b =>
      subst_vars
      have ha := counit_eval_arrow C σ i k rfl rfl ((eComp SSet.{u} i j k).app q (a, b))
      have hi := counit_eval_arrow C σ i j rfl rfl a
      have hj := counit_eval_arrow C σ j k rfl rfl b
      change (counitInterpretation C).evalPath q (arrowPath (coherentNerveFunctor.obj C) σ
        i j rfl rfl a) =
        (σ.map i j).app q a at hi
      change (counitInterpretation C).evalPath q (arrowPath (coherentNerveFunctor.obj C) σ
        j k rfl rfl b) =
        (σ.map j k).app q b at hj
      change (counitInterpretation C).evalPath q
        (arrowPath (coherentNerveFunctor.obj C) σ i k rfl rfl ((eComp SSet.{u} i j k).app q
          (a, b))) =
          (σ.map i k).app q ((eComp SSet.{u} i j k).app q (a, b)) at ha
      have hc : (σ.map i k).app q ((eComp SSet.{u} i j k).app q (a, b)) =
          (eComp SSet.{u} (σ.obj i) (σ.obj j) (σ.obj k)).app q
            ((σ.map i j).app q a, (σ.map j k).app q b) :=
        congr($(σ.map_comp i j k).app q (a, b))
      have hp : (eComp SSet.{u} (σ.obj i) (σ.obj j) (σ.obj k)).app q
          ((σ.map i j).app q a, (σ.map j k).app q b) =
            (eComp SSet.{u} (σ.obj i) (σ.obj j) (σ.obj k)).app q
              ((counitInterpretation C).evalPath q (arrowPath (coherentNerveFunctor.obj C)
                σ i j rfl rfl a),
                (counitInterpretation C).evalPath q (arrowPath (coherentNerveFunctor.obj C)
                  σ j k rfl rfl b)) :=
        congrArg (fun t => (eComp SSet.{u} (σ.obj i) (σ.obj j) (σ.obj k)).app q t)
          (Prod.ext hi.symm hj.symm)
      exact ha.trans (hc.trans (hp.trans
        ((counitInterpretation C).evalPath_comp q
          (arrowPath (coherentNerveFunctor.obj C) σ i j rfl rfl a)
          (arrowPath (coherentNerveFunctor.obj C) σ j k rfl rfl b)).symm))
  | @operator n m f σ i j x y hx hy a =>
      subst x
      subst y
      exact (counit_eval_arrow C ((coherentNerveFunctor.obj C).map f.op σ) i j rfl rfl a).trans
        (counit_eval_arrow C σ ((coherentSimplexMap f).obj i) ((coherentSimplexMap f).obj j)
          (vertex_operator (coherentNerveFunctor.obj C) f σ i).symm
          (vertex_operator (coherentNerveFunctor.obj C) f σ j).symm
          (((coherentSimplexMap f).map i j).app q a)).symm

/-- The genuine coherent realization evaluation counit on the original enriched category carrier. -/
def counit (C : Carrier.{u}) : realization (coherentNerveFunctor.obj C) ⟶ C :=
  (counitInterpretation C).descend (relations (coherentNerveFunctor.obj C)) (counit_relations C)

/-- The actual counit reads the individual original enriched object of the given coherent vertex. -/
theorem counit_obj (C : Carrier.{u}) (x : (coherentNerveFunctor.obj C) _⦋0⦌) :
    (counit C).obj x = vertexOf C x := rfl

/-- Counit evaluation of a whole inserted coherent Hom is the same original enriched Hom map. -/
theorem counit_simplexHom (C : Carrier.{u}) {n : SimplexCategory} (σ : CoherentSimplexIn C n)
    (i j : coherentSimplex.{u} n) :
    simplexHom (coherentNerveFunctor.obj C) σ i j rfl rfl ≫
      (counit C).map (vertex (coherentNerveFunctor.obj C) σ i) (vertex
        (coherentNerveFunctor.obj C) σ j) =
        σ.map i j := by
  ext q a
  exact counit_eval_arrow C σ i j rfl rfl a

/-- The whole nerve triangle is the identity on every original coherent simplex. -/
theorem nerve_triangle (C : Carrier.{u}) :
    unit (coherentNerveFunctor.obj C) ≫ coherentNerveFunctor.map (counit C) =
      𝟙 (coherentNerveFunctor.obj C) := by
  ext n σ
  refine EnrichedFunctor.ext SSet.{u}
    (F := (simplexInto (coherentNerveFunctor.obj C) σ).comp SSet.{u} (counit C)) (G := σ)
    (fun _ => rfl) ?_
  intro i j
  change (simplexHom (coherentNerveFunctor.obj C) σ i j rfl rfl ≫
    (counit C).map (vertex (coherentNerveFunctor.obj C) σ i) (vertex
      (coherentNerveFunctor.obj C) σ j)) ≫
      𝟙 _ = σ.map i j
  exact (Category.comp_id _).trans (counit_simplexHom C σ i j)

end CategoryTheory.CoherentRealization
