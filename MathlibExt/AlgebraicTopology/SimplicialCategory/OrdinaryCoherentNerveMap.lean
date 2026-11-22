/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentVertices
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedEdgeReadback
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMappingEdges
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# The original ordinary functor as a complete coherent nerve map

Every actual ordinal functor determines a coherent simplex on its same
objects. Each original path-poset Hom nerve maps by the supplied ordinary
composite's hom-unit map. All paths, simplex operators and original arrows
are retained. No component category or localization conclusion is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w

open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OrdinaryNerveMap

open SimplicialEnrichment

private def firstPath {n : SimplexCategory} (i j : coherentSimplex.{u} n)
    (q : SimplexCategoryᵒᵖ) (a : (i ⟶[SSet.{u}] j).obj q) : SimplicialThickening.Path i.as j.as :=
  (show Fin (q.unop.len + 1) ⥤ SimplicialThickening.Path i.as j.as from a).obj 0

private def ordinalArrow {C : Carrier.{u}} {n : SimplexCategory}
    (F : Fin (n.len + 1) ⥤ ForgetEnrichment SSet.{u} C)
    (i j : coherentSimplex.{u} n) (h : i.as ≤ j.as) :
    𝟙_ SSet.{u} ⟶ (ForgetEnrichment.to SSet.{u} (F.obj i.as.down) ⟶[SSet.{u}]
      ForgetEnrichment.to SSet.{u} (F.obj j.as.down)) :=
  ForgetEnrichment.homTo SSet.{u} (F.map (homOfLE (show i.as.down ≤ j.as.down from h)))

/-- The supplied original ordinal functor gives the entire original enriched coherent simplex. -/
def simplex {C : Carrier.{u}} {n : SimplexCategory}
    (F : Fin (n.len + 1) ⥤ ForgetEnrichment SSet.{u} C) : CoherentSimplexIn C n where
  obj i := ForgetEnrichment.to SSet.{u} (F.obj i.as.down)
  map i j := {
    app q := ↾fun a => (ordinalArrow F i j (firstPath i j q a).le).app q PUnit.unit
    naturality q r θ := by
      ext a
      exact ConcreteCategory.congr_hom ((ordinalArrow F i j (firstPath i j q a).le).naturality θ) PUnit.unit }
  map_id i := by
    ext q a
    cases a
    change (ForgetEnrichment.homTo SSet.{u} (F.map (𝟙 i.as.down))).app q PUnit.unit =
      (eId SSet.{u} (ForgetEnrichment.to SSet.{u} (F.obj i.as.down))).app q PUnit.unit
    rw [Functor.map_id, ForgetEnrichment.homTo_id]
  map_comp i j k := by
    ext q a
    let f : i.as.down ⟶ j.as.down := homOfLE (show i.as.down ≤ j.as.down from (firstPath i j q a.1).le)
    let g : j.as.down ⟶ k.as.down := homOfLE (show j.as.down ≤ k.as.down from (firstPath j k q a.2).le)
    change (ForgetEnrichment.homTo SSet.{u} (F.map (f ≫ g))).app q PUnit.unit =
      (eComp SSet.{u} (ForgetEnrichment.to SSet.{u} (F.obj i.as.down))
        (ForgetEnrichment.to SSet.{u} (F.obj j.as.down))
        (ForgetEnrichment.to SSet.{u} (F.obj k.as.down))).app q
          ((ForgetEnrichment.homTo SSet.{u} (F.map f)).app q PUnit.unit,
            (ForgetEnrichment.homTo SSet.{u} (F.map g)).app q PUnit.unit)
    rw [Functor.map_comp, ForgetEnrichment.homTo_comp]
    rfl

/-- Every original simplex operator preserves the supplied entire ordinal functor and coherent Hom maps. -/
theorem simplex_operator {C : Carrier.{u}} {n m : SimplexCategory} (θ : n ⟶ m)
    (F : Fin (m.len + 1) ⥤ ForgetEnrichment SSet.{u} C) :
    simplex ((SimplexCategory.toCat.map θ).toFunctor ⋙ F) =
      (coherentSimplexMap θ).comp SSet.{u} (simplex F) := by
  refine EnrichedFunctor.ext SSet.{u} (fun _ => rfl) ?_
  intro i j
  change (simplex ((SimplexCategory.toCat.map θ).toFunctor ⋙ F)).map i j ≫ 𝟙 _ =
    (coherentSimplexMap θ).map i j ≫ (simplex F).map _ _
  rw [Category.comp_id]
  ext q a
  rfl

/-- The actual original ordinary functor induces its complete coherent nerve map in the common universe. -/
def map {A : Type v} [Category.{w} A] (C : Carrier.{max v w})
    (F : A ⥤ ForgetEnrichment SSet.{max v w} C) : nerve A ⟶ coherentNerveFunctor.obj C where
  app q := ↾fun a => simplex (a ⋙ F)
  naturality q r θ := by
    ext a
    change simplex ((SimplexCategory.toCat.map θ.unop).toFunctor ⋙ (a ⋙ F)) =
      (coherentSimplexMap θ.unop).comp SSet.{max v w} (simplex (a ⋙ F))
    exact simplex_operator θ.unop (a ⋙ F)

/-- Each original ordinary simplex retains the SAME entire ordinal functor as its coherent simplex. -/
theorem map_app {A : Type v} [Category.{w} A] (C : Carrier.{max v w})
    (F : A ⥤ ForgetEnrichment SSet.{max v w} C) (q : SimplexCategoryᵒᵖ) (a : (nerve A).obj q) :
    (map C F).app q a = simplex (a ⋙ F) := rfl

/-- The SAME original ordinary object is the actual coherent-nerve vertex. -/
theorem map_vertex {A : Type v} [Category.{w} A] (C : Carrier.{max v w})
    (F : A ⥤ ForgetEnrichment SSet.{max v w} C) (a : A) :
    (map C F).app (op ⦋0⦌) (ComposableArrows.mk₀ a) =
      constantSimplex C ⦋0⦌ (ForgetEnrichment.to SSet.{max v w} (F.obj a)) := by
  apply (verticesEquiv C).injective
  rfl

private def originalEdge {A : Type v} [Category.{w} A] (C : Carrier.{max v w})
    (F : A ⥤ ForgetEnrichment SSet.{max v w} C) {a b : A} (f : a ⟶ b) :
    HomMappingCells.FixedSimplex (ForgetEnrichment.to SSet.{max v w} (F.obj a))
      (ForgetEnrichment.to SSet.{max v w} (F.obj b)) (n := 0) :=
  ⟨(map C F).app (op ⦋1⦌) (ComposableArrows.mk₁ f), rfl, rfl⟩

private theorem originalEdge_read {A : Type v} [Category.{w} A] (C : Carrier.{max v w})
    (F : A ⥤ ForgetEnrichment SSet.{max v w} C) {a b : A} (f : a ⟶ b) :
    FixedEdgeReadback.readVertex _ _ (originalEdge C F f) =
      (ForgetEnrichment.to SSet.{max v w} (F.obj a) ⟶[SSet.{max v w}]
        ForgetEnrichment.to SSet.{max v w} (F.obj b)).unitHomEquiv
          (ForgetEnrichment.homTo SSet.{max v w} (F.map f)) := by
  rfl

/-- The SAME ordinary arrow is the whole original coherent edge of its actual hom-unit representative. -/
theorem map_edge {A : Type v} [Category.{w} A] (C : Carrier.{max v w})
    (F : A ⥤ ForgetEnrichment SSet.{max v w} C) {a b : A} (f : a ⟶ b) :
    (map C F).app (op ⦋1⦌) (ComposableArrows.mk₁ f) =
      (MappingEdges.edge (ForgetEnrichment.to SSet.{max v w} (F.obj a))
        (ForgetEnrichment.to SSet.{max v w} (F.obj b))
          ((ForgetEnrichment.to SSet.{max v w} (F.obj a) ⟶[SSet.{max v w}]
            ForgetEnrichment.to SSet.{max v w} (F.obj b)).unitHomEquiv
              (ForgetEnrichment.homTo SSet.{max v w} (F.map f)))).edge := by
  let x := ForgetEnrichment.to SSet.{max v w} (F.obj a)
  let y := ForgetEnrichment.to SSet.{max v w} (F.obj b)
  let σ := originalEdge C F f
  let τ := (x ⟶[SSet.{max v w}] y).unitHomEquiv (ForgetEnrichment.homTo SSet.{max v w} (F.map f))
  have h := congrArg Subtype.val (FixedEdgeReadback.construct_read x y σ)
  rw [originalEdge_read C F f] at h
  change HomSimplex.simplex x y (SSet.yonedaEquiv.symm τ) = (map C F).app (op ⦋1⦌) _ at h
  exact h.symm.trans (MappingEdges.edge_readback x y τ).symm

end CategoryTheory.CoherentRealization.OrdinaryNerveMap
