/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLimitAction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingCompositionNaturality

/-!
# Full identity and composition for original marked enriched limits

The original target projections detect entire marked parameter prisms.
Their actual component-action equations prove identity and composition
with the same original scalar parameter and every original coefficient.
No vertex-only naturality or target model is used.
-/

noncomputable section
universe u v w t
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.EnrichedLimit
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type v} [EnrichedCategory SSet.{u} C]
    {J : Type w} [Category.{t} J] (K : J ⥤ EnrichedDiagram C)

/-- The original identity action descends to the entire marked limit Hom, as detected by all projections. -/
theorem fullMap_id (x : C) [HasLimit (evaluated K x)] :
    eId SSet.{u} x ≫ maxCurry (action K x x) = maxMappingIdentity (limit (evaluated K x)) := by
  apply targetMap_hom_ext K x (𝟙_ SSet.{u}) (limit (evaluated K x))
  intro j
  let A := (K.obj j).obj x
  let L := limit (evaluated K x)
  let p : L ⟶ A := limit.π (evaluated K x) j
  let f : (x ⟶[SSet.{u}] x) ⟶ mappingComplex .maximal A A := (K.obj j).map x x
  let m := maxCurry (action K x x)
  have hp : m ≫ mappingComplexPost .maximal L p = f ≫ mappingComplexPre .maximal p A :=
    projection_fullMap K x x j
  have hi : eId SSet.{u} x ≫ f = maxMappingIdentity A := (K.obj j).map_id x
  calc
    (eId SSet.{u} x ≫ m) ≫ mappingComplexPost .maximal L p =
        eId SSet.{u} x ≫ (m ≫ mappingComplexPost .maximal L p) := Category.assoc _ _ _
    _ = eId SSet.{u} x ≫ (f ≫ mappingComplexPre .maximal p A) :=
      congrArg (fun t => eId SSet.{u} x ≫ t) hp
    _ = (eId SSet.{u} x ≫ f) ≫ mappingComplexPre .maximal p A := (Category.assoc _ _ _).symm
    _ = maxMappingIdentity A ≫ mappingComplexPre .maximal p A :=
      congrArg (fun t => t ≫ mappingComplexPre .maximal p A) hi
    _ = maxMappingPoint p := maxMappingIdentity_pre p
    _ = maxMappingIdentity L ≫ mappingComplexPost .maximal L p := (maxMappingIdentity_post p).symm

/-- Every whole original enriched composition prism acts on the marked limit through the same original
  component composition. -/
theorem fullMap_comp (x y z : C) [HasLimit (evaluated K x)]
    [HasLimit (evaluated K y)] [HasLimit (evaluated K z)] :
    eComp SSet.{u} x y z ≫ maxCurry (action K x z) =
      (maxCurry (action K x y) ⊗ₘ maxCurry (action K y z)) ≫
        maxMappingCompose (limit (evaluated K x)) (limit (evaluated K y)) (limit (evaluated K z)) := by
  ext n fg
  apply limit.hom_ext
  intro j
  apply Hom.ext
  ext q a
  let px : limit (evaluated K x) ⟶ (K.obj j).obj x := limit.π (evaluated K x) j
  let py : limit (evaluated K y) ⟶ (K.obj j).obj y := limit.π (evaluated K y) j
  let pz : limit (evaluated K z) ⟶ (K.obj j).obj z := limit.π (evaluated K z) j
  let θ := (SSet.stdSimplex.objEquiv a.1).op
  let f := (x ⟶[SSet.{u}] y).map θ fg.1
  let g := (y ⟶[SSet.{u}] z).map θ fg.2
  let h := (SSet.yonedaEquiv.symm ((eComp SSet.{u} x y z).app n fg)).app q a.1
  have hc : h = (eComp SSet.{u} x y z).app q (f, g) :=
    congr($((eComp SSet.{u} x y z).naturality θ) fg).symm
  have hxy : py.hom.app q ((action K x y).hom.app q (f, a.2)) =
      (enrichedDiagramAction (K.obj j) x y).hom.app q (f, px.hom.app q a.2) :=
    congr($(action_projection K x y j).hom.app q (f, a.2))
  have hxz : pz.hom.app q ((action K x z).hom.app q (h, a.2)) =
      (enrichedDiagramAction (K.obj j) x z).hom.app q (h, px.hom.app q a.2) :=
    congr($(action_projection K x z j).hom.app q (h, a.2))
  have hyz : pz.hom.app q ((action K y z).hom.app q
      (g, (action K x y).hom.app q (f, a.2))) =
        (enrichedDiagramAction (K.obj j) y z).hom.app q
          (g, py.hom.app q ((action K x y).hom.app q (f, a.2))) :=
    congr($(action_projection K y z j).hom.app q (g, (action K x y).hom.app q (f, a.2)))
  change pz.hom.app q ((action K x z).hom.app q (h, a.2)) =
    pz.hom.app q ((action K y z).hom.app q (g, (action K x y).hom.app q (f, a.2)))
  exact hxz.trans ((congrArg (fun t => (enrichedDiagramAction (K.obj j) x z).hom.app q
    (t, px.hom.app q a.2)) hc).trans
      ((enrichedDiagramAction_comp (K.obj j) x y z q f g (px.hom.app q a.2)).trans
        ((congrArg (fun t => (enrichedDiagramAction (K.obj j) y z).hom.app q (g, t)) hxy.symm).trans hyz.symm)))

end SSet.Marked.EnrichedLimit
