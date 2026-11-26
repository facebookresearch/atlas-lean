/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLimitLaws

/-!
# Genuine native marked enriched limits

The marked pointwise limit and its whole Hom action define the actual
enriched object. Full target-projection detection proves naturality
of each original cone lift; the whole projection equations and
uniqueness give its genuine limit universal property. These limits
remain at the original coefficient size, without any model input.
-/

noncomputable section
universe u v w t
open CategoryTheory Limits

namespace SSet.Marked.EnrichedLimit
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type v} [EnrichedCategory SSet.{u} C]
    {J : Type w} [Category.{t} J] (K : J ⥤ EnrichedDiagram C)
    [∀ x : C, HasLimit (evaluated K x)]

/-- The actual marked pointwise limit with its proved whole original enriched Hom action. -/
def object : EnrichedDiagram C where
  obj x := limit (evaluated K x)
  map x y := maxCurry (action K x y)
  map_id x := fullMap_id K x
  map_comp x y z := fullMap_comp K x y z

/-- Every original marked projection is a full enriched natural map. -/
def projection (j : J) : object K ⟶ K.obj j where
  app x := limit.π (evaluated K x) j
  naturality x y := projection_fullMap K x y j

/-- The original marked pointwise limit projections form the actual full enriched cone. -/
def cone : Cone K where
  pt := object K
  π :=
    { app j := projection K j
      naturality i j f := by
        apply EnrichedDiagramMap.ext
        funext x
        exact (Category.id_comp _).trans (limit.w (evaluated K x) f).symm }

/-- The actual marked cone lifts pointwise, and full projection detection proves its entire enriched naturality. -/
def lift (q : Cone K) : q.pt ⟶ object K where
  app x := limit.lift (evaluated K x) ((enrichedDiagramEvaluation C x).mapCone q)
  naturality x y := by
    apply targetMap_hom_ext K y (x ⟶[SSet.{u}] y) (q.pt.obj x)
    intro j
    let A := q.pt.obj x
    let B := q.pt.obj y
    let L := limit (evaluated K x)
    let M := limit (evaluated K y)
    let X := (K.obj j).obj x
    let Y := (K.obj j).obj y
    let px : L ⟶ X := limit.π (evaluated K x) j
    let py : M ⟶ Y := limit.π (evaluated K y) j
    let dx : A ⟶ L := limit.lift (evaluated K x) ((enrichedDiagramEvaluation C x).mapCone q)
    let dy : B ⟶ M := limit.lift (evaluated K y) ((enrichedDiagramEvaluation C y).mapCone q)
    let qx : A ⟶ X := (q.π.app j).app x
    let qy : B ⟶ Y := (q.π.app j).app y
    let f : (x ⟶[SSet.{u}] y) ⟶ mappingComplex .maximal A B := q.pt.map x y
    let g : (x ⟶[SSet.{u}] y) ⟶ mappingComplex .maximal X Y := (K.obj j).map x y
    let m := maxCurry (action K x y)
    have hx : dx ≫ px = qx := limit.lift_π ((enrichedDiagramEvaluation C x).mapCone q) j
    have hy : dy ≫ py = qy := limit.lift_π ((enrichedDiagramEvaluation C y).mapCone q) j
    have hm : m ≫ mappingComplexPost .maximal L py = g ≫ mappingComplexPre .maximal px Y :=
      projection_fullMap K x y j
    have hq : f ≫ mappingComplexPost .maximal A qy = g ≫ mappingComplexPre .maximal qx Y :=
      (q.π.app j).naturality x y
    calc
      (f ≫ mappingComplexPost .maximal A dy) ≫ mappingComplexPost .maximal A py =
          f ≫ mappingComplexPost .maximal A (dy ≫ py) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun t => f ≫ t) (mappingComplexPost_comp .maximal A dy py).symm)
      _ = f ≫ mappingComplexPost .maximal A qy :=
        congrArg (fun t => f ≫ mappingComplexPost .maximal A t) hy
      _ = g ≫ mappingComplexPre .maximal qx Y := hq
      _ = g ≫ mappingComplexPre .maximal (dx ≫ px) Y :=
        congrArg (fun t => g ≫ mappingComplexPre .maximal t Y) hx.symm
      _ = (g ≫ mappingComplexPre .maximal px Y) ≫ mappingComplexPre .maximal dx Y :=
        (congrArg (fun t => g ≫ t) (mappingComplexPre_comp .maximal dx px Y)).trans
          (Category.assoc _ _ _).symm
      _ = (m ≫ mappingComplexPost .maximal L py) ≫ mappingComplexPre .maximal dx Y :=
        congrArg (fun t => t ≫ mappingComplexPre .maximal dx Y) hm.symm
      _ = (m ≫ mappingComplexPre .maximal dx M) ≫ mappingComplexPost .maximal A py :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun t => m ≫ t) (mappingComplexPre_post .maximal dx py).symm).trans
            (Category.assoc _ _ _).symm)

/-- Every original whole projection factors through the actual marked cone lift. -/
theorem lift_projection (q : Cone K) (j : J) : lift K q ≫ projection K j = q.π.app j := by
  apply EnrichedDiagramMap.ext
  funext x
  exact limit.lift_π ((enrichedDiagramEvaluation C x).mapCone q) j

/-- The constructed full enriched cone has the native limit universal property and uniqueness. -/
def isLimit : IsLimit (cone K) where
  lift := lift K
  fac q j := lift_projection K q j
  uniq q f hf := by
    apply EnrichedDiagramMap.ext
    funext x
    apply limit.hom_ext
    intro j
    have h := congrArg (fun a => a.app x) (hf j)
    exact h.trans (limit.lift_π ((enrichedDiagramEvaluation C x).mapCone q) j).symm

/-- Original evaluated marked limits supply the actual enriched limit. -/
theorem hasLimit : HasLimit K := ⟨⟨cone K, isLimit K⟩⟩

end SSet.Marked.EnrichedLimit

namespace SSet.Marked.EnrichedLimit
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Original coefficient-sized marked limits give all genuine enriched diagram limits at exactly that size. -/
theorem hasLimits (C : Type v) [EnrichedCategory SSet.{u} C] :
    HasLimitsOfSize.{u, u} (EnrichedDiagram C) where
  has_limits_of_shape J _ :=
    { has_limit K := by
        let _ : ∀ x : C, HasLimit (evaluated K x) := fun _ => inferInstance
        exact hasLimit K }

end SSet.Marked.EnrichedLimit
