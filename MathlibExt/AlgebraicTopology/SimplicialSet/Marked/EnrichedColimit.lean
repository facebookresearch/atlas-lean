/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedColimitObject

/-!
# The actual universal property of marked enriched pointwise colimits

Every original marked cocone descends through its evaluated marked
colimits. Whole source-injection detection proves full enriched
naturality of the resulting map. The original injection equations and
uniqueness prove the genuine colimit universal property, without an
enriched colimit or diagram-model outcome hypothesis.
-/

noncomputable section
universe u v w t
open CategoryTheory Limits

namespace SSet.Marked.EnrichedColimit

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type v} [EnrichedCategory SSet.{u} C]
    {J : Type w} [Category.{t} J] (K : J ⥤ EnrichedDiagram C)
    [∀ x : C, HasColimit (evaluated K x)]

/-- The actual marked cocone descends pointwise, retaining every whole enriched Hom action. -/
def desc (q : Cocone K) : object K ⟶ q.pt where
  app x := colimit.desc (evaluated K x) ((enrichedDiagramEvaluation C x).mapCocone q)
  naturality x y := by
    apply sourceMap_hom_ext K x (x ⟶[SSet.{u}] y) (q.pt.obj y)
    intro j
    let A := (K.obj j).obj x
    let B := (K.obj j).obj y
    let L := colimit (evaluated K x)
    let M := colimit (evaluated K y)
    let X := q.pt.obj x
    let Y := q.pt.obj y
    let p : A ⟶ L := colimit.ι (evaluated K x) j
    let r : B ⟶ M := colimit.ι (evaluated K y) j
    let dx : L ⟶ X := colimit.desc (evaluated K x) ((enrichedDiagramEvaluation C x).mapCocone q)
    let dy : M ⟶ Y := colimit.desc (evaluated K y) ((enrichedDiagramEvaluation C y).mapCocone q)
    let qx : A ⟶ X := (q.ι.app j).app x
    let qy : B ⟶ Y := (q.ι.app j).app y
    let f : (x ⟶[SSet.{u}] y) ⟶ mappingComplex .maximal A B := (K.obj j).map x y
    let g : (x ⟶[SSet.{u}] y) ⟶ mappingComplex .maximal X Y := q.pt.map x y
    let m := maxCurry (action K x y)
    have hp : p ≫ dx = qx := colimit.ι_desc (F := evaluated K x) ((enrichedDiagramEvaluation C x).mapCocone q) j
    have hr : r ≫ dy = qy := colimit.ι_desc (F := evaluated K y) ((enrichedDiagramEvaluation C y).mapCocone q) j
    have hm : m ≫ mappingComplexPre .maximal p M = f ≫ mappingComplexPost .maximal A r :=
      (injection_fullMap K x y j).symm
    have hq : f ≫ mappingComplexPost .maximal A qy = g ≫ mappingComplexPre .maximal qx Y :=
      (q.ι.app j).naturality x y
    calc
      (m ≫ mappingComplexPost .maximal L dy) ≫ mappingComplexPre .maximal p Y =
          m ≫ (mappingComplexPre .maximal p M ≫ mappingComplexPost .maximal A dy) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun h => m ≫ h) (mappingComplexPre_post .maximal p dy).symm)
      _ = (f ≫ mappingComplexPost .maximal A r) ≫ mappingComplexPost .maximal A dy :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun h => h ≫ mappingComplexPost .maximal A dy) hm)
      _ = f ≫ mappingComplexPost .maximal A (r ≫ dy) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun h => f ≫ h) (mappingComplexPost_comp .maximal A r dy).symm)
      _ = f ≫ mappingComplexPost .maximal A qy :=
        congrArg (fun h => f ≫ mappingComplexPost .maximal A h) hr
      _ = g ≫ mappingComplexPre .maximal qx Y := hq
      _ = g ≫ mappingComplexPre .maximal (p ≫ dx) Y :=
        congrArg (fun h => g ≫ mappingComplexPre .maximal h Y) hp.symm
      _ = (g ≫ mappingComplexPre .maximal dx Y) ≫ mappingComplexPre .maximal p Y :=
        (congrArg (fun h => g ≫ h) (mappingComplexPre_comp .maximal p dx Y)).trans
          (Category.assoc _ _ _).symm

/-- The descended map retains exactly each original evaluated marked colimit descent. -/
theorem desc_app (q : Cocone K) (x : C) :
    (desc K q).app x =
      colimit.desc (evaluated K x) ((enrichedDiagramEvaluation C x).mapCocone q) := rfl

/-- Every whole original enriched injection factors through the descended cocone map. -/
theorem injection_desc (q : Cocone K) (j : J) : injection K j ≫ desc K q = q.ι.app j := by
  apply EnrichedDiagramMap.ext
  funext x
  exact colimit.ι_desc (F := evaluated K x) ((enrichedDiagramEvaluation C x).mapCocone q) j

/-- The constructed original enriched cocone is a genuine colimit, with both the native descent and
  uniqueness proved. -/
def isColimit : IsColimit (cocone K) where
  desc := desc K
  fac q j := injection_desc K q j
  uniq q f hf := by
    apply EnrichedDiagramMap.ext
    funext x
    apply colimit.hom_ext
    intro j
    have h := congrArg (fun a => a.app x) (hf j)
    exact h.trans (colimit.ι_desc (F := evaluated K x) ((enrichedDiagramEvaluation C x).mapCocone q) j).symm

/-- Actual evaluated marked colimits give the original full enriched colimit. -/
theorem hasColimit : HasColimit K := ⟨⟨cocone K, isColimit K⟩⟩

end SSet.Marked.EnrichedColimit
