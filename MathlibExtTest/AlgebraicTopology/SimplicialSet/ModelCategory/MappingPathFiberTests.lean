/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MappingPathFiber

/-!
# Direct clients of the computed ending-path/strict mapping-path Iso

Only the defining owner is imported. The original map and base vertex are
arbitrary; no Kan, fibration, weakness or supplied comparison input is used.
Both coordinate pairs and both actual inverse roundtrips are checked,
including explicit carrier universes zero, one and two.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

#check SSet.pathHomotopyFiberStrictMappingPathIso
#print axioms SSet.pathHomotopyFiberStrictMappingPathIso
#check SSet.pathHomotopyFiberStrictMappingPathIso_hom_total
#print axioms SSet.pathHomotopyFiberStrictMappingPathIso_hom_total
#check SSet.pathHomotopyFiberStrictMappingPathIso_hom_path
#print axioms SSet.pathHomotopyFiberStrictMappingPathIso_hom_path
#check SSet.pathHomotopyFiberStrictMappingPathIso_inv_total
#print axioms SSet.pathHomotopyFiberStrictMappingPathIso_inv_total
#check SSet.pathHomotopyFiberStrictMappingPathIso_inv_path
#print axioms SSet.pathHomotopyFiberStrictMappingPathIso_inv_path

namespace MappingPathFiberTests

example {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    SSet.pathHomotopyFiber f b ≅
      (SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b : SSet.{u}) :=
  SSet.pathHomotopyFiberStrictMappingPathIso f b

example {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    (SSet.pathHomotopyFiberStrictMappingPathIso f b).hom ≫
      ((SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b).ι ≫
        SSet.mappingPathRetract f) = SSet.pathHomotopyFiberToTotal f b :=
  SSet.pathHomotopyFiberStrictMappingPathIso_hom_total f b

example {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    (SSet.pathHomotopyFiberStrictMappingPathIso f b).hom ≫
      ((SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b).ι ≫
        SSet.mappingPathEval f) = SSet.pathHomotopyFiberPath f b :=
  SSet.pathHomotopyFiberStrictMappingPathIso_hom_path f b

example {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    (SSet.pathHomotopyFiberStrictMappingPathIso f b).inv ≫
      SSet.pathHomotopyFiberToTotal f b =
        (SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b).ι ≫
          SSet.mappingPathRetract f :=
  SSet.pathHomotopyFiberStrictMappingPathIso_inv_total f b

example {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    (SSet.pathHomotopyFiberStrictMappingPathIso f b).inv ≫
      SSet.pathHomotopyFiberPath f b =
        (SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b).ι ≫
          SSet.mappingPathEval f :=
  SSet.pathHomotopyFiberStrictMappingPathIso_inv_path f b

example {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    (SSet.pathHomotopyFiberStrictMappingPathIso f b).hom ≫
        (SSet.pathHomotopyFiberStrictMappingPathIso f b).inv =
      𝟙 (SSet.pathHomotopyFiber f b) :=
  (SSet.pathHomotopyFiberStrictMappingPathIso f b).hom_inv_id

example {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    (SSet.pathHomotopyFiberStrictMappingPathIso f b).inv ≫
        (SSet.pathHomotopyFiberStrictMappingPathIso f b).hom =
      𝟙 (SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b : SSet.{u}) :=
  (SSet.pathHomotopyFiberStrictMappingPathIso f b).inv_hom_id

-- The entire six-equation contract at carrier universe 0.
example {X B : SSet.{0}} (f : X ⟶ B) (b : B _⦋0⦌) :
    let e := SSet.pathHomotopyFiberStrictMappingPathIso f b
    let F := SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b
    (e.hom ≫ (F.ι ≫ SSet.mappingPathRetract f) = SSet.pathHomotopyFiberToTotal f b) ∧
      (e.hom ≫ (F.ι ≫ SSet.mappingPathEval f) = SSet.pathHomotopyFiberPath f b) ∧
      (e.inv ≫ SSet.pathHomotopyFiberToTotal f b = F.ι ≫ SSet.mappingPathRetract f) ∧
      (e.inv ≫ SSet.pathHomotopyFiberPath f b = F.ι ≫ SSet.mappingPathEval f) ∧
      (e.hom ≫ e.inv = 𝟙 (SSet.pathHomotopyFiber f b)) ∧
      (e.inv ≫ e.hom = 𝟙 (F : SSet.{0})) := by
  let e := SSet.pathHomotopyFiberStrictMappingPathIso f b
  exact ⟨SSet.pathHomotopyFiberStrictMappingPathIso_hom_total f b,
    SSet.pathHomotopyFiberStrictMappingPathIso_hom_path f b,
    SSet.pathHomotopyFiberStrictMappingPathIso_inv_total f b,
    SSet.pathHomotopyFiberStrictMappingPathIso_inv_path f b,
    e.hom_inv_id, e.inv_hom_id⟩

-- The entire six-equation contract at carrier universe 1.
example {X B : SSet.{1}} (f : X ⟶ B) (b : B _⦋0⦌) :
    let e := SSet.pathHomotopyFiberStrictMappingPathIso f b
    let F := SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b
    (e.hom ≫ (F.ι ≫ SSet.mappingPathRetract f) = SSet.pathHomotopyFiberToTotal f b) ∧
      (e.hom ≫ (F.ι ≫ SSet.mappingPathEval f) = SSet.pathHomotopyFiberPath f b) ∧
      (e.inv ≫ SSet.pathHomotopyFiberToTotal f b = F.ι ≫ SSet.mappingPathRetract f) ∧
      (e.inv ≫ SSet.pathHomotopyFiberPath f b = F.ι ≫ SSet.mappingPathEval f) ∧
      (e.hom ≫ e.inv = 𝟙 (SSet.pathHomotopyFiber f b)) ∧
      (e.inv ≫ e.hom = 𝟙 (F : SSet.{1})) := by
  let e := SSet.pathHomotopyFiberStrictMappingPathIso f b
  exact ⟨SSet.pathHomotopyFiberStrictMappingPathIso_hom_total f b,
    SSet.pathHomotopyFiberStrictMappingPathIso_hom_path f b,
    SSet.pathHomotopyFiberStrictMappingPathIso_inv_total f b,
    SSet.pathHomotopyFiberStrictMappingPathIso_inv_path f b,
    e.hom_inv_id, e.inv_hom_id⟩

-- The entire six-equation contract at carrier universe 2.
example {X B : SSet.{2}} (f : X ⟶ B) (b : B _⦋0⦌) :
    let e := SSet.pathHomotopyFiberStrictMappingPathIso f b
    let F := SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b
    (e.hom ≫ (F.ι ≫ SSet.mappingPathRetract f) = SSet.pathHomotopyFiberToTotal f b) ∧
      (e.hom ≫ (F.ι ≫ SSet.mappingPathEval f) = SSet.pathHomotopyFiberPath f b) ∧
      (e.inv ≫ SSet.pathHomotopyFiberToTotal f b = F.ι ≫ SSet.mappingPathRetract f) ∧
      (e.inv ≫ SSet.pathHomotopyFiberPath f b = F.ι ≫ SSet.mappingPathEval f) ∧
      (e.hom ≫ e.inv = 𝟙 (SSet.pathHomotopyFiber f b)) ∧
      (e.inv ≫ e.hom = 𝟙 (F : SSet.{2})) := by
  let e := SSet.pathHomotopyFiberStrictMappingPathIso f b
  exact ⟨SSet.pathHomotopyFiberStrictMappingPathIso_hom_total f b,
    SSet.pathHomotopyFiberStrictMappingPathIso_hom_path f b,
    SSet.pathHomotopyFiberStrictMappingPathIso_inv_total f b,
    SSet.pathHomotopyFiberStrictMappingPathIso_inv_path f b,
    e.hom_inv_id, e.inv_hom_id⟩

end MappingPathFiberTests

end
