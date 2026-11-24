/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

import Mathlib.CategoryTheory.Adjunction.Parametrized
import MathlibExt.CategoryTheory.Adjunction.RightIsoComparison

/-!
# Left comparisons of original parametrized adjunctions

A natural comparison of the right bifunctors gives actual comparisons of
the two original left adjoints. Their entire parameter naturality follows
from the original Hom equivalences and both parametrized adjunction laws.
-/

set_option autoImplicit false
noncomputable section

universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory Opposite

namespace CategoryTheory.ParametrizedAdjunction.LeftIsoComparison

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  {F L : C₁ ⥤ C₂ ⥤ C₃} {G R : C₁ᵒᵖ ⥤ C₃ ⥤ C₂}

/-- The actual component comparison is constructed from both original adjunctions and the
original right Iso. -/
def component (a : F ⊣₂ G) (b : L ⊣₂ R) (e : G ≅ R) (A : C₁) : F.obj A ≅ L.obj A :=
  Adjunction.RightIsoComparison.comparison (a.adj A) (b.adj A) (e.app (op A))

/-- Every original parameter arrow preserves the whole original left-adjoint comparison. -/
@[reassoc]
theorem component_naturality (a : F ⊣₂ G) (b : L ⊣₂ R) (e : G ≅ R)
    {A B : C₁} (p : A ⟶ B) :
    F.map p ≫ (component a b e B).hom = (component a b e A).hom ≫ L.map p := by
  apply NatTrans.ext
  funext X
  change (F.map p).app X ≫ (component a b e B).hom.app X =
    (component a b e A).hom.app X ≫ (L.map p).app X
  let Y := (L.obj B).obj X
  apply ((a.adj A).homEquiv X Y).injective
  apply (cancel_mono ((e.app (op A)).hom.app Y)).1
  have ha : (a.adj A).homEquiv X Y ((F.map p).app X ≫ (component a b e B).hom.app X) =
      (a.adj B).homEquiv X Y ((component a b e B).hom.app X) ≫ (G.map p.op).app Y :=
    a.homEquiv_naturality_one p ((component a b e B).hom.app X)
  have he := congrArg (fun t ↦ t.app Y) (e.hom.naturality p.op)
  change (G.map p.op).app Y ≫ (e.app (op A)).hom.app Y =
    (e.app (op B)).hom.app Y ≫ (R.map p.op).app Y at he
  have hB : (a.adj B).homEquiv X Y ((component a b e B).hom.app X) ≫
      (e.app (op B)).hom.app Y = (b.adj B).homEquiv X Y (𝟙 Y) := by
    have h := Adjunction.RightIsoComparison.forward (a.adj B) (b.adj B) (e.app (op B)) X Y (𝟙 Y)
    change (a.adj B).homEquiv X Y ((component a b e B).hom.app X ≫ 𝟙 Y) ≫
      (e.app (op B)).hom.app Y = (b.adj B).homEquiv X Y (𝟙 Y) at h
    exact (congrArg (fun q ↦ (a.adj B).homEquiv X Y q ≫ (e.app (op B)).hom.app Y)
      (Category.comp_id ((component a b e B).hom.app X))).symm.trans h
  have hb := b.homEquiv_naturality_one (X₂ := X) (X₃ := Y) p (𝟙 Y)
  change (b.adj A).homEquiv X Y ((L.map p).app X ≫ 𝟙 Y) =
    (b.adj B).homEquiv X Y (𝟙 Y) ≫ (R.map p.op).app Y at hb
  have hb' : (b.adj A).homEquiv X Y ((L.map p).app X) =
      (b.adj B).homEquiv X Y (𝟙 Y) ≫ (R.map p.op).app Y :=
    (congrArg ((b.adj A).homEquiv X Y) (Category.comp_id ((L.map p).app X))).symm.trans hb
  calc
    _ = ((a.adj B).homEquiv X Y ((component a b e B).hom.app X) ≫ (G.map p.op).app Y) ≫
        (e.app (op A)).hom.app Y := by rw [ha]
    _ = (a.adj B).homEquiv X Y ((component a b e B).hom.app X) ≫
        ((e.app (op B)).hom.app Y ≫ (R.map p.op).app Y) := by
      rw [Category.assoc, he]
    _ = (b.adj B).homEquiv X Y (𝟙 Y) ≫ (R.map p.op).app Y := by
      rw [← Category.assoc, hB]
    _ = (b.adj A).homEquiv X Y ((L.map p).app X) := by
      exact hb'.symm
    _ = _ :=
      (Adjunction.RightIsoComparison.forward (a.adj A) (b.adj A) (e.app (op A)) X Y
        ((L.map p).app X)).symm

/-- The original component comparisons give a natural Iso of the entire left bifunctors. -/
def iso (a : F ⊣₂ G) (b : L ⊣₂ R) (e : G ≅ R) : F ≅ L :=
  NatIso.ofComponents (fun A ↦ component a b e A) (fun p ↦ component_naturality a b e p)

/-- Every component remains the original right-Iso transport and original left-adjoint
uniqueness choice. -/
theorem iso_app (a : F ⊣₂ G) (b : L ⊣₂ R) (e : G ≅ R) (A : C₁) :
    (iso a b e).app A = Adjunction.RightIsoComparison.comparison (a.adj A) (b.adj A) (e.app
      (op A)) := rfl

end CategoryTheory.ParametrizedAdjunction.LeftIsoComparison
