/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.CategoryTheory.Preadditive.DualFiniteFrame.Naturality

/-!
# Natural dual comparisons and finite-frame evaluation

For functors F:C → D, G:Cᵒᵖ → C and H:Dᵒᵖ → D, a natural isomorphism
η:F∘G ≅ H∘Fᵒᵖ compatible with chosen evaluations at distinguished
objects U and V determines its evaluation on every map U → A.

In preadditive categories, when these functors are additive and a finite
biproduct frame of copies of U is given, this normalized natural comparison
equals the canonical finite-frame comparison. The category object and
morphism universes and finite-index universe are independent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u₁ u₂ v₁ v₂ w
namespace CategoryTheory.DualFiniteFrame

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]

omit [Preadditive C] [Preadditive D] in
/-- Let F:C → D, G:Cᵒᵖ → C and H:Dᵒᵖ → D be functors, η:F∘G ≅ H∘Fᵒᵖ,
and u:F(U) ≅ V, e_G:G(U) ≅ U, e_H:H(V) ≅ V.
Assume u∘F(e_G)=e_H∘H((u⁻¹)ᵒᵖ)∘η_U.
For every v:U → A, evaluation after η_A satisfies
e_H∘H((F(v)∘u⁻¹)ᵒᵖ)∘η_A
=u∘F(e_G∘G(vᵒᵖ)). -/
theorem naturalDualComparison_unitHom (F : C ⥤ D)
    (G : Cᵒᵖ ⥤ C) (H : Dᵒᵖ ⥤ D)
    (η : G ⋙ F ≅ F.op ⋙ H) (U : C) (V : D)
    (u : F.obj U ≅ V) (eG : G.obj (op U) ≅ U) (eH : H.obj (op V) ≅ V)
    (hu : F.map eG.hom ≫ u.hom =
      η.hom.app (op U) ≫ H.map u.inv.op ≫ eH.hom)
    {A : C} (v : U ⟶ A) :
    η.hom.app (op A) ≫ (H.map (u.inv ≫ F.map v).op ≫ eH.hom) =
      F.map (G.map v.op ≫ eG.hom) ≫ u.hom := by
  have hn := η.hom.naturality v.op
  change F.map (G.map v.op) ≫ η.hom.app (op U) =
      η.hom.app (op A) ≫ H.map (F.map v).op at hn
  rw [op_comp, H.map_comp]
  calc
    _ = (η.hom.app (op A) ≫ H.map (F.map v).op) ≫ (H.map u.inv.op ≫ eH.hom) := by
      simp only [Category.assoc]
    _ = (F.map (G.map v.op) ≫ η.hom.app (op U)) ≫ (H.map u.inv.op ≫ eH.hom) :=
      congrArg (fun z => z ≫ (H.map u.inv.op ≫ eH.hom)) hn.symm
    _ = F.map (G.map v.op) ≫ (η.hom.app (op U) ≫ H.map u.inv.op ≫ eH.hom) := by
      simp only [Category.assoc]
    _ = F.map (G.map v.op) ≫ (F.map eG.hom ≫ u.hom) :=
      congrArg (fun z => F.map (G.map v.op) ≫ z) hu.symm
    _ = _ := by rw [F.map_comp, Category.assoc]


/-- Let C,D be preadditive categories, F:C → D additive, and
G:Cᵒᵖ → C, H:Dᵒᵖ → D additive. Fix objects U,V and isomorphisms
u:F(U) ≅ V, e_G:G(U) ≅ U and e_H:H(V) ≅ V.
Let η:F∘G ≅ H∘Fᵒᵖ satisfy
u∘F(e_G)=e_H∘H((u⁻¹)ᵒᵖ)∘η_U.
For finite I, choose I-fold biproducts of U and V, and a bilimit bicone
b of copies of U. Its canonical finite-frame comparison
F(G(b.pt)) ≅ H(F(b.pt)) has forward map η_{b.pt}. -/
theorem finiteFrameDualComparisonIso_eq_natIso (F : C ⥤ D) [F.Additive]
    (G : Cᵒᵖ ⥤ C) [G.Additive] (H : Dᵒᵖ ⥤ D) [H.Additive]
    (η : G ⋙ F ≅ F.op ⋙ H) (I : Type w) [Fintype I]
    (U : C) [HasBiproduct (fun _ : I => U)]
    (V : D) [HasBiproduct (fun _ : I => V)]
    (u : F.obj U ≅ V) (eG : G.obj (op U) ≅ U) (eH : H.obj (op V) ≅ V)
    (hu : F.map eG.hom ≫ u.hom =
      η.hom.app (op U) ≫ H.map u.inv.op ≫ eH.hom)
    (b : Bicone (fun _ : I => U)) (hb : b.IsBilimit) :
    (finiteFrameDualComparisonIso F G H I U V u eG eH b hb).hom = η.hom.app (op b.pt) := by
  apply finiteFrameDualComparison_hom_ext F H I U V u eH b hb
  intro i
  exact (finiteFrameDualComparisonIso_generator F G H I U V u eG eH b hb i).trans
    (naturalDualComparison_unitHom F G H η U V u eG eH hu (b.ι i)).symm

end CategoryTheory.DualFiniteFrame
