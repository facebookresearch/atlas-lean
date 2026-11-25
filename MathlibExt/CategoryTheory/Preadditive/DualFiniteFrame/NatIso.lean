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
# Actual natural comparisons and finite-frame evaluation

An already earned natural dual comparison with the original unit-evaluation
value agrees with canonical finite-frame comparison. This applies to genuine
open restriction without assuming an arbitrary pullback comparison.
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
/-- Naturality and the earned unit evaluation give the actual value on every
pulled original unit-source morphism. -/
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


/-- The actual natural comparison with the original unit value equals the
canonical direct comparison on every earned finite frame. -/
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
