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
# Finite-frame comparisons under natural isomorphisms of functors

Let C,D be preadditive, F,F' : C ⥤ D additive and η : F ≅ F' a natural isomorphism. Fix
additive contravariant endofunctors G,H and coefficient objects U,V with u : F(U) ≅ V, u' :
F'(U) ≅ V and evaluations G(U) ≅ U, H(V) ≅ V. Assume η.hom_U ≫ u'.hom = u.hom.

For every finite bilimit frame b of copies of U, the canonical comparisons satisfy
η.hom_{G(b.pt)} ≫ χ_{F'}.hom = χ_F.hom ≫ H((η.inv_{b.pt}).op). The inverse component inside H
has the direction required by contravariance. The category worlds and indexing universe remain
independent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u₁ u₂ v₁ v₂ w
namespace CategoryTheory.DualFiniteFrame

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]

/-- Naturality of finite-frame comparisons under a functor isomorphism.

Let η : F ≅ F' be a natural isomorphism of additive functors between preadditive categories
and let G,H be additive contravariant endofunctors. For a finite coefficient frame b, suppose
η.hom_U ≫ u'.hom = u.hom for the chosen coefficient identifications and retain the evaluations
G(U) ≅ U, H(V) ≅ V. Then η.hom_{G(b.pt)} ≫ χ_{F'}.hom = χ_F.hom ≫ H((η.inv_{b.pt}).op), where
χ_F and χ_{F'} are the corresponding finite-frame comparisons. -/
theorem finiteFrameDualComparisonIso_functorIso (F F' : C ⥤ D) [F.Additive] [F'.Additive]
    (η : F ≅ F') (G : Cᵒᵖ ⥤ C) [G.Additive] (H : Dᵒᵖ ⥤ D) [H.Additive]
    (I : Type w) [Fintype I]
    (U : C) [HasBiproduct (fun _ : I => U)]
    (V : D) [HasBiproduct (fun _ : I => V)]
    (u : F.obj U ≅ V) (u' : F'.obj U ≅ V)
    (eG : G.obj (op U) ≅ U) (eH : H.obj (op V) ≅ V)
    (hu : η.hom.app U ≫ u'.hom = u.hom)
    (b : Bicone (fun _ : I => U)) (hb : b.IsBilimit) :
    η.hom.app (G.obj (op b.pt)) ≫
        (finiteFrameDualComparisonIso F' G H I U V u' eG eH b hb).hom =
      (finiteFrameDualComparisonIso F G H I U V u eG eH b hb).hom ≫
        H.map (η.inv.app b.pt).op := by
  apply finiteFrameDualComparison_hom_ext F' H I U V u' eH b hb
  intro i
  let A := finiteFrameDualComparisonIso F G H I U V u eG eH b hb
  let B := finiteFrameDualComparisonIso F' G H I U V u' eG eH b hb
  have he : η.app U ≪≫ u' = u := by
    apply Iso.ext
    exact hu
  have hi : u'.inv ≫ η.inv.app U = u.inv := congrArg Iso.inv he
  have hv : (u'.inv ≫ F'.map (b.ι i)) ≫ η.inv.app b.pt = u.inv ≫ F.map (b.ι i) := by
    rw [Category.assoc, η.inv.naturality, ← Category.assoc, hi]
  have hleft : (η.hom.app (G.obj (op b.pt)) ≫ B.hom) ≫
      (H.map (u'.inv ≫ F'.map (b.ι i)).op ≫ eH.hom) =
      F.map (G.map (b.ι i).op ≫ eG.hom) ≫ u.hom := by
    rw [Category.assoc, finiteFrameDualComparisonIso_generator]
    rw [← Category.assoc, ← η.hom.naturality]
    rw [Category.assoc, hu]
  have hright : (A.hom ≫ H.map (η.inv.app b.pt).op) ≫
      (H.map (u'.inv ≫ F'.map (b.ι i)).op ≫ eH.hom) =
      F.map (G.map (b.ι i).op ≫ eG.hom) ≫ u.hom := by
    rw [Category.assoc, ← Category.assoc (H.map _), ← H.map_comp, ← op_comp, hv]
    exact finiteFrameDualComparisonIso_generator F G H I U V u eG eH b hb i
  exact hleft.trans hright.symm

end CategoryTheory.DualFiniteFrame
