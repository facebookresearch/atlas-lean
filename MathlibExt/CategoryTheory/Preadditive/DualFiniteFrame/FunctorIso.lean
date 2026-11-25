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
# Canonical finite-frame dual comparison under actual functor isomorphisms

The original unit component determines compatibility with an earned natural
isomorphism of additive functors. The comparison retains direct generator values.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u₁ u₂ v₁ v₂ w
namespace CategoryTheory.DualFiniteFrame

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]

/-- The canonical finite-frame dual comparison respects every earned functor
isomorphism whose original unit component is compatible. -/
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
