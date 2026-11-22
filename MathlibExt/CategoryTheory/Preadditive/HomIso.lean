/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Algebra.Exact.Basic

/-!
# Additive comparison of represented Hom groups

The full original source and target isomorphisms transport both Hom
functions in any preadditive category. Generic represented exactness
ladders use the stock additive-equivalence
and commutative-square providers. No shift, triangle or model structure
is required.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory

namespace CategoryTheory.Preadditive.HomIsoExact

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The native full Hom isomorphism is additive in the original preadditive Hom groups. -/
def homIso {X X' Y Y' : C} (a : X ≅ X') (b : Y ≅ Y') : (X ⟶ Y) ≃+ (X' ⟶ Y') where
  toEquiv := Iso.homCongr a b
  map_add' f h := by
    change a.inv ≫ (f + h) ≫ b.hom = a.inv ≫ f ≫ b.hom + a.inv ≫ h ≫ b.hom
    rw [Preadditive.add_comp, Preadditive.comp_add]

/-- Both actual source and target comparison maps occur in the whole forward function. -/
theorem homIso_apply {X X' Y Y' : C} (a : X ≅ X') (b : Y ≅ Y') (f : X ⟶ Y) :
    homIso a b f = a.inv ≫ f ≫ b.hom := rfl

/-- The whole inverse function retains both original inverse comparison maps. -/
theorem homIso_symm_apply {X X' Y Y' : C} (a : X ≅ X') (b : Y ≅ Y') (f : X' ⟶ Y') :
    (homIso a b).symm f = a.hom ≫ f ≫ b.inv := rfl

/-- All three original source isomorphisms transport the exact represented
row with every map retained. -/
theorem represented_source_iso {A A' B B' D D' : C}
    (p : A ⟶ B) (q : B ⟶ D) (p' : A' ⟶ B') (q' : B' ⟶ D')
    (eA : A ≅ A') (eB : B ≅ B') (eD : D ≅ D')
    (hp : p ≫ eB.hom = eA.hom ≫ p') (hq : q ≫ eD.hom = eB.hom ≫ q') (E : C) :
    Function.Exact (Preadditive.leftComp E q') (Preadditive.leftComp E p') ↔
      Function.Exact (Preadditive.leftComp E q) (Preadditive.leftComp E p) := by
  apply Function.Exact.iff_of_ladder_addEquiv
    (homIso eD (Iso.refl E)) (homIso eB (Iso.refl E)) (homIso eA (Iso.refl E))
  · ext f
    change Preadditive.leftComp E q' (homIso eD (Iso.refl E) f) =
      homIso eB (Iso.refl E) (Preadditive.leftComp E q f)
    simp only [Preadditive.leftComp, AddMonoidHom.mk'_apply, homIso_apply,
      Iso.refl_hom, Category.comp_id]
    simpa only [Category.assoc] using
      congrArg (fun m : B' ⟶ D => m ≫ f)
        ((CommSq.vert_inv (show CommSq q eB.hom eD.hom q' from ⟨hq⟩)).w)
  · ext f
    change Preadditive.leftComp E p' (homIso eB (Iso.refl E) f) =
      homIso eA (Iso.refl E) (Preadditive.leftComp E p f)
    simp only [Preadditive.leftComp, AddMonoidHom.mk'_apply, homIso_apply,
      Iso.refl_hom, Category.comp_id]
    simpa only [Category.assoc] using
      congrArg (fun m : A' ⟶ B => m ≫ f)
        ((CommSq.vert_inv (show CommSq p eA.hom eB.hom p' from ⟨hp⟩)).w)

end CategoryTheory.Preadditive.HomIsoExact
