/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Limits.Shapes.CoreBiproductLeftTriangle

/-!
# Pentagon for core biproduct translation

The two forward-associator routes from translation by `(A ⊞ B) ⊞ D` to
successive translation by `D`, `B`, and `A` agree.  Objectwise, this is the
explicit biproduct pentagon

```text
  α(A ⊞ B, D, X) ≫ α(A, B, D ⊞ X)
    = (α(A, B, D) ⊞ 𝟙 X) ≫ α(A, B ⊞ D, X) ≫
        (𝟙 A ⊞ α(B, D, X)).
```

The component equality is proved by nested biproduct extensionality and the
defining projection equations of `biprod.associator` and `biprod.map`.  No
unnamed coherence tactic, zero-comma transport, or action bundling is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasBinaryBiproducts C]

/-- Explicit forward biproduct pentagon component. -/
theorem coreLeftBiprodBiprodIso_pentagon_component
    (A B D X : C) :
    (biprod.associator (A ⊞ B) D X).hom ≫
        (biprod.associator A B (D ⊞ X)).hom =
      biprod.map (biprod.associator A B D).hom (𝟙 X) ≫
        (biprod.associator A (B ⊞ D) X).hom ≫
        biprod.map (𝟙 A) (biprod.associator B D X).hom := by
  apply biprod.hom_ext
  · simp [biprod.associator, Category.assoc]
  · apply biprod.hom_ext
    · simp [biprod.associator, Category.assoc]
    · apply biprod.hom_ext <;>
        simp [biprod.associator, Category.assoc]

/-- Pentagon coherence for the multiplication isomorphisms of core
left-biproduct translation. -/
theorem coreLeftBiprodBiprodIso_pentagon (A B D : C) :
    coreLeftBiprodBiprodIso (A ⊞ B) D ≪≫
        Functor.isoWhiskerLeft (coreLeftBiprodFunctor D)
          (coreLeftBiprodBiprodIso A B) =
      coreLeftBiprodIsoOfIso (biprod.associator A B D) ≪≫
        coreLeftBiprodBiprodIso A (B ⊞ D) ≪≫
        Functor.isoWhiskerRight (coreLeftBiprodBiprodIso B D)
          (coreLeftBiprodFunctor A) ≪≫
        Functor.associator (coreLeftBiprodFunctor D)
          (coreLeftBiprodFunctor B) (coreLeftBiprodFunctor A) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply Core.hom_ext
  change
    (biprod.associator (A ⊞ B) D X.of).hom ≫
          (biprod.associator A B (D ⊞ X.of)).hom =
      biprod.map (biprod.associator A B D).hom (𝟙 X.of) ≫
          (biprod.associator A (B ⊞ D) X.of).hom ≫
          biprod.map (𝟙 A) (biprod.associator B D X.of).hom ≫ 𝟙 _
  rw [Category.comp_id]
  exact coreLeftBiprodBiprodIso_pentagon_component A B D X.of

end CategoryTheory.Limits

end
