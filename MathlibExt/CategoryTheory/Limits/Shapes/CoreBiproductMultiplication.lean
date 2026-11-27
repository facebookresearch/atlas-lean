/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Limits.Shapes.CoreBiproductCoherence

/-!
# Parameter and multiplication coherence for core biproduct translation

An isomorphism between fixed left summands induces a natural isomorphism
between the corresponding translation functors on `Core C`.  Translation by
`A ⊞ B` is also naturally isomorphic to translation first by `B` and then by
`A`:

```text
  K (A ⊞ B) ≅ K B ⋙ K A.
```

The order is forced by functor composition.  At `X`, the comparison is the
forward biproduct associator from `(A ⊞ B) ⊞ X` to `A ⊞ (B ⊞ X)`.
Naturality uses `biprod.associator_natural` after explicitly identifying
`biprod.map (𝟙 A) (𝟙 B)` with `𝟙 (A ⊞ B)`.

No parameter-naturality law between these isomorphisms, triangle, pentagon,
or action structure is asserted here.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasBinaryBiproducts C]

/-- Isomorphic left summands give naturally isomorphic core left-biproduct
translation functors. -/
noncomputable def coreLeftBiprodIsoOfIso
    {A B : C} (e : A ≅ B) :
    coreLeftBiprodFunctor A ≅ coreLeftBiprodFunctor B :=
  NatIso.ofComponents
    (fun X => Core.isoMk (biprod.mapIso e (Iso.refl X.of)))
    (by
      intro X Y g
      apply Core.hom_ext
      change
        biprod.map (𝟙 A) g.iso.hom ≫
            biprod.map e.hom (𝟙 Y.of) =
          biprod.map e.hom (𝟙 X.of) ≫
            biprod.map (𝟙 B) g.iso.hom
      apply biprod.hom_ext <;> simp)

/-- Underlying map of a parameter-change component. -/
@[simp]
theorem coreLeftBiprodIsoOfIso_hom_app_iso_hom
    {A B : C} (e : A ≅ B) (X : Core C) :
    ((coreLeftBiprodIsoOfIso e).hom.app X).iso.hom =
      biprod.map e.hom (𝟙 X.of) :=
  rfl

/-- Translation by `A ⊞ B` is translation by `B` followed by translation by
`A`.  Components use the forward biproduct associator. -/
noncomputable def coreLeftBiprodBiprodIso (A B : C) :
    coreLeftBiprodFunctor (A ⊞ B) ≅
      coreLeftBiprodFunctor B ⋙ coreLeftBiprodFunctor A :=
  NatIso.ofComponents
    (fun X => Core.isoMk (biprod.associator A B X.of))
    (by
      intro X Y g
      apply Core.hom_ext
      change
        biprod.map (𝟙 (A ⊞ B)) g.iso.hom ≫
            (biprod.associator A B Y.of).hom =
          (biprod.associator A B X.of).hom ≫
            biprod.map (𝟙 A) (biprod.map (𝟙 B) g.iso.hom)
      have hId : biprod.map (𝟙 A) (𝟙 B) = 𝟙 (A ⊞ B) := by
        apply biprod.hom_ext <;> simp
      rw [← hId]
      exact biprod.associator_natural (𝟙 A) (𝟙 B) g.iso.hom)

/-- Underlying map of a multiplication component is the forward biproduct
associator. -/
@[simp]
theorem coreLeftBiprodBiprodIso_hom_app_iso_hom
    (A B : C) (X : Core C) :
    ((coreLeftBiprodBiprodIso A B).hom.app X).iso.hom =
      (biprod.associator A B X.of).hom :=
  rfl

end CategoryTheory.Limits

end
