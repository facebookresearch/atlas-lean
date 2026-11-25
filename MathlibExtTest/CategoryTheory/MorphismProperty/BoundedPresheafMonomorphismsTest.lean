/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.MorphismProperty.BoundedPresheafMonomorphisms
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Types.Monomorphisms

/-! # Literal shared bounded-Mono predicate clients

Both endpoint total-element bounds and the original Mono are retained.
The empty and nonmonic controls use actual original presheaves and maps.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.MorphismProperty.BoundedPresheafMonomorphismsTest

variable {E : Type u} [SmallCategory E]

/-- The shared predicate has exactly the original Mono and both literal endpoint bounds. -/
theorem originalPredicate {A B : Eᵒᵖ ⥤ Type u} (f : A ⟶ B) :
    boundedPresheafMonomorphisms E f ↔
      Mono f ∧
        Cardinal.mk A.Elements ≤ max Cardinal.aleph0 (Cardinal.mk (CategoryTheory.Arrow E)) ∧
        Cardinal.mk B.Elements ≤ max Cardinal.aleph0 (Cardinal.mk (CategoryTheory.Arrow E)) :=
  Iff.rfl

/-- The representative-family Arrow predicate is only the same canonical view. -/
theorem originalView (a : CategoryTheory.Arrow (Eᵒᵖ ⥤ Type u)) :
    Presheaf.boundedMonoArrows E a ↔ boundedPresheafMonomorphisms E a.hom := Iff.rfl

/-- The original G1 conversion consumes exactly the same proof without unfolding two formulas. -/
theorem exactCellView {A B : Eᵒᵖ ⥤ Type u} (f : A ⟶ B)
    (hf : boundedPresheafMonomorphisms E f) :
    Presheaf.boundedMonoArrows E (CategoryTheory.Arrow.mk f) := hf

/-- Actual empty presheaf values in the unchanged value universe. -/
abbrev emptyValues (E : Type u) [SmallCategory E] : Eᵒᵖ ⥤ Type u :=
  (Functor.const Eᵒᵖ).obj (ULift.{u} PEmpty)

/-- Empty endpoint values satisfy both original total-element bounds. -/
theorem emptyIdentity (E : Type u) [SmallCategory E] :
    boundedPresheafMonomorphisms E (𝟙 (emptyValues E)) := by
  let _ : IsEmpty (emptyValues E).Elements := ⟨fun x => PEmpty.elim x.val.down⟩
  exact ⟨inferInstance, by simp, by simp⟩

/-- The two-component source and one-component target on an actual singleton site. -/
def finiteFold :
    (Functor.const (Discrete PUnit)ᵒᵖ).obj (Fin 2) ⟶
      (Functor.const (Discrete PUnit)ᵒᵖ).obj PUnit :=
  (Functor.const (Discrete PUnit)ᵒᵖ).map (TypeCat.ofHom (fun _ : Fin 2 => PUnit.unit))

/-- The predicate does not forget the original monomorphism requirement. -/
theorem finiteFoldNotBounded :
    ¬ boundedPresheafMonomorphisms (Discrete PUnit) finiteFold := by
  intro h
  have hmono := (NatTrans.mono_iff_mono_app finiteFold).1 h.1
    (Opposite.op (Discrete.mk PUnit.unit))
  have bad : (0 : Fin 2) = 1 := (mono_iff_injective _).1 hmono (by rfl)
  exact (by decide : (0 : Fin 2) ≠ 1) bad

/-- The original empty site imposes no extra nonemptiness premise on the property/view equality. -/
theorem emptySite (a : CategoryTheory.Arrow ((Discrete PEmpty)ᵒᵖ ⥤ Type)) :
    Presheaf.boundedMonoArrows (Discrete PEmpty) a ↔
      boundedPresheafMonomorphisms (Discrete PEmpty) a.hom := Iff.rfl

/-- The same view works with a genuinely raised site and value universe. -/
theorem raisedView {F : Type (u + 1)} [SmallCategory F]
    (a : CategoryTheory.Arrow (Fᵒᵖ ⥤ Type (u + 1))) :
    Presheaf.boundedMonoArrows F a ↔ boundedPresheafMonomorphisms F a.hom := Iff.rfl

end CategoryTheory.MorphismProperty.BoundedPresheafMonomorphismsTest
