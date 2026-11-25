/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.Monoidal
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# The monoid axiom

This file packages the monoid axiom for a selected model structure and
symmetric monoidal tensor. The generating property consists literally of
right tensors of selected trivial cofibrations by arbitrary objects.
-/

@[expose] public section

set_option autoImplicit false

universe w v u

open CategoryTheory MonoidalCategory
open CategoryTheory.MorphismProperty
open scoped MonoidalCategory

namespace HomotopicalAlgebra

variable (C : Type u) [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C]

/-- Right tensors of selected trivial cofibrations by arbitrary objects. -/
def tensorTrivialCofibrationsRight : MorphismProperty C :=
  .ofHoms (fun q : (trivialCofibrations C).toSet × C =>
    q.1.1.hom ▷ q.2)

/-- A right tensor of a selected trivial cofibration is one of the literal
generators in `tensorTrivialCofibrationsRight`. -/
theorem whiskerRight_mem_tensorTrivialCofibrationsRight
    {A B : C} (f : A ⟶ B) (hf : trivialCofibrations C f) (X : C) :
    tensorTrivialCofibrationsRight C (f ▷ X) := by
  unfold tensorTrivialCofibrationsRight
  let q : (trivialCofibrations C).toSet × C :=
    ⟨⟨Arrow.mk f, hf⟩, X⟩
  exact MorphismProperty.ofHoms.mk q

/-- Membership in `tensorTrivialCofibrationsRight` means equality, as a
bundled arrow, to a right tensor of a selected trivial cofibration. -/
theorem mem_tensorTrivialCofibrationsRight_iff
    {A B : C} (g : A ⟶ B) :
    tensorTrivialCofibrationsRight C g ↔
      ∃ (X Y : C) (f : X ⟶ Y), trivialCofibrations C f ∧
        ∃ Z : C, Arrow.mk g = Arrow.mk (f ▷ Z) := by
  unfold tensorTrivialCofibrationsRight
  rw [MorphismProperty.ofHoms_iff]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q.1.1.left, q.1.1.right, q.1.1.hom, q.1.2, q.2, hq⟩
  · rintro ⟨X, Y, f, hf, Z, hg⟩
    exact ⟨⟨⟨Arrow.mk f, hf⟩, Z⟩, hg⟩

/-- To prove that every right-tensor generator lies in a morphism property,
it suffices to check each selected trivial cofibration and tensor factor. -/
theorem tensorTrivialCofibrationsRight_le_iff
    (P : MorphismProperty C) :
    tensorTrivialCofibrationsRight C ≤ P ↔
      ∀ {A B : C} (f : A ⟶ B), trivialCofibrations C f →
        ∀ X : C, P (f ▷ X) := by
  constructor
  · intro h A B f hf X
    exact h _ (whiskerRight_mem_tensorTrivialCofibrationsRight C f hf X)
  · intro h A B g hg
    rw [mem_tensorTrivialCofibrationsRight_iff] at hg
    obtain ⟨X, Y, f, hf, Z, hgf⟩ := hg
    rw [← P.arrow_mk_mem_toSet_iff, hgf, P.arrow_mk_mem_toSet_iff]
    exact h f hf Z

/-- The cellular closure of tensors of trivial cofibrations consists of weak
equivalences.  In a symmetric monoidal category the right-tensor formulation
also supplies the left-tensor formulation. -/
class MonoidAxiom [SymmetricCategory C] : Prop where
  cellularClosure_le_weakEquivalences :
    transfiniteCompositions.{w}
      (coproducts.{w} (tensorTrivialCofibrationsRight C)).pushouts ≤
        weakEquivalences C

end HomotopicalAlgebra
