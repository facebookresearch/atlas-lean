/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.PowersetVerification
public import MathlibExt.CategoryTheory.Monoidal.VerificationFunctor

/-! # Consumers of abstract verification-functor rules -/

@[expose] public section
open CategoryTheory MonoidalCategory
open scoped MonoidalCategory
open CategoryTheory.VerificationFunctor
universe u v w

section Generic
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  (F : C ⥤ MonRelCat.{w}) [F.Monoidal] (T : SymmetricTrace C)
  (hF : T.Preserves MonRelCat.symmetricTrace F)
  {X Y Z U : C}

example (f : X ⟶ Y) (g : Y ⟶ Z) (P : F.obj X) (R : F.obj Z) :
    Triple F (f ≫ g) P R ↔ ∃ Q, Triple F f P Q ∧ Triple F g Q R :=
  triple_comp_iff F f g P R

example (f : X ⊗ U ⟶ Y ⊗ U) (P : F.obj X) (Q : F.obj Y) :
    Triple F (T.trace f) P Q ↔ ∃ I : F.obj U, TensorTriple F f (P, I) (Q, I) :=
  triple_trace_iff F hF f P Q

example (P Q : F.obj X) (h : P ≤ Q) : Triple F (𝟙 X) P Q :=
  (triple_id_iff F P Q).mpr h
end Generic

/-- Distinct assertions can be equivalent in a preorder. -/
private def indiscrete : MonRelCat where
  carrier := Bool
  str := { le := fun _ _ => True
           lt := fun _ _ => False
           lt_iff_le_not_ge := by intros; simp
           le_refl := fun _ => trivial
           le_trans := fun _ _ _ _ _ => trivial }

example : Triple (𝟭 MonRelCat) (𝟙 indiscrete) false true :=
  (triple_id_iff _ _ _).mpr trivial

example : ¬ Triple (𝟭 MonRelCat) (𝟙 (MonRelCat.of ℕ)) (2 : ℕ) (1 : ℕ) := by
  simp [triple_id_iff]

-- Powerset comparisons genuinely change the carrier: sets of sums versus pairs of sets.
example {X Y U V : SumRelCat} (f : X ⟶ Y) (g : U ⟶ V)
    (P : Set X) (Q : Set Y) (I : Set U) (J : Set V) :
    TensorTriple PowersetVerification.verification (f ⊗ₘ g) (P, I) (Q, J) ↔
      f.rel.image P ⊆ Q ∧ g.rel.image I ⊆ J :=
  tensorTriple_tensor_iff PowersetVerification.verification f g P I Q J

example {X Y U : SumRelCat} (f : X ⊗ U ⟶ Y ⊗ U) (P : Set X) (Q : Set Y) :
    Triple PowersetVerification.verification (SumRelCat.symmetricTrace.trace f) P Q ↔
      ∃ I : Set U, TensorTriple PowersetVerification.verification f (P, I) (Q, I) :=
  triple_trace_iff _ PowersetVerification.preserves_trace f P Q

-- Empty state spaces still have a powerset assertion; do not confuse the two kinds of emptiness.
example (P Q : Set ℕ) :
    Triple PowersetVerification.verification
      (SumRelCat.symmetricTrace.trace
        (𝟙 (SumRelCat.of ℕ ⊗ SumRelCat.of Empty))) P Q ↔ P ⊆ Q := by
  change (SumRelCat.feedback _).rel.image P ⊆ Q ↔ _
  have h : SumRelCat.feedback (𝟙 (SumRelCat.of ℕ ⊗ SumRelCat.of Empty)) =
      𝟙 (SumRelCat.of ℕ) := by
    apply SumRelCat.Hom.ext
    ext ⟨x, y⟩
    constructor
    · intro hp
      cases hp with
      | output h => exact Sum.inl.inj h
      | step h _ => cases h
    · intro h
      exact .output (congrArg Sum.inl h)
  rw [h]
  simp
