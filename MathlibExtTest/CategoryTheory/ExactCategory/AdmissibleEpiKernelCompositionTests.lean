/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.ExactCategory.AdmissibleEpiKernelComposition

/-!
# Tests for admissible-epi kernel composition

These tests deliberately assume only the exact-category interface used by the
source.  In particular they do not assume a balanced or abelian category and
do not install global pullback, kernel, cokernel, or exactness instances.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Preadditive ZeroObject

universe v u

namespace CategoryTheory.ExactCategory

open AdmissibleEpiKernelPresentation

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

example {A B : C} {p : A ⟶ B} (hp : IsAdmissibleEpi p) :
    Nonempty (AdmissibleEpiKernelPresentation p) :=
  AdmissibleEpiKernelPresentation.nonempty hp

example {A B Z : C} {p : A ⟶ B}
    (P : AdmissibleEpiKernelPresentation p) (g : Z ⟶ B) :
    Nonempty (P.BaseChange g) :=
  P.baseChange_nonempty g

example {A B Z : C} {p : A ⟶ B}
    (P : AdmissibleEpiKernelPresentation p) (g : Z ⟶ B) :
    IsAdmissibleExact
      (ShortComplex.mk (P.baseChange g).kernelPresentation.ι
        (P.baseChange g).fst (P.baseChange g).kernelPresentation.zero) := by
  exact (P.baseChange g).kernelPresentation.exact

example {A B D : C} {p : A ⟶ B} {q : B ⟶ D}
    (P : AdmissibleEpiKernelPresentation p)
    (Q : AdmissibleEpiKernelPresentation q) :
    IsAdmissibleExact (compositeKernelSequence P Q) :=
  compositeKernelSequence_exact P Q

example {A B D : C} {p : A ⟶ B} {q : B ⟶ D}
    (P : AdmissibleEpiKernelPresentation p)
    (Q : AdmissibleEpiKernelPresentation q) :
    AdmissibleEpiKernelPresentation (p ≫ q) :=
  P.composite Q

example {A B D : C} {p : A ⟶ B} {q : B ⟶ D}
    (P : AdmissibleEpiKernelPresentation p)
    (Q : AdmissibleEpiKernelPresentation q) :
    (compositeKernelSequence P Q).f =
        (compositeBaseChange P Q).kernelLift ∧
      (compositeKernelSequence P Q).g =
        (compositeBaseChange P Q).fst := by
  exact ⟨compositeKernelSequence_f P Q, compositeKernelSequence_g P Q⟩

/-- Split admissible epis use their evident kernel presentation. -/
example (X Y : C) :
    AdmissibleEpiKernelPresentation
      (biprod.snd : X ⊞ Y ⟶ Y) :=
  { kernel := X
    ι := biprod.inl
    zero := by simp
    exact := isAdmissibleExact_split X Y }

/-- A split epi followed by an identity has the expected admissible kernel
row. -/
example (X Y : C) :
    let P : AdmissibleEpiKernelPresentation
        (biprod.snd : X ⊞ Y ⟶ Y) :=
      { kernel := X
        ι := biprod.inl
        zero := by simp
        exact := isAdmissibleExact_split X Y }
    let Q := (AdmissibleEpiKernelPresentation.nonempty
      (IsAdmissibleEpi.id Y)).some
    IsAdmissibleExact (compositeKernelSequence P Q) := by
  dsimp only
  exact compositeKernelSequence_exact _ _

/-- Identity on the source side of an arbitrary admissible epi. -/
example {A D : C} {q : A ⟶ D}
    (Q : AdmissibleEpiKernelPresentation q) :
    let P := (AdmissibleEpiKernelPresentation.nonempty
      (IsAdmissibleEpi.id A)).some
    IsAdmissibleExact (compositeKernelSequence P Q) := by
  dsimp only
  exact compositeKernelSequence_exact _ _

/-- Identity on the target side of an arbitrary admissible epi. -/
example {A B : C} {p : A ⟶ B}
    (P : AdmissibleEpiKernelPresentation p) :
    let Q := (AdmissibleEpiKernelPresentation.nonempty
      (IsAdmissibleEpi.id B)).some
    IsAdmissibleExact (compositeKernelSequence P Q) := by
  dsimp only
  exact compositeKernelSequence_exact _ _

/-- The construction applies at the zero object without a special case. -/
example :
    let P := (AdmissibleEpiKernelPresentation.nonempty
      (IsAdmissibleEpi.id (0 : C))).some
    let Q := (AdmissibleEpiKernelPresentation.nonempty
      (IsAdmissibleEpi.id (0 : C))).some
    IsAdmissibleExact (compositeKernelSequence P Q) := by
  dsimp only
  exact compositeKernelSequence_exact _ _

section TypeZero

variable {C₀ : Type} [Category C₀] [Preadditive C₀]
  [HasZeroObject C₀] [HasBinaryBiproducts C₀] [ExactCategory C₀]

example {A B D : C₀} {p : A ⟶ B} {q : B ⟶ D}
    (P : AdmissibleEpiKernelPresentation p)
    (Q : AdmissibleEpiKernelPresentation q) :
    IsAdmissibleExact (compositeKernelSequence P Q) :=
  compositeKernelSequence_exact P Q

end TypeZero

section TypeOne

variable {C₁ : Type 1} [Category.{1} C₁] [Preadditive C₁]
  [HasZeroObject C₁] [HasBinaryBiproducts C₁] [ExactCategory C₁]

example {A B D : C₁} {p : A ⟶ B} {q : B ⟶ D}
    (P : AdmissibleEpiKernelPresentation p)
    (Q : AdmissibleEpiKernelPresentation q) :
    IsAdmissibleExact (compositeKernelSequence P Q) :=
  compositeKernelSequence_exact P Q

end TypeOne

end CategoryTheory.ExactCategory

end
