/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyPushout

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.HomotopyPushoutTests

variable {C : Type u} [Category.{v} C] [ModelCategory C]
variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]

section Core

variable (D : WalkingSpan ⥤ C)

example : C := (homotopyPushout (C := C)).obj D

example : (homotopyPushout (C := C)).obj D ⟶ colimit D :=
  (homotopyPushoutComparison (C := C)).app D

example :
    (homotopyPushout (C := C)).map (𝟙 D) =
      𝟙 ((homotopyPushout (C := C)).obj D) :=
  (homotopyPushout (C := C)).map_id D

variable {E F : WalkingSpan ⥤ C}

example (f : D ⟶ E) (g : E ⟶ F) :
    (homotopyPushout (C := C)).map (f ≫ g) =
      (homotopyPushout (C := C)).map f ≫
        (homotopyPushout (C := C)).map g :=
  (homotopyPushout (C := C)).map_comp f g

example (f : D ⟶ E) :
    (homotopyPushout (C := C)).map f ≫
        (homotopyPushoutComparison (C := C)).app E =
      (homotopyPushoutComparison (C := C)).app D ≫ colim.map f :=
  (homotopyPushoutComparison (C := C)).naturality f

end Core

section PointwiseWeak

variable {D E : WalkingSpan ⥤ C} (f : D ⟶ E)
variable (hzero : WeakEquivalence (f.app WalkingSpan.zero))
variable (hleft : WeakEquivalence (f.app WalkingSpan.left))
variable (hright : WeakEquivalence (f.app WalkingSpan.right))

example : WeakEquivalence ((homotopyPushout (C := C)).map f) := by
  apply homotopyPushout_map_weakEquivalence f
  rintro (_ | _ | _)
  · exact hzero
  · exact hleft
  · exact hright

example (D : WalkingSpan ⥤ C) :
    WeakEquivalence ((homotopyPushout (C := C)).map (𝟙 D)) := by
  apply homotopyPushout_map_weakEquivalence (𝟙 D)
  intro j
  change WeakEquivalence (𝟙 (D.obj j))
  infer_instance

end PointwiseWeak

section ComparisonCriteria

variable (D : WalkingSpan ⥤ C)

example [IsCofibrant (D.obj WalkingSpan.zero)]
    [IsCofibrant (D.obj WalkingSpan.right)]
    [Cofibration (D.map WalkingSpan.Hom.fst)] :
    WeakEquivalence ((homotopyPushoutComparison (C := C)).app D) :=
  weakEquivalence_homotopyPushoutComparison_of_fst D

example [IsCofibrant (D.obj WalkingSpan.zero)]
    [IsCofibrant (D.obj WalkingSpan.left)]
    [Cofibration (D.map WalkingSpan.Hom.snd)] :
    WeakEquivalence ((homotopyPushoutComparison (C := C)).app D) :=
  weakEquivalence_homotopyPushoutComparison_of_snd D

section LeftProper

variable [IsLeftProper C]

example [Cofibration (D.map WalkingSpan.Hom.fst)] :
    WeakEquivalence ((homotopyPushoutComparison (C := C)).app D) :=
  weakEquivalence_homotopyPushoutComparison_of_leftProper_fst D

example [Cofibration (D.map WalkingSpan.Hom.snd)] :
    WeakEquivalence ((homotopyPushoutComparison (C := C)).app D) :=
  weakEquivalence_homotopyPushoutComparison_of_leftProper_snd D

end LeftProper

end ComparisonCriteria

section IdentitySpans

variable {X Y : C}

private abbrev identitySpan (X : C) : WalkingSpan ⥤ C :=
  span (𝟙 X) (𝟙 X)

private abbrev leftIdentitySpan (f : X ⟶ Y) : WalkingSpan ⥤ C :=
  span (𝟙 X) f

private abbrev rightIdentitySpan (f : X ⟶ Y) : WalkingSpan ⥤ C :=
  span f (𝟙 X)

example [IsCofibrant X] :
    WeakEquivalence
      ((homotopyPushoutComparison (C := C)).app (identitySpan X)) := by
  let _ : IsCofibrant ((identitySpan X).obj WalkingSpan.zero) := by
    change IsCofibrant X
    infer_instance
  let _ : IsCofibrant ((identitySpan X).obj WalkingSpan.right) := by
    change IsCofibrant X
    infer_instance
  let _ : Cofibration ((identitySpan X).map WalkingSpan.Hom.fst) := by
    change Cofibration (𝟙 X)
    infer_instance
  exact weakEquivalence_homotopyPushoutComparison_of_fst (identitySpan X)

example (f : X ⟶ Y) [IsCofibrant X] [IsCofibrant Y] :
    WeakEquivalence
      ((homotopyPushoutComparison (C := C)).app (leftIdentitySpan f)) := by
  let _ : IsCofibrant ((leftIdentitySpan f).obj WalkingSpan.zero) := by
    change IsCofibrant X
    infer_instance
  let _ : IsCofibrant ((leftIdentitySpan f).obj WalkingSpan.right) := by
    change IsCofibrant Y
    infer_instance
  let _ : Cofibration ((leftIdentitySpan f).map WalkingSpan.Hom.fst) := by
    change Cofibration (𝟙 X)
    infer_instance
  exact weakEquivalence_homotopyPushoutComparison_of_fst (leftIdentitySpan f)

example (f : X ⟶ Y) [IsCofibrant X] [IsCofibrant Y] :
    WeakEquivalence
      ((homotopyPushoutComparison (C := C)).app (rightIdentitySpan f)) := by
  let _ : IsCofibrant ((rightIdentitySpan f).obj WalkingSpan.zero) := by
    change IsCofibrant X
    infer_instance
  let _ : IsCofibrant ((rightIdentitySpan f).obj WalkingSpan.left) := by
    change IsCofibrant Y
    infer_instance
  let _ : Cofibration ((rightIdentitySpan f).map WalkingSpan.Hom.snd) := by
    change Cofibration (𝟙 X)
    infer_instance
  exact weakEquivalence_homotopyPushoutComparison_of_snd (rightIdentitySpan f)

end IdentitySpans

section ArbitraryPacket

variable {D : WalkingSpan ⥤ C} (R : CofibrantSpanReplacement D)

example :
    ∃ f : R.pushoutObj ⟶ (homotopyPushout (C := C)).obj D,
      WeakEquivalence f ∧
        f ≫ (homotopyPushoutComparison (C := C)).app D = R.toPushout :=
  R.exists_weakEquivalence_to_homotopyPushout

example : True := by
  obtain ⟨f, hf, htriangle⟩ :=
    R.exists_weakEquivalence_to_homotopyPushout
  have _ : WeakEquivalence f := hf
  have _ : f ≫ (homotopyPushoutComparison (C := C)).app D =
      (R.toPushout : R.pushoutObj ⟶ colimit D) := htriangle
  trivial

example :
    WeakEquivalence ((homotopyPushoutComparison (C := C)).app D) ↔
      WeakEquivalence R.toPushout :=
  R.weakEquivalence_homotopyPushoutComparison_iff

example
    (h : WeakEquivalence ((homotopyPushoutComparison (C := C)).app D)) :
    WeakEquivalence R.toPushout :=
  R.weakEquivalence_homotopyPushoutComparison_iff.mp h

example (h : WeakEquivalence R.toPushout) :
    WeakEquivalence ((homotopyPushoutComparison (C := C)).app D) :=
  R.weakEquivalence_homotopyPushoutComparison_iff.mpr h

end ArbitraryPacket

section UniverseOneCategoryZero

variable {C₁ : Type 1} [Category.{0} C₁] [ModelCategory C₁]
variable [HasFunctorialFactorization
  (cofibrations C₁) (trivialFibrations C₁)]

example : (WalkingSpan ⥤ C₁) ⥤ C₁ := homotopyPushout (C := C₁)

example (D : WalkingSpan ⥤ C₁) :
    (homotopyPushout (C := C₁)).obj D ⟶ colimit D :=
  (homotopyPushoutComparison (C := C₁)).app D

example {D : WalkingSpan ⥤ C₁} (R : CofibrantSpanReplacement D) :
    WeakEquivalence ((homotopyPushoutComparison (C := C₁)).app D) ↔
      WeakEquivalence R.toPushout :=
  R.weakEquivalence_homotopyPushoutComparison_iff

end UniverseOneCategoryZero

section Falsifiers

section MissingFactorization

variable {C₀ : Type u} [Category.{v} C₀] [ModelCategory C₀]

example (_D : WalkingSpan ⥤ C₀) : True := by
  fail_if_success
    have _ : (WalkingSpan ⥤ C₀) ⥤ C₀ := homotopyPushout (C := C₀)
  trivial

example {D : WalkingSpan ⥤ C₀}
    (_R : CofibrantSpanReplacement D) : True := by
  fail_if_success
    have _ := _R.exists_weakEquivalence_to_homotopyPushout
  trivial

end MissingFactorization

section MissingLeftProperness

variable {C₀ : Type u} [Category.{v} C₀] [ModelCategory C₀]
variable [HasFunctorialFactorization
  (cofibrations C₀) (trivialFibrations C₀)]

example (_D : WalkingSpan ⥤ C₀)
    [Cofibration (_D.map WalkingSpan.Hom.fst)] : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyPushoutComparison (C := C₀)).app _D) :=
      weakEquivalence_homotopyPushoutComparison_of_leftProper_fst _D
  trivial

end MissingLeftProperness

section MissingCofibrationLegs

example (_D : WalkingSpan ⥤ C)
    [IsCofibrant (_D.obj WalkingSpan.zero)]
    [IsCofibrant (_D.obj WalkingSpan.right)] : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyPushoutComparison (C := C)).app _D) :=
      weakEquivalence_homotopyPushoutComparison_of_fst _D
  trivial

example (_D : WalkingSpan ⥤ C)
    [IsCofibrant (_D.obj WalkingSpan.zero)]
    [IsCofibrant (_D.obj WalkingSpan.left)] : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyPushoutComparison (C := C)).app _D) :=
      weakEquivalence_homotopyPushoutComparison_of_snd _D
  trivial

section LeftProper

variable [IsLeftProper C]

example (_D : WalkingSpan ⥤ C) : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyPushoutComparison (C := C)).app _D) :=
      weakEquivalence_homotopyPushoutComparison_of_leftProper_fst _D
  trivial

example (_D : WalkingSpan ⥤ C) : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyPushoutComparison (C := C)).app _D) :=
      weakEquivalence_homotopyPushoutComparison_of_leftProper_snd _D
  trivial

end LeftProper

end MissingCofibrationLegs

example (_D : WalkingSpan ⥤ C) : True := by
  fail_if_success
    let _ : WeakEquivalence
        ((homotopyPushoutComparison (C := C)).app _D) := inferInstance
  trivial

example {D E : WalkingSpan ⥤ C} (_f : D ⟶ E) : True := by
  fail_if_success
    have _ : WeakEquivalence ((homotopyPushout (C := C)).map _f) :=
      homotopyPushout_map_weakEquivalence _f
  trivial

example {D : WalkingSpan ⥤ C}
    (_R : CofibrantSpanReplacement D) : True := by
  fail_if_success
    let _ := HomotopicalAlgebra.functorialCofibrantSpanReplacement D
  fail_if_success
    let _ := HomotopicalAlgebra.cofibrantSpanReplacementFunctor (C := C)
  fail_if_success
    let _ := CofibrantSpanReplacement.toHomotopyPushout _R
  fail_if_success
    have _ : _R.pushoutObj = (homotopyPushout (C := C)).obj D := rfl
  fail_if_success
    let _ := CofibrantSpanReplacement.homotopyPushoutIso _R
  fail_if_success
    let _ := CofibrantSpanReplacement.localizationComparison _R
  fail_if_success
    let _ := CofibrantSpanReplacement.hoUniversalProperty _R
  trivial

end Falsifiers

end HomotopicalAlgebra.HomotopyPushoutTests

#check HomotopicalAlgebra.homotopyPushout
#check HomotopicalAlgebra.homotopyPushoutComparison
#check HomotopicalAlgebra.homotopyPushout_map_weakEquivalence
#check HomotopicalAlgebra.weakEquivalence_homotopyPushoutComparison_of_fst
#check HomotopicalAlgebra.weakEquivalence_homotopyPushoutComparison_of_snd
#check HomotopicalAlgebra.weakEquivalence_homotopyPushoutComparison_of_leftProper_fst
#check HomotopicalAlgebra.weakEquivalence_homotopyPushoutComparison_of_leftProper_snd
#check HomotopicalAlgebra.CofibrantSpanReplacement.exists_weakEquivalence_to_homotopyPushout
#check HomotopicalAlgebra.CofibrantSpanReplacement.weakEquivalence_homotopyPushoutComparison_iff

#print axioms HomotopicalAlgebra.homotopyPushout
#print axioms HomotopicalAlgebra.homotopyPushoutComparison
#print axioms HomotopicalAlgebra.homotopyPushout_map_weakEquivalence
#print axioms HomotopicalAlgebra.weakEquivalence_homotopyPushoutComparison_of_fst
#print axioms HomotopicalAlgebra.weakEquivalence_homotopyPushoutComparison_of_snd
#print axioms HomotopicalAlgebra.weakEquivalence_homotopyPushoutComparison_of_leftProper_fst
#print axioms HomotopicalAlgebra.weakEquivalence_homotopyPushoutComparison_of_leftProper_snd
#print axioms HomotopicalAlgebra.CofibrantSpanReplacement.exists_weakEquivalence_to_homotopyPushout
#print axioms
  HomotopicalAlgebra.CofibrantSpanReplacement.weakEquivalence_homotopyPushoutComparison_iff

end
