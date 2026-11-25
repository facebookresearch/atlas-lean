/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyPullback

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.HomotopyPullbackTests

variable {C : Type u} [Category.{v} C] [ModelCategory C]
variable [HasFunctorialFactorization
  (trivialCofibrations C) (fibrations C)]

section Core

variable (D : WalkingCospan ⥤ C)

example : C := (homotopyPullback (C := C)).obj D

example : limit D ⟶ (homotopyPullback (C := C)).obj D :=
  (homotopyPullbackComparison (C := C)).app D

example :
    (homotopyPullback (C := C)).map (𝟙 D) =
      𝟙 ((homotopyPullback (C := C)).obj D) :=
  (homotopyPullback (C := C)).map_id D

variable {E F : WalkingCospan ⥤ C}

example (f : D ⟶ E) (g : E ⟶ F) :
    (homotopyPullback (C := C)).map (f ≫ g) =
      (homotopyPullback (C := C)).map f ≫
        (homotopyPullback (C := C)).map g :=
  (homotopyPullback (C := C)).map_comp f g

example (f : D ⟶ E) :
    lim.map f ≫ (homotopyPullbackComparison (C := C)).app E =
      (homotopyPullbackComparison (C := C)).app D ≫
        (homotopyPullback (C := C)).map f :=
  (homotopyPullbackComparison (C := C)).naturality f

end Core

section PointwiseWeak

variable {D E : WalkingCospan ⥤ C} (f : D ⟶ E)
variable (hone : WeakEquivalence (f.app WalkingCospan.one))
variable (hleft : WeakEquivalence (f.app WalkingCospan.left))
variable (hright : WeakEquivalence (f.app WalkingCospan.right))

example : WeakEquivalence ((homotopyPullback (C := C)).map f) := by
  apply homotopyPullback_map_weakEquivalence f
  rintro (_ | _ | _)
  · exact hone
  · exact hleft
  · exact hright

example (D : WalkingCospan ⥤ C) :
    WeakEquivalence ((homotopyPullback (C := C)).map (𝟙 D)) := by
  apply homotopyPullback_map_weakEquivalence (𝟙 D)
  intro j
  change WeakEquivalence (𝟙 (D.obj j))
  infer_instance

end PointwiseWeak

section ComparisonCriteria

variable (D : WalkingCospan ⥤ C)

example [IsFibrant (D.obj WalkingCospan.one)]
    [IsFibrant (D.obj WalkingCospan.right)]
    [Fibration (D.map WalkingCospan.Hom.inl)] :
    WeakEquivalence ((homotopyPullbackComparison (C := C)).app D) :=
  weakEquivalence_homotopyPullbackComparison_of_inl D

example [IsFibrant (D.obj WalkingCospan.one)]
    [IsFibrant (D.obj WalkingCospan.left)]
    [Fibration (D.map WalkingCospan.Hom.inr)] :
    WeakEquivalence ((homotopyPullbackComparison (C := C)).app D) :=
  weakEquivalence_homotopyPullbackComparison_of_inr D

section RightProper

variable [IsRightProper C]

example [Fibration (D.map WalkingCospan.Hom.inl)] :
    WeakEquivalence ((homotopyPullbackComparison (C := C)).app D) :=
  weakEquivalence_homotopyPullbackComparison_of_rightProper_inl D

example [Fibration (D.map WalkingCospan.Hom.inr)] :
    WeakEquivalence ((homotopyPullbackComparison (C := C)).app D) :=
  weakEquivalence_homotopyPullbackComparison_of_rightProper_inr D

end RightProper

end ComparisonCriteria

section IdentityCospans

variable {X : C}

private abbrev identityCospan (X : C) : WalkingCospan ⥤ C :=
  cospan (𝟙 X) (𝟙 X)

example [IsFibrant X] :
    WeakEquivalence
      ((homotopyPullbackComparison (C := C)).app
        (identityCospan X)) := by
  let _ : IsFibrant
      ((identityCospan X).obj WalkingCospan.one) := by
    change IsFibrant X
    infer_instance
  let _ : IsFibrant
      ((identityCospan X).obj WalkingCospan.right) := by
    change IsFibrant X
    infer_instance
  let _ : Fibration
      ((identityCospan X).map WalkingCospan.Hom.inl) := by
    change Fibration (𝟙 X)
    infer_instance
  exact weakEquivalence_homotopyPullbackComparison_of_inl
    (identityCospan X)

example [IsFibrant X] :
    WeakEquivalence
      ((homotopyPullbackComparison (C := C)).app
        (identityCospan X)) := by
  let _ : IsFibrant
      ((identityCospan X).obj WalkingCospan.one) := by
    change IsFibrant X
    infer_instance
  let _ : IsFibrant
      ((identityCospan X).obj WalkingCospan.left) := by
    change IsFibrant X
    infer_instance
  let _ : Fibration
      ((identityCospan X).map WalkingCospan.Hom.inr) := by
    change Fibration (𝟙 X)
    infer_instance
  exact weakEquivalence_homotopyPullbackComparison_of_inr
    (identityCospan X)

private abbrev terminalCospan : WalkingCospan ⥤ C :=
  cospan (𝟙 (⊤_ C)) (𝟙 (⊤_ C))

example :
    WeakEquivalence
      ((homotopyPullbackComparison (C := C)).app
        (terminalCospan (C := C))) := by
  let hTerminal : IsFibrant (⊤_ C) :=
    (isFibrant_iff_of_isTerminal (𝟙 (⊤_ C)) terminalIsTerminal).2
      (by infer_instance)
  let _ : IsFibrant
      ((terminalCospan (C := C)).obj WalkingCospan.one) := by
    change IsFibrant (⊤_ C)
    exact hTerminal
  let _ : IsFibrant
      ((terminalCospan (C := C)).obj WalkingCospan.right) := by
    change IsFibrant (⊤_ C)
    exact hTerminal
  let _ : Fibration
      ((terminalCospan (C := C)).map WalkingCospan.Hom.inl) := by
    change Fibration (𝟙 (⊤_ C))
    infer_instance
  apply weakEquivalence_homotopyPullbackComparison_of_inl

end IdentityCospans

section ArbitraryPacket

variable {D : WalkingCospan ⥤ C} (R : FibrantCospanReplacement D)

example :
    ∃ f : (homotopyPullback (C := C)).obj D ⟶ R.pullbackObj,
      WeakEquivalence f ∧
        (homotopyPullbackComparison (C := C)).app D ≫ f =
          R.fromPullback :=
  R.exists_weakEquivalence_from_homotopyPullback

example : True := by
  obtain ⟨f, hf, htriangle⟩ :=
    R.exists_weakEquivalence_from_homotopyPullback
  have _ : WeakEquivalence f := hf
  have _ : (homotopyPullbackComparison (C := C)).app D ≫ f =
      (R.fromPullback : limit D ⟶ R.pullbackObj) := htriangle
  trivial

example :
    WeakEquivalence ((homotopyPullbackComparison (C := C)).app D) ↔
      WeakEquivalence R.fromPullback :=
  R.weakEquivalence_homotopyPullbackComparison_iff

end ArbitraryPacket

section UniverseOneCategoryZero

variable {C₁ : Type 1} [Category.{0} C₁] [ModelCategory C₁]
variable [HasFunctorialFactorization
  (trivialCofibrations C₁) (fibrations C₁)]

example : (WalkingCospan ⥤ C₁) ⥤ C₁ :=
  homotopyPullback (C := C₁)

example (D : WalkingCospan ⥤ C₁) :
    limit D ⟶ (homotopyPullback (C := C₁)).obj D :=
  (homotopyPullbackComparison (C := C₁)).app D

example {D : WalkingCospan ⥤ C₁}
    (R : FibrantCospanReplacement D) :
    WeakEquivalence ((homotopyPullbackComparison (C := C₁)).app D) ↔
      WeakEquivalence R.fromPullback :=
  R.weakEquivalence_homotopyPullbackComparison_iff

end UniverseOneCategoryZero

section Falsifiers

section MissingFactorization

variable {C₀ : Type u} [Category.{v} C₀] [ModelCategory C₀]

example (_D : WalkingCospan ⥤ C₀) : True := by
  fail_if_success
    have _ : (WalkingCospan ⥤ C₀) ⥤ C₀ :=
      homotopyPullback (C := C₀)
  trivial

example {D : WalkingCospan ⥤ C₀}
    (_R : FibrantCospanReplacement D) : True := by
  fail_if_success
    have _ := _R.exists_weakEquivalence_from_homotopyPullback
  trivial

end MissingFactorization

section MissingRightProperness

variable {C₀ : Type u} [Category.{v} C₀] [ModelCategory C₀]
variable [HasFunctorialFactorization
  (trivialCofibrations C₀) (fibrations C₀)]

example (_D : WalkingCospan ⥤ C₀)
    [Fibration (_D.map WalkingCospan.Hom.inl)] : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyPullbackComparison (C := C₀)).app _D) :=
      weakEquivalence_homotopyPullbackComparison_of_rightProper_inl _D
  trivial

end MissingRightProperness

section MissingFibrancy

example (_D : WalkingCospan ⥤ C)
    [Fibration (_D.map WalkingCospan.Hom.inl)] : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyPullbackComparison (C := C)).app _D) :=
      weakEquivalence_homotopyPullbackComparison_of_inl _D
  trivial

end MissingFibrancy

section MissingFibrationLegs

example (_D : WalkingCospan ⥤ C)
    [IsFibrant (_D.obj WalkingCospan.one)]
    [IsFibrant (_D.obj WalkingCospan.right)] : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyPullbackComparison (C := C)).app _D) :=
      weakEquivalence_homotopyPullbackComparison_of_inl _D
  trivial

section RightProper

variable [IsRightProper C]

example (_D : WalkingCospan ⥤ C) : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyPullbackComparison (C := C)).app _D) :=
      weakEquivalence_homotopyPullbackComparison_of_rightProper_inl _D
  trivial

example (_D : WalkingCospan ⥤ C) : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyPullbackComparison (C := C)).app _D) :=
      weakEquivalence_homotopyPullbackComparison_of_rightProper_inr _D
  trivial

end RightProper

end MissingFibrationLegs

example (_D : WalkingCospan ⥤ C) : True := by
  fail_if_success
    let _ : WeakEquivalence
        ((homotopyPullbackComparison (C := C)).app _D) := inferInstance
  trivial

example {D E : WalkingCospan ⥤ C} (_f : D ⟶ E) : True := by
  fail_if_success
    have _ : WeakEquivalence ((homotopyPullback (C := C)).map _f) :=
      homotopyPullback_map_weakEquivalence _f
  trivial

example {D : WalkingCospan ⥤ C}
    (_R : FibrantCospanReplacement D) : True := by
  fail_if_success
    let _ := HomotopicalAlgebra.functorialFibrantCospanReplacement D
  fail_if_success
    let _ := HomotopicalAlgebra.fibrantCospanReplacementFunctor (C := C)
  fail_if_success
    let _ := FibrantCospanReplacement.fromHomotopyPullback _R
  fail_if_success
    have _ : (homotopyPullback (C := C)).obj D = R.pullbackObj := rfl
  fail_if_success
    let _ := FibrantCospanReplacement.homotopyPullbackIso _R
  fail_if_success
    let _ := FibrantCospanReplacement.localizationComparison _R
  fail_if_success
    let _ := FibrantCospanReplacement.hoUniversalProperty _R
  trivial

end Falsifiers

end HomotopicalAlgebra.HomotopyPullbackTests

#check HomotopicalAlgebra.homotopyPullback
#check HomotopicalAlgebra.homotopyPullbackComparison
#check HomotopicalAlgebra.homotopyPullback_map_weakEquivalence
#check HomotopicalAlgebra.weakEquivalence_homotopyPullbackComparison_of_inl
#check HomotopicalAlgebra.weakEquivalence_homotopyPullbackComparison_of_inr
#check HomotopicalAlgebra.weakEquivalence_homotopyPullbackComparison_of_rightProper_inl
#check HomotopicalAlgebra.weakEquivalence_homotopyPullbackComparison_of_rightProper_inr
#check HomotopicalAlgebra.FibrantCospanReplacement.exists_weakEquivalence_from_homotopyPullback
#check HomotopicalAlgebra.FibrantCospanReplacement.weakEquivalence_homotopyPullbackComparison_iff

#print axioms HomotopicalAlgebra.homotopyPullback
#print axioms HomotopicalAlgebra.homotopyPullbackComparison
#print axioms HomotopicalAlgebra.homotopyPullback_map_weakEquivalence
#print axioms HomotopicalAlgebra.weakEquivalence_homotopyPullbackComparison_of_inl
#print axioms HomotopicalAlgebra.weakEquivalence_homotopyPullbackComparison_of_inr
#print axioms
  HomotopicalAlgebra.weakEquivalence_homotopyPullbackComparison_of_rightProper_inl
#print axioms
  HomotopicalAlgebra.weakEquivalence_homotopyPullbackComparison_of_rightProper_inr
#print axioms
  HomotopicalAlgebra.FibrantCospanReplacement.exists_weakEquivalence_from_homotopyPullback
#print axioms
  HomotopicalAlgebra.FibrantCospanReplacement.weakEquivalence_homotopyPullbackComparison_iff

end
