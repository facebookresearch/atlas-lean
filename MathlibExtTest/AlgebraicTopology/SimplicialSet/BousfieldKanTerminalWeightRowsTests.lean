/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanTerminalWeightRows

/-!
# Terminal-weight row tests

These tests pin coefficient evaluation, terminal `PUnit` reassociation, all
outer operator orientations, and the evaluated augmentation on a weighted
summand.  They make no diagonal or weak-equivalence claim.
-/

open CategoryTheory Limits Opposite Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.BousfieldKanTerminalWeightRowsTests

variable {J : Type u} [Category.{0} J]
variable (D : J ⥤ SSet.{u}) (a : SimplexCategoryᵒᵖ)

example : J ⥤ Type u := SSet.wbarDegreeCoefficient D a

noncomputable example : SSet.{u} := SSet.wbarRow D a

noncomputable example :
    (StrictOrdinaryWeightedBar.wbarData
          (CategoryBar.replUnit J) D).toSimplicialObject ⋙
        (evaluation SimplexCategoryᵒᵖ (Type u)).obj a ≅
      SSet.wbarRow D a :=
  SSet.wbarRowEvaluationIso D a

example (b : SimplexCategoryᵒᵖ) :
    (SSet.wbarRowEvaluationIso D a).hom.app b = 𝟙 _ :=
  SSet.wbarRowEvaluationIso_hom_app D a b

example (j : J) :
    (SSet.wbarDegreeCoefficient D a).obj j = (D.obj j).obj a :=
  SSet.wbarDegreeCoefficient_obj D a j

example {n : ℕ} (s : ComposableArrows J n) (w : PUnit)
    (x : (D.obj s.left).obj a) :
    SSet.terminalWeightSigmaEquiv D a n ⟨⟨s, w⟩, x⟩ =
      (⟨s, x, w⟩ : CategoryBar.replObj J
        (SSet.wbarDegreeCoefficient D a) n) :=
  SSet.terminalWeightSigmaEquiv_apply D a s w x

example {n : ℕ} (s : ComposableArrows J n) (w : PUnit)
    (x : (D.obj s.left).obj a) :
    (SSet.terminalWeightSigmaEquiv D a n).symm
        (⟨s, x, w⟩ : CategoryBar.replObj J
          (SSet.wbarDegreeCoefficient D a) n) =
      ⟨⟨s, w⟩, x⟩ :=
  SSet.terminalWeightSigmaEquiv_symm_apply D a s w x

example (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
    (x : (D.obj p.1.left).obj a) :
    (SSet.terminalWeightRowDegreeIso D a n).hom
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) D n p).app a x) =
      (⟨p.1, x, p.2⟩ : CategoryBar.replObj J
        (SSet.wbarDegreeCoefficient D a) n) :=
  SSet.terminalWeightRowDegreeIso_hom_ι_apply D a n p x

section Operators

/-- Face zero commutes with the row comparison. -/
example :
    (SSet.wbarRow D a).map (SimplexCategory.δ (0 : Fin 3)).op ≫
        (SSet.terminalWeightRowIso D a).hom.app (op ⦋1⦌) =
      (SSet.terminalWeightRowIso D a).hom.app (op ⦋2⦌) ≫
        (CategoryBar.simplicialReplacement
          (SSet.wbarDegreeCoefficient D a)).map
            (SimplexCategory.δ (0 : Fin 3)).op :=
  (SSet.terminalWeightRowIso D a).hom.naturality _

/-- The last face commutes with the row comparison. -/
example :
    (SSet.wbarRow D a).map (SimplexCategory.δ (Fin.last 2)).op ≫
        (SSet.terminalWeightRowIso D a).hom.app (op ⦋1⦌) =
      (SSet.terminalWeightRowIso D a).hom.app (op ⦋2⦌) ≫
        (CategoryBar.simplicialReplacement
          (SSet.wbarDegreeCoefficient D a)).map
            (SimplexCategory.δ (Fin.last 2)).op :=
  (SSet.terminalWeightRowIso D a).hom.naturality _

/-- A genuine interior face commutes with the row comparison. -/
example :
    (SSet.wbarRow D a).map (SimplexCategory.δ (1 : Fin 3)).op ≫
        (SSet.terminalWeightRowIso D a).hom.app (op ⦋1⦌) =
      (SSet.terminalWeightRowIso D a).hom.app (op ⦋2⦌) ≫
        (CategoryBar.simplicialReplacement
          (SSet.wbarDegreeCoefficient D a)).map
            (SimplexCategory.δ (1 : Fin 3)).op :=
  (SSet.terminalWeightRowIso D a).hom.naturality _

/-- Degeneracy commutes with the row comparison. -/
example :
    (SSet.wbarRow D a).map (SimplexCategory.σ (0 : Fin 2)).op ≫
        (SSet.terminalWeightRowIso D a).hom.app (op ⦋2⦌) =
      (SSet.terminalWeightRowIso D a).hom.app (op ⦋1⦌) ≫
        (CategoryBar.simplicialReplacement
          (SSet.wbarDegreeCoefficient D a)).map
            (SimplexCategory.σ (0 : Fin 2)).op :=
  (SSet.terminalWeightRowIso D a).hom.naturality _

end Operators

section Augmentation

variable {Z : SSet.{u}} (τ : D ⟶ (Functor.const J).obj Z)

example :
    (SSet.terminalWeightRowIso D a).hom ≫
        SSet.terminalWeightDegreeAugmentation τ a =
      SSet.wbarRowAugmentation τ a :=
  SSet.terminalWeightRowIso_hom_comp_degreeAugmentation τ a

example :
    (SSet.wbarRowEvaluationIso D a).hom ≫
        SSet.wbarRowAugmentation τ a =
      Functor.whiskerRight (SSet.wbarAugmentation τ)
        ((evaluation SimplexCategoryᵒᵖ (Type u)).obj a) :=
  SSet.wbarRowEvaluationIso_hom_comp_rowAugmentation τ a

example (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit J) D n p).app a ≫
        (SSet.wbarRowAugmentation τ a).app (op ⦋n⦌) =
      (τ.app p.1.left).app a :=
  SSet.wbarRowAugmentation_ι τ a n p

/-- In outer degree zero the transported augmentation selects its sole
source coefficient. -/
example (j : J) :
    (ComposableArrows.mk₀ j).left = j ∧
      SSet.terminalWeightReplIncl D a 0
            ⟨ComposableArrows.mk₀ j, PUnit.unit⟩ ≫
          (SSet.terminalWeightDegreeAugmentation τ a).app (op ⦋0⦌) =
        (τ.app (ComposableArrows.mk₀ j).left).app a :=
  ⟨rfl, SSet.terminalWeightReplIncl_comp_degreeAugmentation τ a 0
    ⟨ComposableArrows.mk₀ j, PUnit.unit⟩⟩

/-- In outer degree one a genuine arrow still selects the coefficient at its
left/source endpoint. -/
example {j k : J} (_hjk : j ≠ k) (f : j ⟶ k) :
    (ComposableArrows.mk₁ f).left = j ∧
      SSet.terminalWeightReplIncl D a 1
            ⟨ComposableArrows.mk₁ f, PUnit.unit⟩ ≫
          (SSet.terminalWeightDegreeAugmentation τ a).app (op ⦋1⦌) =
        (τ.app (ComposableArrows.mk₁ f).left).app a :=
  ⟨rfl, SSet.terminalWeightReplIncl_comp_degreeAugmentation τ a 1
    ⟨ComposableArrows.mk₁ f, PUnit.unit⟩⟩

end Augmentation

section UniverseOne

variable {J₁ : Type 1} [Category.{0} J₁]
variable (D₁ : J₁ ⥤ SSet.{1}) (a₁ : SimplexCategoryᵒᵖ)

noncomputable example : SSet.{1} := SSet.wbarRow D₁ a₁

noncomputable example :
    SSet.wbarRow D₁ a₁ ≅
      CategoryBar.simplicialReplacement
        (SSet.wbarDegreeCoefficient D₁ a₁) :=
  SSet.terminalWeightRowIso D₁ a₁

variable {Z₁ : SSet.{1}} (τ₁ : D₁ ⟶ (Functor.const J₁).obj Z₁)

example (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J₁ (CategoryBar.replUnit J₁) n) :
    SSet.terminalWeightReplIncl D₁ a₁ n p ≫
        (SSet.terminalWeightDegreeAugmentation τ₁ a₁).app (op ⦋n⦌) =
      (τ₁.app p.1.left).app a₁ :=
  SSet.terminalWeightReplIncl_comp_degreeAugmentation τ₁ a₁ n p

end UniverseOne

section UniverseZero

variable {J₀ : Type} [Category J₀]
variable (D₀ : J₀ ⥤ SSet.{0}) (a₀ : SimplexCategoryᵒᵖ)

noncomputable example : SSet.{0} := SSet.wbarRow D₀ a₀

variable {Z₀ : SSet.{0}} (τ₀ : D₀ ⟶ (Functor.const J₀).obj Z₀)

example (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J₀ (CategoryBar.replUnit J₀) n) :
    SSet.terminalWeightReplIncl D₀ a₀ n p ≫
        (SSet.terminalWeightDegreeAugmentation τ₀ a₀).app (op ⦋n⦌) =
      (τ₀.app p.1.left).app a₀ :=
  SSet.terminalWeightReplIncl_comp_degreeAugmentation τ₀ a₀ n p

noncomputable example :
    let J := Discrete Empty
    let D := (Functor.const J).obj (⊥_ SSet.{0})
    SSet.wbarRow D (op ⦋0⦌) ≅
      CategoryBar.simplicialReplacement
        (SSet.wbarDegreeCoefficient D (op ⦋0⦌)) :=
  SSet.terminalWeightRowIso _ _

noncomputable example :
    let J := Discrete Bool
    let D := (Functor.const J).obj (⊥_ SSet.{0})
    SSet.wbarRow D (op ⦋1⦌) ≅
      CategoryBar.simplicialReplacement
        (SSet.wbarDegreeCoefficient D (op ⦋1⦌)) :=
  SSet.terminalWeightRowIso _ _

end UniverseZero

#print axioms SSet.terminalWeightFace_compat
#print axioms SSet.terminalWeightDegeneracy_compat
#print axioms SSet.terminalWeightReplIncl_comp_degreeAugmentation

end MathlibExtTest.AlgebraicTopology.SimplicialSet.BousfieldKanTerminalWeightRowsTests
