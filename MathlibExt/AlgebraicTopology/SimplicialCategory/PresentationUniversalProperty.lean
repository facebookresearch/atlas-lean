/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.Presentation
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeUniversalProperty

/-!
# The actual simplicial presentation universal property

Genuine enriched functors from the presentation correspond to original
generator interpretations satisfying its explicit generating equations.
The proof descends the full path evaluation and establishes both whole
inverse equations, rather than providing a comparison certificate.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialQuiver
variable {O : Type u} {Q : Data O} (R : Relations Q)
    {C : Type v} [EnrichedCategory SSet.{u} C]

/-- The actual enriched quotient functor on whole original paths, fixing every original object. -/
def quotientFunctor : EnrichedFunctor SSet.{u} (free Q) (presented R) where
  obj x := x
  map x y := quotientHom R x y
  map_id x := by ext n a; rfl
  map_comp x y z := by ext n a; rfl

/-- Restriction of a genuine presentation functor to its original generating simplicial arrows. -/
def restrictPresented (F : EnrichedFunctor SSet.{u} (presented R) C) : Interpretation Q C :=
  restrict Q ((quotientFunctor R).comp SSet.{u} F)

/-- Whole-path evaluation of this restriction reads the actual presentation functor on that
path class. -/
theorem evalPath_restrictPresented (F : EnrichedFunctor SSet.{u} (presented R) C)
    (n : SimplexCategoryᵒᵖ) {x y : O} (p : Path Q n x y) :
    (restrictPresented R F).evalPath n p =
      (F.map x y).app n (_root_.Quotient.mk (congruence R n x y) p) :=
  evalPath_restrict Q ((quotientFunctor R).comp SSet.{u} F) n p

/-- The actual restricted generators satisfy every original stated presentation equation. -/
theorem restrictPresented_relations (F : EnrichedFunctor SSet.{u} (presented R) C)
    (n : SimplexCategoryᵒᵖ) (x y : O) (p q : Path Q n x y) (h : R n x y p q) :
    (restrictPresented R F).evalPath n p = (restrictPresented R F).evalPath n q := by
  exact (evalPath_restrictPresented R F n p).trans
    ((congrArg (fun a => (F.map x y).app n a) (_root_.Quotient.sound (Closure.relation h))).trans
      (evalPath_restrictPresented R F n q).symm)

/-- Descending the original generator restriction recovers the whole enriched presentation
functor. -/
theorem descend_restrictPresented (F : EnrichedFunctor SSet.{u} (presented R) C) :
    (restrictPresented R F).descend R (restrictPresented_relations R F) = F := by
  let : EnrichedCategory SSet.{u} O := presentedEnrichment R
  change EnrichedFunctor SSet.{u} O C at F
  refine EnrichedFunctor.ext SSet.{u} (C := O) (D := C)
    (F := (restrictPresented R F).descend R (restrictPresented_relations R F)) (G := F)
    (fun _ => rfl) ?_
  intro x y
  change (restrictPresented R F).descendHom R (restrictPresented_relations R F) x y ≫
    𝟙 _ = F.map x y
  rw [Category.comp_id]
  ext n a
  induction a using _root_.Quotient.inductionOn with
  | h p => exact evalPath_restrictPresented R F n p

/-- Restricting the descended original generator interpretation recovers every given
generator map. -/
theorem restrictPresented_descend (I : Interpretation Q C)
    (hR : ∀ n x y p q, R n x y p q → I.evalPath n p = I.evalPath n q) :
    restrictPresented R (I.descend R hR) = I := by
  cases I with
  | mk obj map =>
      change Interpretation.mk obj
        (fun x y => generator Q x y ≫ quotientHom R x y ≫
          (Interpretation.descendHom (Q := Q) ⟨obj, map⟩ R hR x y)) = Interpretation.mk obj map
      congr 1
      funext x y
      exact (congrArg (fun g => generator Q x y ≫ g)
        (Interpretation.quotient_descend ⟨obj, map⟩ R hR x y)).trans
          (Interpretation.generator_eval ⟨obj, map⟩ x y)

/-- The genuine Hom equivalence for the actual simplicial presentation and its original
generators. -/
def presentedInterpretationEquiv : EnrichedFunctor SSet.{u} (presented R) C ≃
    {I : Interpretation Q C // ∀ n x y p q, R n x y p q → I.evalPath n p = I.evalPath n q} where
  toFun F := ⟨restrictPresented R F, restrictPresented_relations R F⟩
  invFun I := I.val.descend R I.property
  left_inv := descend_restrictPresented R
  right_inv I := Subtype.ext (restrictPresented_descend R I.val I.property)

end CategoryTheory.SimplicialQuiver
