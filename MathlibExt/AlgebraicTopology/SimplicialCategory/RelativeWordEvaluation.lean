/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordMaps
import MathlibExt.CategoryTheory.Category.RelativeGeneratorsEvaluation

/-!
# Actual scalar evaluation of a compatible enriched attaching cocone

The original enriched map and whole target-generator maps evaluate every
normalized word. The actual attaching square reads each target letter
back exactly. Whole evaluation commutes with every original simplex
operator, using the original enriched composition and actual map
naturality; no evaluation or pushout outcome is supplied as an input.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords

variable {O : Type u} {C D : FixedObjects O}

/-- Evaluate every normalized word by the actual original enriched map and supplied target-generator images. -/
def evalAt (T : Data C) (F : C ⟶ D) (m : ∀ x y : O, T.target.Hom x y ⟶ hom D x y)
    (q : SimplexCategoryᵒᵖ) {x y : O} (p : WordAt T q x y) : (hom D x y).obj q :=
  @RelativeWords.eval O (scalarCategory C q) (newAt T q) O (scalarCategory D q)
    (scalarFunctor F q) (fun {x y} g => (m x y).app q g.val) x y p

/-- The original Hom segment is read back by the same whole original enriched map. -/
theorem evalAt_old (T : Data C) (F : C ⟶ D) (m : ∀ x y : O, T.target.Hom x y ⟶ hom D x y)
    (q : SimplexCategoryᵒᵖ) {x y : O} (p : (hom C x y).obj q) :
    evalAt T F m q (oldWord T q p) = (homMap F x y).app q p := rfl

/-- Evaluation preserves the actual whole normalized-word composition. -/
theorem evalAt_comp (T : Data C) (F : C ⟶ D) (m : ∀ x y : O, T.target.Hom x y ⟶ hom D x y)
    (q : SimplexCategoryᵒᵖ) {x y z : O} (p : WordAt T q x y) (t : WordAt T q y z) :
    evalAt T F m q (compWords T q p t) =
      (compositionMap D x y z).app q (evalAt T F m q p, evalAt T F m q t) :=
  @RelativeWords.eval_comp O (scalarCategory C q) (newAt T q) O (scalarCategory D q)
    (scalarFunctor F q) (fun {x y} g => (m x y).app q g.val) x y z p t

/-- The complete original first segment, target letter and remaining word evaluate by actual target composition. -/
theorem evalAt_cons (T : Data C) (F : C ⟶ D) (m : ∀ x y : O, T.target.Hom x y ⟶ hom D x y)
    (q : SimplexCategoryᵒᵖ) {a x y b : O} (h : (hom C a x).obj q)
    (g : newAt T q x y) (p : WordAt T q y b) :
    evalAt T F m q (consWord T q h g p) =
      (compositionMap D a x b).app q ((homMap F a x).app q h,
        (compositionMap D x y b).app q ((m x y).app q g.val, evalAt T F m q p)) := rfl

/-- The actual attaching square evaluates every target letter as its same supplied original image. -/
theorem evalAt_letter (T : Data C) (F : C ⟶ D) (m : ∀ x y : O, T.target.Hom x y ⟶ hom D x y)
    (hm : ∀ x y : O, T.inclusion x y ≫ m x y = T.attaching x y ≫ homMap F x y)
    (q : SimplexCategoryᵒᵖ) {x y : O} (b : (T.target.Hom x y).obj q) :
    evalAt T F m q (letter T q b) = (m x y).app q b :=
  @RelativeGenerators.eval_reduce O (scalarCategory C q) O (scalarCategory D q)
    (fun x y => (T.domain.Hom x y).obj q) (fun x y => (T.target.Hom x y).obj q)
    (scalarFunctor F q) (fun {_ _} a => inclusionAt T q a) (fun {_ _} a => attachingAt T q a)
    (fun {x y} b => (m x y).app q b)
    (fun {x y} a => congr($(hm x y).app q a)) x y b

private theorem composition_operator (D : FixedObjects O) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r)
    (x y z : O) (a : (hom D x y).obj q) (b : (hom D y z).obj q) :
    (hom D x z).map f ((compositionMap D x y z).app q (a, b)) =
      (compositionMap D x y z).app r ((hom D x y).map f a, (hom D y z).map f b) :=
  congr($((compositionMap D x y z).naturality f) (a, b)).symm

/-- Every actual original scalar operator commutes with evaluation of the entire normalized word. -/
theorem evalAt_operator (T : Data C) (F : C ⟶ D) (m : ∀ x y : O, T.target.Hom x y ⟶ hom D x y)
    (hm : ∀ x y : O, T.inclusion x y ≫ m x y = T.attaching x y ≫ homMap F x y)
    {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) {x y : O} (p : WordAt T q x y) :
    (hom D x y).map f (evalAt T F m q p) = evalAt T F m r (operator T f p) := by
  induction p with
  | @old x y h =>
      rw [operator_old, evalAt_old, evalAt_old]
      exact (scalarFunctor_operator F f x y h).symm
  | @cons a x y b h g p ih =>
      change (hom D a b).map f (evalAt T F m q (consWord T q h g p)) =
        evalAt T F m r (operator T f (consWord T q h g p))
      rw [evalAt_cons, composition_operator, composition_operator,
        operator_cons, evalAt_comp, evalAt_old, evalAt_comp, evalAt_letter T F m hm]
      have hF := scalarFunctor_operator F f a x h
      have hM := congr($((m x y).naturality f) g.val)
      change (m x y).app r ((T.target.Hom x y).map f g.val) =
        (hom D x y).map f ((m x y).app q g.val) at hM
      rw [hF, hM, ← ih]

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
