/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceCoefficientLiftMap
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceCategory
import Mathlib.CategoryTheory.ConnectedComponents

/-!
# Actual full original flagged-necklace evaluation in the SAME raw Hom

The proven unique native coefficient lift is sent through the entire
original input map. Every actual full flagged morphism retains its
original over-map square and complete coefficient image equation, so
evaluation descends to the actual original category components.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open OriginalNecklaceHom

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- Every SAME original flagged object has its entire actual joint-containing coefficient. -/
def jointCoefficient (T : Object K x y q) : (fullCoefficient.{u} T.necklace).obj q :=
  ⟨T.coefficient, T.joints⟩

/-- The SAME original full input map retains the actual original source vertex equation. -/
theorem input_source (T : Object K x y q) : T.input.app (op ⦋0⦌) (sourceVertex T.necklace) = x :=
  (SSet.yonedaEquiv_comp T.necklace.source T.input).symm.trans T.source_eq

/-- The SAME original full input map retains the actual original target vertex equation. -/
theorem input_target (T : Object K x y q) : T.input.app (op ⦋0⦌) (targetVertex T.necklace) = y :=
  (SSet.yonedaEquiv_comp T.necklace.target T.input).symm.trans T.target_eq

/-- The SAME entire original input Hom map from the native raw Hom to the original input raw Hom. -/
def inputHomMap (T : Object K x y q) :
    hom T.necklace.object.{u} (sourceVertex T.necklace) (targetVertex T.necklace) ⟶ hom K x y :=
  pointedHomMap T.input (input_source T) (input_target T)

/-- Every actual original full flagged map retains its complete original raw input Hom square. -/
theorem inputHomMap_natural {T U : Object K x y q} (f : T ⟶ U) :
    nativeHomMap f.necklaceMap ≫ inputHomMap U = inputHomMap T :=
  (pointedHomMap_comp f.necklaceMap.map U.input (nativeMap_source f.necklaceMap)
    (nativeMap_target f.necklaceMap) (input_source U) (input_target U)).trans
      (pointedHomMap_eq f.over
        ((congrArg (fun v => U.input.app (op ⦋0⦌) v) (nativeMap_source f.necklaceMap)).trans (input_source U))
        ((congrArg (fun v => U.input.app (op ⦋0⦌) v) (nativeMap_target f.necklaceMap)).trans (input_target U))
        (input_source T) (input_target T))

/-- The actual full original flagged-necklace value in the SAME original raw coherent Hom. -/
def evaluation (T : Object K x y q) : (hom K x y).obj q :=
  (inputHomMap T).app q (coefficientLift T.necklace (jointCoefficient T))

/-- EVERY actual full original flagged morphism retains the SAME original raw evaluation. -/
theorem evaluation_natural {T U : Object K x y q} (f : T ⟶ U) : evaluation T = evaluation U := by
  have h := ConcreteCategory.congr_hom (congr_app (inputHomMap_natural f) q)
    (coefficientLift T.necklace (jointCoefficient T))
  exact h.symm.trans (congrArg ((inputHomMap U).app q)
    (coefficientLift_native f.necklaceMap (jointCoefficient T) (jointCoefficient U) f.flags))

/-- The SAME original raw evaluation is a genuine functor to its discrete original Hom simplex set. -/
def evaluationFunctor (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    Object K x y q ⥤ Discrete ((hom K x y).obj q) where
  obj T := Discrete.mk (evaluation T)
  map f := Discrete.eqToHom (evaluation_natural f)

namespace Components

/-- The SAME actual full flagged component is evaluated in its original raw coherent Hom quotient. -/
def rawEvaluation (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    CategoryTheory.ConnectedComponents (Object K x y q) → (hom K x y).obj q :=
  CategoryTheory.ConnectedComponents.liftFunctor (Object K x y q) (evaluationFunctor K x y q)

/-- Every SAME actual original component representative retains its entire original input and coefficient lift. -/
theorem rawEvaluation_mk (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) (T : Object K x y q) :
    rawEvaluation K x y q (CategoryTheory.ConnectedComponents.mk T) = evaluation T := rfl

end Components

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
