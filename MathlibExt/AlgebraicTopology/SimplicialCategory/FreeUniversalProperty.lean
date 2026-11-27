/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeEvaluation

/-!
# The actual free simplicial universal property

Restriction and extension are the existing computad `functorEquiv`,
transported through the path-label adapter and the singleton-operator
assignment equivalence. There is one free enriched universal property.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialQuiver
variable {O : Type u} (Q : Data O) {C : Type v} [EnrichedCategory SSet.{u} C]

/-- Unwrapping the labels identifies functors from the same actual free path category. -/
def computadFunctorEquiv :
    (EnrichedFunctor SSet.{u} (free Q) C) ≃
      EnrichedFunctor SSet.{u} (computad Q).Object C where
  toFun F := EnrichedFunctor.comp SSet.{u} (fromComputad Q) F
  invFun F := EnrichedFunctor.comp SSet.{u} (toComputad Q) F
  left_inv F := by
    refine EnrichedFunctor.ext SSet.{u} (fun _ => rfl) ?_
    intro x y
    ext n p
    change (F.map x y).app n (fromNativePath Q n (toNativePath Q n p)) = (F.map x y).app n p
    exact congrArg ((F.map x y).app n) (fromNativePath_toNativePath Q n p)
  right_inv F := by
    refine EnrichedFunctor.ext SSet.{u} (fun _ => rfl) ?_
    intro x y
    ext n p
    change (F.map x y).app n (toNativePath Q n (fromNativePath Q n p)) = (F.map x y).app n p
    exact congrArg ((F.map x y).app n) (toNativePath_fromNativePath Q n p)

/-- The canonical computad universal property, with the original quiver labels and maps retained. -/
def interpretationEquiv :
    (EnrichedFunctor SSet.{u} (free Q) C) ≃ Interpretation Q C :=
  (computadFunctorEquiv Q).trans
    ((SSet.SimplicialComputad.functorEquiv (computad Q)).trans assignmentEquiv)

/-- Restrict a genuine enriched functor to the supplied individual generating arrows. -/
def restrict (F : EnrichedFunctor SSet.{u} (free Q) C) : Interpretation Q C :=
  interpretationEquiv Q F

/-- Restriction followed by path evaluation reads back every original enriched Hom simplex. -/
theorem evalPath_restrict (F : EnrichedFunctor SSet.{u} (free Q) C)
    (n : SimplexCategoryᵒᵖ) {x y : O} (p : Path Q n x y) :
    (restrict Q F).evalPath n p = (F.map x y).app n p := by
  have h := SSet.SimplicialComputad.functor_map_path (computad Q)
    (EnrichedFunctor.comp SSet.{u} (fromComputad Q) F) n (toNativePath Q n p)
  change (F.map x y).app n (fromNativePath Q n (toNativePath Q n p)) =
    (restrict Q F).evalPath n p at h
  exact h.symm.trans (congrArg ((F.map x y).app n) (fromNativePath_toNativePath Q n p))

/-- The free extension of the actual generator restriction is the whole original enriched
functor. -/
theorem extend_restrict (F : EnrichedFunctor SSet.{u} (free Q) C) :
    (restrict Q F).extend = F := (interpretationEquiv Q).left_inv F

/-- Restricting the genuine free extension returns the same actual generator interpretation. -/
theorem restrict_extend (I : Interpretation Q C) : restrict Q I.extend = I :=
  (interpretationEquiv Q).right_inv I

end CategoryTheory.SimplicialQuiver
