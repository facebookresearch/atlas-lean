/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeBasisImageIso
import Mathlib.CategoryTheory.Yoneda

/-!
# Actual native simplex and sharp-edge image isomorphisms

The original simplex and sharp chart Hom correspondences corepresent
the same whole slice Hom functor as native straightening. Mathlib's
corepresenter uniqueness constructs their comparison through precisely
the actual native unit and chart unit. No replacement or comparison
outcome is an input.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The native adjunction corepresents the original whole same-base slice Hom functor. -/
def nativeImageCorepresenter (B : SSet.{u}) (X : Over (max B)) :
    ((nativeUnstraightening B) ⋙ coyoneda.obj (op X)).CorepresentableBy
      ((nativeStraightening B).obj X) where
  homEquiv := (nativeStraighteningAdjunction B).homEquiv X _
  homEquiv_comp g f := (nativeStraighteningAdjunction B).homEquiv_naturality_right f g

/-- The original native simplex chart corepresents that same entire slice Hom functor. -/
def nativeSimplexCorepresenter (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    ((nativeUnstraightening B) ⋙ coyoneda.obj (op (nativeSimplexBasis B n σ))).CorepresentableBy
      (nativeSimplexChart B n σ) where
  homEquiv := nativeSimplexChartHomEquiv B n σ _
  homEquiv_comp g f := nativeSimplexChartHomEquiv_natural_right B n σ f g

/-- The original full sharp-edge chart corepresents its whole marked slice Hom functor. -/
def nativeSharpCorepresenter (B : SSet.{u}) (σ : B _⦋1⦌) :
    ((nativeUnstraightening B) ⋙ coyoneda.obj (op (nativeSharpBasis B σ))).CorepresentableBy
      (nativeSharpChart B σ) where
  homEquiv := nativeSharpChartHomEquiv B σ _
  homEquiv_comp g f := nativeSharpChartHomEquiv_natural_right B σ f g

/-- The actual native straightening image of the original minimal simplex is its complete native chart
  through the two original unit mates. -/
def nativeSimplexImageIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    (nativeStraightening B).obj (nativeSimplexBasis B n σ) ≅ nativeSimplexChart B n σ :=
  (nativeImageCorepresenter B (nativeSimplexBasis B n σ)).uniqueUpToIso
    (nativeSimplexCorepresenter B n σ)

/-- The actual native image of the whole maximally marked interval is the original sharp chart through the
  same native mates. -/
def nativeSharpImageIso (B : SSet.{u}) (σ : B _⦋1⦌) :
    (nativeStraightening B).obj (nativeSharpBasis B σ) ≅ nativeSharpChart B σ :=
  (nativeImageCorepresenter B (nativeSharpBasis B σ)).uniqueUpToIso
    (nativeSharpCorepresenter B σ)

/-- The simplex image comparison reads exactly the original chart unit under the actual native adjunction. -/
theorem nativeSimplexImageIso_homEquiv (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    (nativeStraighteningAdjunction B).homEquiv _ _ (nativeSimplexImageIso B n σ).hom =
      nativeSimplexChartHomEquiv B n σ (nativeSimplexChart B n σ) (𝟙 _) := by
  change (nativeStraighteningAdjunction B).homEquiv _ _
    (((nativeStraighteningAdjunction B).homEquiv _ _).symm
      (nativeSimplexChartHomEquiv B n σ (nativeSimplexChart B n σ) (𝟙 _))) = _
  exact ((nativeStraighteningAdjunction B).homEquiv _ _).apply_symm_apply _

/-- The sharp image comparison retains the original sharp chart unit as its exact native mate. -/
theorem nativeSharpImageIso_homEquiv (B : SSet.{u}) (σ : B _⦋1⦌) :
    (nativeStraighteningAdjunction B).homEquiv _ _ (nativeSharpImageIso B σ).hom =
      nativeSharpChartHomEquiv B σ (nativeSharpChart B σ) (𝟙 _) := by
  change (nativeStraighteningAdjunction B).homEquiv _ _
    (((nativeStraighteningAdjunction B).homEquiv _ _).symm
      (nativeSharpChartHomEquiv B σ (nativeSharpChart B σ) (𝟙 _))) = _
  exact ((nativeStraighteningAdjunction B).homEquiv _ _).apply_symm_apply _

end SSet.Marked
