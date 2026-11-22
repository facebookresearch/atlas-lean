/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceComponentProjectionWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceScalarDiagram
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveDiscreteIso

/-!
# SAME original full scalar component augmentation

The actual original scalar functors give the simplicial set of genuine
flagged-category components. The full native scalar-nerve diagram maps
to its constant-row component diagram by the SAME original projection.
Every original face, degeneracy and complete native chain is retained,
and every component map is genuinely weak.
-/

noncomputable section

universe u

open CategoryTheory Opposite MorphismProperty
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components

/-- The SAME genuine original category components, with all original scalar maps. -/
def simplicialSet (K : SSet.{u}) (x y : K _⦋0⦌) : SSet.{u} where
  obj q := ConnectedComponents (Object K x y q)
  map θ := ↾(scalarFunctor K x y θ).mapConnectedComponents
  map_id q := by
    apply ConcreteCategory.hom_ext
    intro c
    induction c using Quotient.inductionOn' with
    | h T => rfl
  map_comp θ ψ := by
    apply ConcreteCategory.hom_ext
    intro c
    induction c using Quotient.inductionOn' with
    | h T => rfl

/-- The actual constant-row diagram on the SAME original scalar component sets. -/
def constantDiagram (K : SSet.{u}) (x y : K _⦋0⦌) : SimplicialObject SSet.{u} :=
  simplicialSet K x y ⋙ CategoryTheory.Functor.const SimplexCategoryᵒᵖ

/-- The SAME complete original scalar component augmentation, with the canonical discrete-nerve inverse. -/
def augmentation (K : SSet.{u}) (x y : K _⦋0⦌) : scalarNerveDiagram K x y ⟶ constantDiagram K x y where
  app q := projection K x y q ≫ (SSet.nerveDiscreteIso (ConnectedComponents (Object K x y q))).hom
  naturality _q _r _θ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro X
    rfl

/-- Every original scalar component is the SAME whole native component projection. -/
theorem augmentation_app (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    (augmentation K x y).app q = projection K x y q ≫
      (SSet.nerveDiscreteIso (ConnectedComponents (Object K x y q))).hom := rfl

/-- Every entire original native chain retains its literal first object's SAME original component. -/
theorem augmentation_app_chain (K : SSet.{u}) (x y : K _⦋0⦌) (q d : SimplexCategoryᵒᵖ)
    (X : (nerve (Object K x y q)).obj d) :
    ((augmentation K x y).app q).app d X = ConnectedComponents.mk (X.obj 0) := rfl

/-- The SAME complete original scalar augmentation is genuinely weak in EVERY original scalar degree. -/
theorem augmentation_app_weak (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    SSet.realizationWeakEquivalences ((augmentation K x y).app q) :=
  RespectsIso.postcomp SSet.realizationWeakEquivalences
    (SSet.nerveDiscreteIso (ConnectedComponents (Object K x y q))).hom (projection K x y q)
    (projection_weak K x y q)

/-- The SAME original scalar component map retains the full original scalar-object readback. -/
theorem simplicialSet_map_mk (K : SSet.{u}) (x y : K _⦋0⦌) {q r : SimplexCategoryᵒᵖ}
    (θ : q ⟶ r) (T : Object K x y q) :
    (simplicialSet K x y).map θ (ConnectedComponents.mk T) =
      ConnectedComponents.mk (scalarObject θ T) := rfl

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components
