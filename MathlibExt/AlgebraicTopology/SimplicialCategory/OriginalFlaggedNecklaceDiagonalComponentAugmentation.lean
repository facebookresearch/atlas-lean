/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceScalarComponentAugmentation
import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialDiagonalWeakEquivalence

/-!
# Genuine SAME original full flagged diagonal augmentation

The entire original scalar flagged-nerve diagram maps weakly to the
simplicial set of its SAME actual category components. The original
levelwise weak component projections and the existing genuine diagonal
theorem prove weakness, with every original scalar degree retained.
The component simplicial set is not identified with the raw coherent
Hom quotient here.
-/

noncomputable section

universe u

open CategoryTheory Opposite MorphismProperty
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components

/-- The SAME full original scalar-nerve diagonal. -/
def diagonal (K : SSet.{u}) (x y : K _⦋0⦌) : SSet.{u} :=
  SSet.simplicialDiagonalFunctor.obj (scalarNerveDiagram K x y)

/-- Both entire original constant-row diagonal maps are the SAME literal component maps. -/
def constantDiagonalIso (K : SSet.{u}) (x y : K _⦋0⦌) :
    SSet.simplicialDiagonalFunctor.obj (constantDiagram K x y) ≅ simplicialSet K x y :=
  NatIso.ofComponents (fun q => Iso.refl _) (by
    intro q r θ
    apply ConcreteCategory.hom_ext
    intro c
    rfl)

/-- The SAME actual original full diagonal augmentation with its canonical constant-row readback. -/
def diagonalProjection (K : SSet.{u}) (x y : K _⦋0⦌) : diagonal K x y ⟶ simplicialSet K x y :=
  SSet.simplicialDiagonalFunctor.map (augmentation K x y) ≫ (constantDiagonalIso K x y).hom

/-- The SAME entire original flagged diagonal projection is genuinely weak for EVERY original simplicial input. -/
theorem diagonalProjection_weak (K : SSet.{u}) (x y : K _⦋0⦌) :
    SSet.realizationWeakEquivalences (diagonalProjection K x y) := by
  have h : SSet.realizationWeakEquivalences (SSet.simplicialDiagonalFunctor.map (augmentation K x y)) :=
    SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences (augmentation K x y)
      (fun n => augmentation_app_weak K x y (op ⦋n⦌))
  exact RespectsIso.postcomp SSet.realizationWeakEquivalences (constantDiagonalIso K x y).hom
    (SSet.simplicialDiagonalFunctor.map (augmentation K x y)) h

/-- EVERY actual original full diagonal chain retains the SAME original first-object component label. -/
theorem diagonalProjection_app (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ)
    (X : (nerve (Object K x y q)).obj q) :
    (diagonalProjection K x y).app q X = ConnectedComponents.mk (X.obj 0) := rfl

/-- The SAME actual inverse constant-row chart retains EVERY original scalar component. -/
theorem constantDiagonalIso_inv_app (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ)
    (c : ConnectedComponents (Object K x y q)) : (constantDiagonalIso K x y).inv.app q c = c := rfl

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components
