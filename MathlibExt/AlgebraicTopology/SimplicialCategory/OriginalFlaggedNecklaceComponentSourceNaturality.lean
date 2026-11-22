/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceDiagonalComponentAugmentation
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceSourceNaturality

/-!
# SAME full original component-augmentation source naturality

Every original source simplicial map acts on the complete original
flagged-category components. The entire scalar and diagonal augmentation
squares retain the SAME full source functors, original coefficient flags
and original endpoint images, for arbitrary original source maps.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components

variable {K L M : SSet.{u}}

/-- The SAME complete original source map on the actual scalar component simplicial sets. -/
def sourceMap (f : K ⟶ L) (x y : K _⦋0⦌) :
    simplicialSet K x y ⟶ simplicialSet L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) where
  app q := ↾(sourceFunctor f x y q).mapConnectedComponents
  naturality _q _r _θ := by
    apply ConcreteCategory.hom_ext
    intro c
    induction c using Quotient.inductionOn' with
    | h T => rfl

/-- Every SAME original component source map retains the literal original whole source object. -/
theorem sourceMap_mk (f : K ⟶ L) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) (T : Object K x y q) :
    (sourceMap f x y).app q (ConnectedComponents.mk T) = ConnectedComponents.mk (sourceObject f T) := rfl

/-- The SAME complete original source identity acts as the actual component-simplicial-set identity. -/
theorem sourceMap_id (K : SSet.{u}) (x y : K _⦋0⦌) : sourceMap (𝟙 K) x y = 𝟙 (simplicialSet K x y) := by
  ext q c
  induction c using Quotient.inductionOn' with
  | h T => rfl

/-- The SAME complete original source composition retains both original source maps and original labels. -/
theorem sourceMap_comp (f : K ⟶ L) (g : L ⟶ M) (x y : K _⦋0⦌) :
    sourceMap (f ≫ g) x y = sourceMap f x y ≫
      sourceMap g (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) := by
  ext q c
  induction c using Quotient.inductionOn' with
  | h T => rfl

/-- The SAME full original source map on the actual constant-row component diagrams. -/
def constantSourceMap (f : K ⟶ L) (x y : K _⦋0⦌) :
    constantDiagram K x y ⟶ constantDiagram L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) :=
  Functor.whiskerRight (sourceMap f x y) (CategoryTheory.Functor.const SimplexCategoryᵒᵖ)

/-- Both SAME full original scalar augmentation and source maps commute exactly in every arity. -/
theorem augmentation_source (f : K ⟶ L) (x y : K _⦋0⦌) :
    sourceNerveDiagramMap f x y ≫ augmentation L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) =
      augmentation K x y ≫ constantSourceMap f x y := by
  ext q d X
  rfl

/-- The SAME complete original source map on the full original scalar-nerve diagonals. -/
def diagonalSourceMap (f : K ⟶ L) (x y : K _⦋0⦌) :
    diagonal K x y ⟶ diagonal L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) :=
  SSet.simplicialDiagonalFunctor.map (sourceNerveDiagramMap f x y)

/-- Both SAME full original diagonal augmentation and source maps commute with the literal original component map. -/
theorem diagonalProjection_source (f : K ⟶ L) (x y : K _⦋0⦌) :
    diagonalSourceMap f x y ≫ diagonalProjection L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) =
      diagonalProjection K x y ≫ sourceMap f x y := by
  ext q X
  rfl

/-- The SAME full original diagonal source map retains the actual source identity. -/
theorem diagonalSourceMap_id (K : SSet.{u}) (x y : K _⦋0⦌) :
    diagonalSourceMap (𝟙 K) x y = 𝟙 (diagonal K x y) := by
  ext q X
  rfl

/-- The SAME full original diagonal source composition retains both actual original maps. -/
theorem diagonalSourceMap_comp (f : K ⟶ L) (g : L ⟶ M) (x y : K _⦋0⦌) :
    diagonalSourceMap (f ≫ g) x y = diagonalSourceMap f x y ≫
      diagonalSourceMap g (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) := by
  ext q X
  rfl

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components
