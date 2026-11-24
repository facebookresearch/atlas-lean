/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EquivariantDerivedObstructionModels
public import MathlibExt.AlgebraicGeometry.FixedDerivedObstructionMaps

/-!
# Compatible native action and fixed-component cotangent diagrams

The original and relative models are chosen together with all actual
fixed-component models. Every square uses the same original model and
the full source polynomial-resolution normalization in every negative
degree. This construction imposes no globally strict action on an
arbitrary preselected target complex.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.EquivariantCotangentDiagramModels

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonObj
open AlgebraicWeightBundleModels TorusFixedSchemeModels GlobalObstructionMorphisms
open GlobalPerfectObstructionTheory
open EquivariantDerivedObstructionModels FixedDerivedObstructionMaps GlobalCotangentSquareMaps

/-- Every actual square shares the same source-compatible original normalization. -/
structure CotangentDiagram (X : Over base) [ModObj Gm X]
    (F : FixedSchemeModel Gm X) (Z : FixedComponents Gm X F) where
  original : CotangentNormalization X.hom
  action : CotangentActionData X original
  fixed : ∀ j : Fin Z.count, CotangentNormalization (Z.component j).data.scheme.hom
  square : ∀ j : Fin Z.count,
    SquareMap (fixedSquare ((Z.component j).toAmbient Gm X)) original (fixed j)

end MathlibExt.AlgebraicGeometry.EquivariantCotangentDiagramModels
