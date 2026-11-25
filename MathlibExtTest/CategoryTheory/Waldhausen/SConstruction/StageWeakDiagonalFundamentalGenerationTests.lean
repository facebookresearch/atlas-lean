/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalFundamentalGeneration

/-!
# Weak-diagonal fundamental-group generation tests

These tests pin connector normalization, inverse/composition orientation,
E3 edge specialization, `hom_rec` subgroup membership, and generation at the
zero vertex.  They make no commutativity, K-zero relation, encode/decode,
realization, loop-space, approximation, spectrum, or Q/S claim.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageWeakDiagonalFundamentalGenerationTests

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

example : Type (max u v) := stageWeakDiagonalFundamentalGroup C

example (A : C) : stageWeakDiagonalFundamentalGroup C :=
  stageWeakDiagonalObjectGenerator C A

example : Subgroup (stageWeakDiagonalFundamentalGroup C) :=
  stageWeakDiagonalObjectGeneratorSubgroup C

example (A : C) :
    stageWeakDiagonalObjectGenerator C A ∈
      stageWeakDiagonalObjectGeneratorSubgroup C :=
  stageWeakDiagonalObjectGenerator_mem C A

example (p : SSet.FundamentalGroupoid (stageWeakDiagonal C)) :
    SSet.FundamentalGroupoid.mk (stageWeakDiagonalZeroVertex C) ⟶ p :=
  stageWeakDiagonalConnectorHom C p

example :
    stageWeakDiagonalConnectorHom C
        (SSet.FundamentalGroupoid.mk (stageWeakDiagonalZeroVertex C)) =
      𝟙 _ :=
  stageWeakDiagonalConnectorHom_zero C

example (f : stageWeakDiagonalFundamentalGroup C) :
    stageWeakDiagonalNormalizedHom C f.asHom = f :=
  stageWeakDiagonalNormalizedHom_end C f

example {p q : SSet.FundamentalGroupoid (stageWeakDiagonal C)}
    (f : p ⟶ q) :
    stageWeakDiagonalNormalizedHom C (inv f) =
      (stageWeakDiagonalNormalizedHom C f)⁻¹ :=
  stageWeakDiagonalNormalizedHom_inv C f

example {p q r : SSet.FundamentalGroupoid (stageWeakDiagonal C)}
    (f : p ⟶ q) (g : q ⟶ r) :
    stageWeakDiagonalNormalizedHom C (f ≫ g) =
      stageWeakDiagonalNormalizedHom C g *
        stageWeakDiagonalNormalizedHom C f :=
  stageWeakDiagonalNormalizedHom_comp C f g

example {x y : (stageWeakDiagonal C).obj (op ⦋0⦌)}
    (e : (stageWeakDiagonal C).Edge x y) :
    stageWeakDiagonalNormalizedHom C
        (SSet.FundamentalGroupoid.homMk e) =
      stageWeakDiagonalObjectGenerator C
        ((stageOneEval C).obj (ComposableArrows.left e.edge).obj) :=
  stageWeakDiagonalNormalizedHom_homMk C e

example {p q : SSet.FundamentalGroupoid (stageWeakDiagonal C)}
    (f : p ⟶ q) :
    stageWeakDiagonalNormalizedHom C f ∈
      stageWeakDiagonalObjectGeneratorSubgroup C :=
  stageWeakDiagonalNormalizedHom_mem C f

example (f : stageWeakDiagonalFundamentalGroup C) :
    f ∈ stageWeakDiagonalObjectGeneratorSubgroup C :=
  stageWeakDiagonalFundamentalGroup_mem_objectGenerators C f

example : stageWeakDiagonalObjectGeneratorSubgroup C = ⊤ :=
  stageWeakDiagonalObjectGeneratorSubgroup_eq_top C

end StageWeakDiagonalFundamentalGenerationTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction

end
