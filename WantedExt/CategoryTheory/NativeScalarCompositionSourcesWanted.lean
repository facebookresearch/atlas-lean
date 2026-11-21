/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.CategoryTheory.NativeScalarCompositionSources

/-!
# Direct original scalar-composition source requests

All identifications are normalized on every original native module
and section. They identify actual scalar functors and actual degree-zero
cochains; no higher comparison isomorphism is a field.

Source: native Mathlib, Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

@[expose] public noncomputable section

namespace WantedExt.CategoryTheory.NativeScalarCompositionSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations
open MathlibExt.CategoryTheory.NativeScalarCompositionSources

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [UnivLE.{max u v, 1}] [HasSheafify J AddCommGrpCat.{1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{1}]
  (R₀ R₁ R₂ : Sheaf J CommRingCat.{1}) (a : R₀ ⟶ R₁) (b : R₁ ⟶ R₂)
  [(pushforward (𝟭 C) R₀ R₁ a).IsRightAdjoint]
  [(pushforward (𝟭 C) R₁ R₂ b).IsRightAdjoint]
  [(pushforward (𝟭 C) R₀ R₂ (a ≫ b)).IsRightAdjoint]

public def_wanted originalScalarComposition : CompositionSource R₀ R₁ R₂ a b

variable (R O : Sheaf J CommRingCat.{1}) (eta : R ⟶ O)

public def_wanted originalIdentityRestriction : IdentityRestrictionSource O

public def_wanted originalSingleRestriction : SingleRestrictionSource R O eta

end WantedExt.CategoryTheory.NativeScalarCompositionSources
