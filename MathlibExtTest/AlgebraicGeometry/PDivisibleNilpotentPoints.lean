/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.PDivisibleTangentTests
import Mathlib.Algebra.Field.ZMod

/-! A nontrivial mu_2 point on a genuine square-zero test ring reduces
  to the identity on its field quotient. These are the infinitesimal
  points which the formal Lie/crystalline interface must retain.
-/

open MathlibExt.AlgebraicGeometry.PDivisibleTangentTests
open CategoryTheory _root_.AlgebraicGeometry

noncomputable section

private abbrev test : Test 2 (ZMod 2) where
  algebra := CommAlgCat.of (ZMod 2) (ZMod 2)
  module := ModuleCat.of (ZMod 2) (ZMod 2)
  nilpotent := ⟨1, by decide⟩

private def epsilon : Extension 2 (ZMod 2) test :=
  TrivSqZeroExt.inr (1 : ZMod 2)

private instance : DecidableEq (Extension 2 (ZMod 2) test) :=
  inferInstanceAs (DecidableEq (ZMod 2 × ZMod 2))

example : epsilon ≠ 0 := by decide
example : epsilon ^ 2 = 0 := by decide
example : (1 + epsilon) ^ 2 = 1 := by decide
example : 1 + epsilon ≠ 1 := by decide

example : (TrivSqZeroExt.fstHom (ZMod 2) test.algebra test.module)
    (1 + epsilon) = 1 := rfl
