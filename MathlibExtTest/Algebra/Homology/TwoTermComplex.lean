/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.TwoTermComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic

@[expose] public section

/-!
# Tests for the two-term cochain complex

The arrow sits in degrees zero and one; every later term is zero and so is
the differential out of degree one.
-/

open CategoryTheory CategoryTheory.Limits ZeroObject
open MathlibExt.Algebra.Homology

namespace MathlibExtTest.Algebra.Homology

variable {A B : ModuleCat.{0} ℤ} (f : A ⟶ B)

example : (twoTermComplex f).X 0 = A := rfl

example : (twoTermComplex f).X 1 = B := rfl

example : (twoTermComplex f).d 0 1 = f := twoTermComplex_d_zero f

example : IsZero ((twoTermComplex f).X 2) := isZero_zero _

example : (twoTermComplex f).d 1 2 = 0 := by
  dsimp [twoTermComplex]
  apply CochainComplex.of_d

end MathlibExtTest.Algebra.Homology
