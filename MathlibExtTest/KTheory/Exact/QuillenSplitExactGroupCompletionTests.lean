/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.KTheory.Exact.Quillen.SplitExactGroupCompletion

/-! # Tests for projective S⁻¹S components -/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicKTheory.QuillenSplitExactGroupCompletionTests

open AlgebraicKTheory

variable (R : Type u) [Ring R]

example :
    ConnectedComponents
        (SInverseS.Pair (FGProjectiveCat.{u} R)) ≃
      RingK0 R :=
  RingK0.sInverseSComponentsEquiv R

end AlgebraicKTheory.QuillenSplitExactGroupCompletionTests
