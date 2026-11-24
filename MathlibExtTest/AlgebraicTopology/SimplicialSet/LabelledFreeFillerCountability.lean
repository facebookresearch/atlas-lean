/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.LabelledFreeFillerCountability

/-!
# Encoding the full nondegenerate simplex set after labelled attachment
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.LabelledFreeFillerCountability

/-- All output nondegenerate simplices admit one injective natural-number encoding,
for an arbitrary countable arrow family with finite domains and countable targets. -/
theorem output_encoding (I : Type u) [Countable I] (K D : I → SSet.{u})
    (j : ∀ i, K i ⟶ D i) [∀ i, (K i).Finite] [∀ i, Countable (D i).N]
    (X : SSet.{u}) [Countable X.N] :
    ∃ e : ((SSet.labelledFreeFiller j).obj X).N → ℕ, Function.Injective e := by
  have : Countable ((SSet.labelledFreeFiller j).obj X).N :=
    SSet.labelledFreeFiller.countable_N j X
  exact Countable.exists_injective_nat _

end MathlibExtTest.AlgebraicTopology.SimplicialSet.LabelledFreeFillerCountability
