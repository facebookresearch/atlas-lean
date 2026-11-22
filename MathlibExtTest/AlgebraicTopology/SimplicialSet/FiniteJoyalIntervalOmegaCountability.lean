/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaCountability

/-!
# Encoding every nondegenerate simplex of the actual omega output
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaCountability

/-- The full chosen output admits one injective natural-number encoding,
with no added assumption on any stage or on fibrancy. -/
theorem output_encoding (X : SSet.{u}) [Countable X.N] :
    ∃ e : (SSet.joyalInterval.auxiliaryOmegaFreeFiller.{u}.obj X).N → ℕ,
      Function.Injective e := by
  have : Countable (SSet.joyalInterval.auxiliaryOmegaFreeFiller.{u}.obj X).N :=
    SSet.joyalInterval.auxiliaryOmegaFreeFiller_countable_N X
  exact Countable.exists_injective_nat _

end MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaCountability
