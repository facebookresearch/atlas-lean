/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Countability

/-!
# Public degree countability and one encoding of the entire simplex family
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.Countability

/-- The original general API covers every degree without a vertex or model premise. -/
theorem degree_countable (X : SSet.{u}) [Countable X.N] (n : ℕ) :
    Countable (X _⦋n⦌) :=
  SSet.countable_obj_of_countable_N X (op ⦋n⦌)

/-- All simplices in all dimensions admit one injective encoding, including empty families. -/
theorem total_encoding (X : SSet.{u}) [Countable X.N] :
    ∃ e : (Σ n : ℕ, X _⦋n⦌) → ℕ, Function.Injective e := by
  have : Countable (Σ n : ℕ, X _⦋n⦌) := SSet.countable_sigma_obj_of_countable_N X
  exact Countable.exists_injective_nat _

end MathlibExtTest.AlgebraicTopology.SimplicialSet.Countability
