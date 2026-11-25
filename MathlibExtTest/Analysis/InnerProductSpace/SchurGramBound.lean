/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.SchurGramBound

set_option autoImplicit false

/-!
# Tests for the Schur-multiplier Gram bound

Two-point instantiation of `norm_hadamard_gram_factor_le` and `keyEstimate`,
plus axiom checks.
-/

open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open MathlibExt.Analysis.InnerProductSpace.SchurGramBound

namespace MathlibExtTest.SchurGramBound

/-- Identity test matrix on two points. -/
def testA : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]

/-- First test vector family on two points. -/
def testU : Fin 2 → ℂ := ![1, 1]

/-- Second test vector family on two points. -/
def testV : Fin 2 → ℂ := ![1, -1]

/-- Test family for the key estimate on two points. -/
def testZ : Fin 2 → ℂ := ![1, 0]

/-- The Schur-Gram bound instantiated on two points. -/
example : ‖testA ⊙ Matrix.of (fun x y => inner ℂ (testU x) (testV y))‖ ≤
    ‖testA‖ * (⨆ x, ‖testU x‖) * (⨆ y, ‖testV y‖) :=
  norm_hadamard_gram_factor_le testA testU testV

/-- The key estimate instantiated on two points. -/
example : ∑ x, ‖∑ y, testA x y • testZ y‖ ^ 2 ≤ ‖testA‖ ^ 2 * ∑ y, ‖testZ y‖ ^ 2 :=
  keyEstimate testA testZ

#print axioms norm_hadamard_gram_factor_le
#print axioms keyEstimate

end MathlibExtTest.SchurGramBound
