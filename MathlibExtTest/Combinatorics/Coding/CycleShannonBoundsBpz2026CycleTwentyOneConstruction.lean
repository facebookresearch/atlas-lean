/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Coding.CycleShannonBoundsBpz2026CycleTwentyOneConstruction

/-!
# Tests for the twenty-one-cycle construction

The constructed code gives the corresponding lower bound on Shannon capacity.

Source: Pjotr Buys, Sven Polak and Jeroen Zuiddam, *Lean-verified lower bounds for the
Shannon capacity of odd cycles*, arXiv:2607.29681v1 (2026).
-/

namespace MathlibExtTest.Combinatorics.Coding.CycleShannonBoundsBpz2026CycleTwentyOneConstruction

open MathlibExt.Combinatorics.Coding.CycleGraphCode
open MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted

example :
    ENNReal.rpow (bpzC21Pi1024.code.toNat : ENNReal) ((4096 : ℝ)⁻¹) ≤
      shannonCapacityCycle 21 :=
  cycleConstruction_implies_lowerBound 21 4096 bpzC21Pi1024.code.toNat (by decide)
    bpz2026CycleTwentyOneConstruction

end MathlibExtTest.Combinatorics.Coding.CycleShannonBoundsBpz2026CycleTwentyOneConstruction
