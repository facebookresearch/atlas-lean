/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Coding.CycleShannonBoundsBpz2026CycleTwentyOneConstruction

/-!
# The Buys–Polak–Zuiddam lower bound for the twenty-one-cycle

The twenty-one-cycle root-rate bound. It follows from `bpz2026CycleTwentyOneConstruction`, the
authors' code of length `4096` whose size is the code coordinate of the final profile, by
`cycleConstruction_implies_lowerBound`.

Source: Pjotr Buys, Sven Polak and Jeroen Zuiddam,
*Lean-verified lower bounds for the Shannon capacity of odd cycles*, arXiv:2607.29681v1
(2026), for the profiles and the bound; the coset code behind the construction is from the
authors' Lean repository https://github.com/spectra-research/shannon-capacity-lean, revision
aa21eeb12b75b0413d3fa9fb4208b5d0bf2c4d65, `ShannonBounds/BaseC21CosetData.lean` and
`ShannonBounds/CosetC21.lean`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted

open MathlibExt.Combinatorics.Coding.CycleGraphCode

/-- **Buys–Polak–Zuiddam lower bound for the capacity of the 21-cycle.** Let $c$ be the code
coordinate of BPZ's final twenty-one-cycle profile after ten squarings, and let
$M = \max(c, 0)$. Then $M^{1/4096}$ is at most the Shannon capacity of the $21$-cycle, as an
inequality in $[0, \infty]$.

Source: BPZ, arXiv:2607.29681, exact twenty-one-cycle root rate. -/
theorem bpz2026CycleTwentyOneLowerBound :
  ENNReal.rpow (bpzC21Pi1024.code.toNat : ENNReal) ((4096 : ℝ)⁻¹) ≤ shannonCapacityCycle 21
    := by
  exact_mod_cast cycleConstruction_implies_lowerBound 21 4096 _ (by decide)
    bpz2026CycleTwentyOneConstruction

end MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted
