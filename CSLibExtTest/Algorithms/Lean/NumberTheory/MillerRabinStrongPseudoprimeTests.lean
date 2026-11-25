/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.NumberTheory.MillerRabinStrongPseudoprime
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the bridge between Miller–Rabin non-witnesses and strong pseudoprimes

`2047 = 23 · 89` is a strong pseudoprime to base `2`, so `WITNESS(2, 2047)` finds no witness;
conversely `9` is a strong pseudoprime to base `1`, so `WITNESS(1, 9)` finds no witness. The
`1/4` bound is instantiated at `n = 9` (bound `(9 - 1)/4 = 2`).
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MillerRabin

example : (witness 2 2047).ret = false := by
  refine (isStrongPseudoprime_iff_witness_eq_false (by norm_num) (by norm_num) (by decide) 2).1 ?_
  exact_mod_cast MetaMathlibExt.isStrongPseudoprime_2047_two

/-- The converse direction: every odd composite is a strong pseudoprime to base `1`, so `1` is
never a Miller–Rabin witness for it. -/
example : (witness 1 9).ret = false := by
  refine (isStrongPseudoprime_iff_witness_eq_false (by norm_num) (by norm_num) (by decide) 1).1 ?_
  exact_mod_cast MetaMathlibExt.isStrongPseudoprime_one (by norm_num) (by norm_num) (by decide)

open Classical in
example : ((Finset.Ioo 0 9).filter fun a : ℕ =>
    MetaMathlibExt.IsStrongPseudoprime 9 (a : ZMod 9)).card ≤ 2 :=
  card_isStrongPseudoprime_le_quarter (by norm_num) (by norm_num) (by decide)

end Cslib.Algorithms.Lean.MillerRabin
