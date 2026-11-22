/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.EndOfTheLine
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

open MathlibExt.Computability.EndOfTheLine

namespace MathlibExtTest.Computability.EndOfTheLine

/-- A line `0 → 1 → 2` on `Fin 3`: successor candidate. -/
def S : Fin 3 → Fin 3 := ![1, 2, 2]

/-- Predecessor candidate for the line `0 → 1 → 2`. -/
def P : Fin 3 → Fin 3 := ![0, 0, 1]

/-- Non-vacuity: the hypotheses `P 0 = 0 ≠ S 0` hold. -/
example : P 0 = 0 ∧ S 0 ≠ 0 := by decide

/-- The edges of the instance are `0 → 1` and `1 → 2`. -/
example : Adj S P 0 1 ∧ Adj S P 1 2 ∧ ¬ Adj S P 2 2 := by decide

/-- The end of the line `2` is a sink, as `exists_sink` predicts. -/
example : ∀ y, ¬ Adj S P 2 y := forall_not_adj_iff.mpr (by decide)

example : ∃ x, ∀ y, ¬ Adj S P x y := exists_sink S P 0 (by decide) (by decide)

end MathlibExtTest.Computability.EndOfTheLine
