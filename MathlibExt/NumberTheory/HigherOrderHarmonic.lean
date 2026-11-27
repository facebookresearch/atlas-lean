/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Field.Rat

@[expose] public section

/-- **Higher-order harmonic numbers.** For natural numbers $n$ and $r$, the harmonic number of
order $r$ is the rational number $H_n^{(r)} = \sum_{k=1}^{n} 1/k^r$. -/
def higherHarmonic (n r : Nat) : Rat :=
  ∑ k ∈ Finset.Icc 1 n, (1 : Rat) / ((k : Rat) ^ r)

theorem higherHarmonic_zero (r : Nat) : higherHarmonic 0 r = 0 := by
  unfold higherHarmonic
  simp

theorem higherHarmonic_succ (n r : Nat) :
    higherHarmonic (n + 1) r =
      higherHarmonic n r + (1 : Rat) / ((((n + 1 : Nat)) : Rat) ^ r) := by
  unfold higherHarmonic
  rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n))]

theorem higherHarmonic_one (r : Nat) : higherHarmonic 1 r = 1 := by
  unfold higherHarmonic
  rw [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, one_pow, div_one]

theorem higherHarmonic_order_one (n : Nat) : higherHarmonic n 1 = harmonic n := by
  induction n with
  | zero => simp [higherHarmonic, harmonic]
  | succ n ih =>
    rw [higherHarmonic_succ, ih, harmonic_succ, pow_one, one_div]

end
