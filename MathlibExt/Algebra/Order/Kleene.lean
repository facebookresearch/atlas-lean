/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Kleene

/-!
# Simulation in Kleene algebras

A one-step simulation lifts to Kleene star, without assuming that the
simulator is invertible. As a corollary, an idempotent subidentity absorbed
after one step is also absorbed after arbitrary finite iteration.

These proofs originate in this project's Meta program-verification
development and are reused here with unchanged statements and proof bodies.
That development follows the style of Kozen, *Kleene algebra with tests*,
ACM TOPLAS 19(3), 1997. No PDL or relation-algebra definitions are needed.

See `docs/provenance/kleene/Algebra.lean.txt`, lines 192-215, and the
adjacent `manifest.json` for exact source declarations, origin path/revision
and SHA-256 receipts. These are uncompiled documentation snapshots.
-/

public section

namespace KleeneAlgebra

open scoped Computability

/-- **A one-step simulation lifts to finite iteration.**
A one-step simulation lifts to arbitrary finite iteration.
The simulator `p` need not be invertible or a test. -/
theorem star_simulation {K : Type*} [KleeneAlgebra K] {p a b : K}
    (h : p * a ≤ b * p) : p * a∗ ≤ b∗ * p := by
  have hp : p ≤ b∗ * p := le_mul_of_one_le_left' one_le_kstar
  have hstep : (b∗ * p) * a ≤ b∗ * p := by
    calc
      (b∗ * p) * a = b∗ * (p * a) := mul_assoc _ _ _
      _ ≤ b∗ * (b * p) := mul_right_mono h
      _ = (b∗ * b) * p := (mul_assoc _ _ _).symm
      _ ≤ b∗ * p := mul_left_mono kstar_mul_le_kstar
  exact mul_kstar_le hp hstep

/-- **Tests preserved by one step are preserved by iteration.**
An idempotent subidentity preserved by one step is preserved by
iteration. This is a corollary of `star_simulation`; the test assumptions
are explicit, with no additional algebraic structure. -/
theorem test_star_absorption {K : Type*} [KleeneAlgebra K] {p a : K}
    (hp : p ≤ 1) (hpp : p * p = p) (h : p * a = p * a * p) :
    p * a∗ = p * a∗ * p := by
  have hpa : p * a ≤ a := (mul_left_mono hp).trans_eq (one_mul a)
  have hcomm : p * a ≤ a * p := h.trans_le (mul_left_mono hpa)
  have hle : p * a∗ ≤ p * a∗ * p := by
    calc
      p * a∗ = p * (p * a∗) := by rw [← mul_assoc, hpp]
      _ ≤ p * (a∗ * p) := mul_right_mono (star_simulation hcomm)
      _ = p * a∗ * p := (mul_assoc _ _ _).symm
  exact hle.antisymm ((mul_right_mono hp).trans_eq (mul_one _))

end KleeneAlgebra
