/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.Amortized.Framework
public import CSLibExt.Algorithms.Lean.DataStructures.Amortized.Unary

/-!
# Amortized framework regression tests

A tiny concrete unary instance (`countUp`: each step costs 1, potential
is the counter) exercises the unary framework's state evolution and the
`unary_aeq` / `unary_ub` bounds. The generic rose-tree framework's main
statements are checked for availability.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Amortized.FrameworkTests

open Amortized

/-- Count up: `nxt` increments, actual cost `1`, potential is the counter,
bound `2`. -/
def countUp : UnaryAmortized Unit ℕ where
  init := 0
  nxt := fun _ s => s + 1
  inv := fun _ => True
  T := fun _ _ => 1
  Phi := fun s => (s : ℝ)
  U := fun _ _ => 2
  inv_init := trivial
  inv_nxt := fun _ => trivial
  ppos := fun _ => Nat.cast_nonneg _
  p0 := Nat.cast_zero
  U_bound := by
    intro f s _
    push_cast
    linarith

example : unaryState countUp (fun _ => ()) 3 = 3 := rfl

example : countUp.Phi (unaryState countUp (fun _ => ()) 2) = 2 := by
  simp [countUp, unaryState]

example (n : ℕ) :
    (∑ i ∈ Finset.range n,
      countUp.T ((fun _ => ()) i) (unaryState countUp (fun _ => ()) i)) ≤
    (∑ i ∈ Finset.range n,
      countUp.U ((fun _ => ()) i) (unaryState countUp (fun _ => ()) i)) :=
  unary_ub countUp _ n

example :
    (∑ i ∈ Finset.range 2,
      countUp.T ((fun _ => ()) i) (unaryState countUp (fun _ => ()) i)) =
    (∑ i ∈ Finset.range 2, unaryA countUp (fun _ => ()) i) -
      countUp.Phi (unaryState countUp (fun _ => ()) 2) :=
  unary_aeq countUp _ 2

#check @t_sum_a_sum
#check @t_sum_le_U_sum
#check @amortizedTransfer

end Cslib.Algorithms.Lean.Amortized.FrameworkTests
