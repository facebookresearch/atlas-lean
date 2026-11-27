/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ClassTranspositionProductOrdersKourovka18Problem48
import Mathlib.Tactic.SplitIfs

namespace MathlibExtTest.GroupTheory.ClassTranspositionProductOrdersKourovka18Problem48

open MathlibExt.GroupTheory.ClassTranspositionProductOrdersKourovka18Problem48Wanted

private def slantedFn (x : ℤ) : ℤ :=
  if x % 2 = 0 then 1 + 4 * (x / 2) else if x % 4 = 1 then 2 * (x / 4) else x

private theorem slanted_involutive : Function.Involutive slantedFn := by
  intro x
  unfold slantedFn
  split_ifs <;> omega

private def slanted : Equiv.Perm ℤ :=
  ⟨slantedFn, slantedFn, slanted_involutive, slanted_involutive⟩

private theorem slanted_spec : IsClassTrans slanted 0 2 1 4 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro x hx hy
    change x % 2 = 0 % 2 at hx
    change x % 4 = 1 % 4 at hy
    omega
  · intro k
    change slantedFn (0 + k * 2) = 1 + k * 4 ∧ slantedFn (1 + k * 4) = 0 + k * 2
    constructor <;> unfold slantedFn <;> split_ifs <;> omega
  · intro x hx hy
    change ¬ x % 2 = 0 % 2 at hx
    change ¬ x % 4 = 1 % 4 at hy
    change slantedFn x = x
    unfold slantedFn
    split_ifs <;> omega

private def orders : Set ℕ :=
  {k | 0 < k ∧ ∃ σ τ : Equiv.Perm ℤ, IsClassTransposition σ ∧ IsClassTransposition τ ∧
    orderOf (σ * τ) = k}

example : orders.Finite := classTranspositionProductOrdersFinite_holds

-- A slanted class transposition composed with itself realizes order one.
example : 1 ∈ orders := by
  have hs : IsClassTransposition slanted := ⟨0, 2, 1, 4, slanted_spec⟩
  refine ⟨by decide, slanted, slanted, hs, hs, ?_⟩
  have h : slanted * slanted = 1 := Equiv.ext slanted_involutive
  rw [h, orderOf_one]

private def parityFn (x : ℤ) : ℤ := if x % 2 = 0 then x + 1 else x - 1

private theorem parity_involutive : Function.Involutive parityFn := by
  intro x
  unfold parityFn
  split_ifs <;> omega

private def paritySwap : Equiv.Perm ℤ :=
  ⟨parityFn, parityFn, parity_involutive, parity_involutive⟩

private theorem parity_spec : IsClassTrans paritySwap 0 2 1 2 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro x hx hy
    change x % 2 = 0 % 2 at hx
    change x % 2 = 1 % 2 at hy
    omega
  · intro k
    change parityFn (0 + k * 2) = 1 + k * 2 ∧ parityFn (1 + k * 2) = 0 + k * 2
    constructor <;> unfold parityFn <;> split_ifs <;> omega
  · intro x hx hy
    change ¬ x % 2 = 0 % 2 at hx
    change ¬ x % 2 = 1 % 2 at hy
    omega

private theorem product_apply (k : ℤ) :
    (slanted * paritySwap) (1 + 2 * k) = 1 + 2 * (2 * k) := by
  change slantedFn (parityFn (1 + 2 * k)) = _
  unfold slantedFn parityFn
  split_ifs <;> omega

private theorem product_pow_apply (n : ℕ) :
    ((slanted * paritySwap) ^ n) 3 = 1 + 2 * (2 : ℤ) ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, product_apply, pow_succ']

-- Both factors are class transpositions and their product has an unbounded orbit.
example : ∃ σ τ : Equiv.Perm ℤ, IsClassTransposition σ ∧ IsClassTransposition τ ∧
    orderOf (σ * τ) = 0 := by
  refine ⟨slanted, paritySwap, ⟨0, 2, 1, 4, slanted_spec⟩, ⟨0, 2, 1, 2, parity_spec⟩, ?_⟩
  by_contra hn
  have h := product_pow_apply (orderOf (slanted * paritySwap))
  rw [pow_orderOf_eq_one, Equiv.Perm.one_apply] at h
  have := one_lt_pow₀ (show (1 : ℤ) < 2 by decide) hn
  omega

example : 0 ∉ orders := fun h => Nat.lt_irrefl _ h.1

end MathlibExtTest.GroupTheory.ClassTranspositionProductOrdersKourovka18Problem48
