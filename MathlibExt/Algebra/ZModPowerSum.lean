/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Basic

import Mathlib.FieldTheory.Finite.Basic

/-!
# Power sums over prime fields

We prove that `∑ a : ZMod p, a ^ t` is `-1` when `p - 1` divides the positive exponent `t`
and `0` otherwise.
-/

set_option autoImplicit false

open Finset

namespace MathlibExt.Algebra.PermutationPolynomialsWanted

@[expose] public section

/-- **Power sums over $\mathbb{Z}/p\mathbb{Z}$.** Let $p$ be a prime and $t$ a positive
integer. Then $\sum_{a \in \mathbb{Z}/p\mathbb{Z}} a^t$ equals $-1$ if $p - 1$ divides $t$,
and $0$ otherwise.

Source: Zhiguo Ding and Michael E. Zieve, "Permutation
Polynomials of the Form `∑_{n=1}^k h(n) X^n`", Lemma 1. -/
theorem sum_zmod_pow_eq_ite
    (p t : ℕ) [NeZero p] (hp : p.Prime) (ht : 0 < t) :
    (∑ a : ZMod p, a ^ t) = if (p - 1) ∣ t then -1 else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  classical
  let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x => x, Units.val_injective⟩
  have hmap : univ.map φ = univ \ {0} := by
    ext x
    simp only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton, φ]
    exact isUnit_iff_ne_zero
  calc
    (∑ a : ZMod p, a ^ t) = ∑ a ∈ univ \ {(0 : ZMod p)}, a ^ t := by
      rw [← sum_sdiff ({0} : Finset (ZMod p)).subset_univ, sum_singleton, zero_pow ht.ne',
        add_zero]
    _ = ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ t) := by
      rw [← hmap, sum_map]
      rfl
    _ = if (p - 1) ∣ t then -1 else 0 := by
      rw [FiniteField.sum_pow_units (ZMod p) t, ZMod.card]

end

end MathlibExt.Algebra.PermutationPolynomialsWanted
