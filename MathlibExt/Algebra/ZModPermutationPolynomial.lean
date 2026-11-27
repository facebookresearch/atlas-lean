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
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.FieldTheory.Finite.Basic

/-!
# Permutation polynomials over prime fields

We prove that the sum of `n ^ t * c ^ n` over `1 ≤ n ≤ k` induces the identity on
`ZMod p` under the congruences of the permutation polynomial theorem.
-/

set_option autoImplicit false

open Finset

namespace MathlibExt.Algebra.PermutationPolynomialsWanted

private theorem sum_range_blocks {p : ℕ} [Fact p.Prime] (t m : ℕ) (c : ZMod p) :
    (∑ n ∈ range (p * m), (n : ZMod p) ^ t * c ^ n) =
      (∑ i ∈ range m, c ^ i) * ∑ j ∈ range p, (j : ZMod p) ^ t * c ^ j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ (fun i => c ^ i), add_mul,
      mul_sum _ _ (c ^ m)]
    congr 1
    apply sum_congr rfl
    intro j _
    simp [Nat.cast_add, Nat.cast_mul, pow_add, pow_mul, mul_left_comm]

private theorem sum_range_pow_eq_zero {p t : ℕ} [Fact p.Prime]
    (ht : 0 < t) (hndvd : ¬(p - 1) ∣ t) : (∑ n ∈ range p, (n : ZMod p) ^ t) = 0 := by
  have hrem : t % (p - 1) ≠ 0 := fun h => hndvd (Nat.dvd_of_mod_eq_zero h)
  have hp : p.Prime := Fact.out
  calc
    (∑ n ∈ range p, (n : ZMod p) ^ t) = ∑ x : ZMod p, x ^ t := by
      refine sum_nbij' (fun n : ℕ => (n : ZMod p)) ZMod.val (by simp) ?_ ?_ ?_ (by simp)
      · exact fun x _ => mem_range.2 x.val_lt
      · exact fun n hn => ZMod.val_natCast_of_lt (mem_range.1 hn)
      · exact fun x _ => x.natCast_zmod_val
    _ = ∑ x : ZMod p, x ^ (t % (p - 1)) := by
      apply sum_congr rfl
      intro x _
      by_cases hx : x = 0
      · simp [hx, ht.ne', hrem]
      · exact pow_eq_pow_of_modEq (Nat.mod_modEq t (p - 1)).symm
          (ZMod.pow_card_sub_one_eq_one hx)
    _ = 0 := FiniteField.sum_pow_lt_card_sub_one _ _ (by
      rw [ZMod.card]
      exact Nat.mod_lt _ (Nat.sub_pos_of_lt hp.one_lt))

@[expose] public section

/-- **Permutation polynomials $\sum_{n=1}^k n^t X^n$ over $\mathbb{F}_p$.** Let $p$ be an
odd prime and let $k$ and $t$ be positive integers with $k \equiv 1 \pmod{p(p-1)}$.
Suppose that $k \equiv 1 \pmod{p^2}$ or that $p - 1$ does not divide $t$. Then the map
$c \mapsto \sum_{n=1}^{k} n^t c^n$ is a bijection from $\mathbb{Z}/p\mathbb{Z}$ to itself.

Ding and Zieve quote this result from an earlier paper.

Source: Zhiguo Ding and Michael E. Zieve, "Permutation
Polynomials of the Form `∑_{n=1}^k h(n) X^n`", Theorem 1. -/
theorem bijective_sum_pow_mul_pow_zmod
    (p k t : ℕ) (hp : p.Prime) (hpodd : p % 2 = 1)
    (hk : 0 < k) (ht : 0 < t)
    (hkcong : k % (p * (p - 1)) = 1)
    (hcases : k % (p ^ 2) = 1 ∨ ¬(p - 1) ∣ t) :
    Function.Bijective
      (fun c : ZMod p =>
        ∑ n ∈ Finset.Icc 1 k, (n : ZMod p) ^ t * c ^ n) := by
  let : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := by omega
  let m := (p - 1) * (k / (p * (p - 1)))
  have hk' : k = p * m + 1 := by
    simpa only [m, Nat.mul_assoc, hkcong] using (Nat.div_add_mod k (p * (p - 1))).symm
  suffices h : (fun c : ZMod p => ∑ n ∈ Icc 1 k, (n : ZMod p) ^ t * c ^ n) = id by
    rw [h]
    exact Function.bijective_id
  funext c
  change (∑ n ∈ Icc 1 k, (n : ZMod p) ^ t * c ^ n) = c
  by_cases hc : c = 0
  · subst c
    exact sum_eq_zero fun n hn => by
      rw [zero_pow (Nat.ne_of_gt (mem_Icc.1 hn).1), mul_zero]
  have hpow : c ^ m = 1 := by
    simp only [m, pow_mul, ZMod.pow_card_sub_one_eq_one hc, one_pow]
  -- The last term is c and the term at p * m vanishes.
  -- The remaining terms form m full blocks of length p.
  let f (n : ℕ) := (n : ZMod p) ^ t * c ^ n
  have hf0 : f 0 = 0 := by simp [f, ht.ne']
  have hboundary : f (p * m) = 0 := by simp [f, Nat.cast_mul, ht.ne']
  have hlast : f k = c := by
    rw [hk']
    simp [f, Nat.cast_add, Nat.cast_mul, pow_add, pow_mul, hpow]
  have hprefix : (∑ n ∈ range (p * m), f n) = 0 := by
    change (∑ n ∈ range (p * m), (n : ZMod p) ^ t * c ^ n) = 0
    rw [sum_range_blocks]
    by_cases hc1 : c = 1
    · simp only [hc1, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
      rcases hcases with hk₂ | ht'
      · have hdecomp : p ^ 2 * (k / p ^ 2) + 1 = k := by
          rw [← hk₂]
          exact Nat.div_add_mod k (p ^ 2)
        have hdiv : p * p ∣ p * m :=
          ⟨k / p ^ 2, by
            rw [← pow_two]
            exact Nat.add_right_cancel (hk'.symm.trans hdecomp.symm)⟩
        have hm : (m : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff m p).2 (Nat.dvd_of_mul_dvd_mul_left hp0 hdiv)
        rw [hm, zero_mul]
      · rw [sum_range_pow_eq_zero ht ht', mul_zero]
    · have hgeom : (∑ i ∈ range m, c ^ i) = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_right (sub_ne_zero.mpr hc1)
        rw [geom_sum_mul, hpow, sub_self]
      rw [hgeom, zero_mul]
  calc
    (∑ n ∈ Icc 1 k, f n) = ∑ n ∈ range (k + 1), f n := by
      rw [sum_range_eq_add_Ico f (n := k + 1) (Nat.lt_succ_of_lt hk),
        Ico_add_one_right_eq_Icc, hf0, zero_add]
    _ = (∑ n ∈ range (p * m), f n) + c := by
      rw [sum_range_succ f k, hlast, hk', sum_range_succ f (p * m), hboundary, add_zero]
    _ = c := by rw [hprefix, zero_add]

end

end MathlibExt.Algebra.PermutationPolynomialsWanted
