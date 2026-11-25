/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic
import MathlibExt.Combinatorics.Enumerative.StirlingSecondExplicit
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace MetaMathlibExt

private theorem rising_eq (n : ℕ) (y : ℝ) :
    ∏ i ∈ Finset.range n, (y + (i : ℝ)) =
      ∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n k : ℝ) * y ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h0 : Nat.stirlingFirst (n + 1) 0 = 0 := Nat.stirlingFirst_succ_zero n
    have hU : ∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n (k + 1) : ℝ) * y ^ (k + 1)
        = (∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n k : ℝ) * y ^ k)
          - (Nat.stirlingFirst n 0 : ℝ) := by
      have hS : (∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n k : ℝ) * y ^ k)
          = (∑ k ∈ Finset.range n, (Nat.stirlingFirst n (k + 1) : ℝ) * y ^ (k + 1))
            + (Nat.stirlingFirst n 0 : ℝ) := by
        rw [Finset.sum_range_succ' (fun k => (Nat.stirlingFirst n k : ℝ) * y ^ k) n]
        simp only [pow_zero, mul_one]
      have htop : (∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n (k + 1) : ℝ) * y ^ (k + 1))
          = (∑ k ∈ Finset.range n, (Nat.stirlingFirst n (k + 1) : ℝ) * y ^ (k + 1)) := by
        rw [Finset.sum_range_succ]
        have hz : (Nat.stirlingFirst n (n + 1) : ℝ) * y ^ (n + 1) = 0 := by
          have hz' : Nat.stirlingFirst n (n + 1) = 0 :=
            Nat.stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self n)
          rw [hz', Nat.cast_zero, zero_mul]
        rw [hz, add_zero]
      rw [htop, hS]; ring
    have hV : ∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n k : ℝ) * y ^ (k + 1)
        = y * (∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n k : ℝ) * y ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    have hn0 : (n : ℝ) * (Nat.stirlingFirst n 0 : ℝ) = 0 := by
      cases n with
      | zero => simp
      | succ m => rw [Nat.stirlingFirst_succ_zero]; simp
    have hT : ∑ k ∈ Finset.range (n + 2), (Nat.stirlingFirst (n + 1) k : ℝ) * y ^ k
        = (n : ℝ) * (∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n k : ℝ) * y ^ k)
          + y * (∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n k : ℝ) * y ^ k) := by
      have hT' : ∑ k ∈ Finset.range (n + 2), (Nat.stirlingFirst (n + 1) k : ℝ) * y ^ k
          = (n : ℝ) * (∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n (k + 1) : ℝ) * y ^ (k + 1))
            + (∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n k : ℝ) * y ^ (k + 1)) := by
        rw [Finset.sum_range_succ' (fun k => (Nat.stirlingFirst (n + 1) k : ℝ) * y ^ k) (n + 1),
          h0, Nat.cast_zero, zero_mul, add_zero, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Nat.stirlingFirst_succ_succ]
        push_cast
        ring
      rw [hT', hU, hV, mul_sub, hn0, sub_zero]
    rw [Finset.prod_range_succ, ih, Finset.sum_mul, hT, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring




private theorem falling_pow (n : ℕ) (y : ℝ) :
    y ^ n = ∑ l ∈ Finset.range (n + 1),
      (Nat.stirlingSecond n l : ℝ) * ∏ i ∈ Finset.range l, (y - (i : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h0 : Nat.stirlingSecond (n + 1) 0 = 0 := Nat.stirlingSecond_succ_zero n
    have hfall : ∀ l : ℕ, y * ∏ i ∈ Finset.range l, (y - (i : ℝ))
        = ∏ i ∈ Finset.range (l + 1), (y - (i : ℝ))
          + (l : ℝ) * ∏ i ∈ Finset.range l, (y - (i : ℝ)) := by
      intro l
      rw [Finset.prod_range_succ]
      ring
    have hB : ∑ l ∈ Finset.range (n + 1),
          ((l : ℝ) * (Nat.stirlingSecond n l : ℝ) * ∏ i ∈ Finset.range l, (y - (i : ℝ)))
        = ∑ l ∈ Finset.range n,
          (((l : ℝ) + 1) * (Nat.stirlingSecond n (l + 1) : ℝ)
            * ∏ i ∈ Finset.range (l + 1), (y - (i : ℝ))) := by
      rw [Finset.sum_range_succ' (fun l => (l : ℝ) * (Nat.stirlingSecond n l : ℝ) *
        ∏ i ∈ Finset.range l, (y - (i : ℝ))) n]
      simp only [Nat.cast_zero, zero_mul, Finset.range_zero, Finset.prod_empty, add_zero]
      apply Finset.sum_congr rfl
      intro k hk
      push_cast
      ring
    have hA : ∑ l ∈ Finset.range (n + 1),
          (Nat.stirlingSecond n l : ℝ) * ∏ i ∈ Finset.range (l + 1), (y - (i : ℝ))
        = (∑ l ∈ Finset.range n,
            (Nat.stirlingSecond n l : ℝ) * ∏ i ∈ Finset.range (l + 1), (y - (i : ℝ)))
          + ∏ i ∈ Finset.range (n + 1), (y - (i : ℝ)) := by
      rw [Finset.sum_range_succ]
      have hself : (Nat.stirlingSecond n n : ℝ) = 1 := by
        rw [Nat.stirlingSecond_self, Nat.cast_one]
      rw [hself, one_mul]
    have hT : ∑ l ∈ Finset.range (n + 2),
          (Nat.stirlingSecond (n + 1) l : ℝ) * ∏ i ∈ Finset.range l, (y - (i : ℝ))
        = (∑ l ∈ Finset.range n,
            (Nat.stirlingSecond (n + 1) (l + 1) : ℝ) * ∏ i ∈ Finset.range (l + 1), (y - (i : ℝ)))
          + ∏ i ∈ Finset.range (n + 1), (y - (i : ℝ)) := by
      rw [Finset.sum_range_succ' (fun l => (Nat.stirlingSecond (n + 1) l : ℝ) *
        ∏ i ∈ Finset.range l, (y - (i : ℝ))) (n + 1),
        h0, Nat.cast_zero, zero_mul, add_zero, Finset.sum_range_succ]
      have hself : (Nat.stirlingSecond (n + 1) (n + 1) : ℝ) = 1 := by
        rw [Nat.stirlingSecond_self, Nat.cast_one]
      rw [hself, one_mul]
    have hAB : (∑ l ∈ Finset.range n, (Nat.stirlingSecond n l : ℝ) *
          ∏ i ∈ Finset.range (l + 1), (y - (i : ℝ)))
        + ∑ l ∈ Finset.range n, (((l : ℝ) + 1) * (Nat.stirlingSecond n (l + 1) : ℝ) *
          ∏ i ∈ Finset.range (l + 1), (y - (i : ℝ)))
        = ∑ l ∈ Finset.range n, (Nat.stirlingSecond (n + 1) (l + 1) : ℝ) *
          ∏ i ∈ Finset.range (l + 1), (y - (i : ℝ)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      have hss : Nat.stirlingSecond (n + 1) (l + 1)
          = (l + 1) * Nat.stirlingSecond n (l + 1) + Nat.stirlingSecond n l :=
        Nat.stirlingSecond_succ_succ n l
      rw [hss]
      push_cast
      ring
    have hexpand : y * (∑ l ∈ Finset.range (n + 1), (Nat.stirlingSecond n l : ℝ) *
          ∏ i ∈ Finset.range l, (y - (i : ℝ)))
        = ∑ l ∈ Finset.range (n + 1), (Nat.stirlingSecond n l : ℝ) *
          (∏ i ∈ Finset.range (l + 1), (y - (i : ℝ))
            + (l : ℝ) * ∏ i ∈ Finset.range l, (y - (i : ℝ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      have e := hfall l
      linear_combination (Nat.stirlingSecond n l : ℝ) * e
    have hsplit : (∑ l ∈ Finset.range (n + 1), (Nat.stirlingSecond n l : ℝ) *
          (∏ i ∈ Finset.range (l + 1), (y - (i : ℝ))
            + (l : ℝ) * ∏ i ∈ Finset.range l, (y - (i : ℝ))))
        = (∑ l ∈ Finset.range (n + 1), (Nat.stirlingSecond n l : ℝ) *
            ∏ i ∈ Finset.range (l + 1), (y - (i : ℝ)))
          + ∑ l ∈ Finset.range (n + 1),
            ((l : ℝ) * (Nat.stirlingSecond n l : ℝ) * ∏ i ∈ Finset.range l, (y - (i : ℝ))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    have hpow : y ^ (n + 1) = y * y ^ n := by ring
    rw [hT, hpow, ih, hexpand, hsplit, hA, hB]
    linear_combination hAB




private theorem binom_expand (u v : ℝ) (e : ℕ) :
    (u + v) ^ e = ∑ m ∈ Finset.range (e + 1), (Nat.choose e m : ℝ) * u ^ (e - m) * v ^ (m) := by
  rw [add_comm u v, add_pow]
  apply Finset.sum_congr rfl
  intro m hm
  ring

private theorem inner_eval (α β : ℝ) (r p k' : ℕ) :
    (∑ j ∈ Finset.range (p + 1), (-1 : ℝ) ^ (p - j) * (Nat.choose p j : ℝ) *
        (α * (r : ℝ) + β * (j : ℝ)) ^ (k'))
    = ∑ j' ∈ Finset.range (k' + 1), (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') * β ^ (j') *
      ((Nat.factorial p : ℝ) * (Nat.stirlingSecond j' p : ℝ)) := by
  calc (∑ j ∈ Finset.range (p + 1), (-1 : ℝ) ^ (p - j) * (Nat.choose p j : ℝ) *
      (α * (r : ℝ) + β * (j : ℝ)) ^ (k'))
      = ∑ j ∈ Finset.range (p + 1), ∑ j' ∈ Finset.range (k' + 1),
        ((-1 : ℝ) ^ (p - j) * (Nat.choose p j : ℝ) *
          ((Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') * (β * (j : ℝ)) ^ (j'))) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [binom_expand (α * (r : ℝ)) (β * (j : ℝ)) k', Finset.mul_sum]
    _ = ∑ j' ∈ Finset.range (k' + 1), ∑ j ∈ Finset.range (p + 1),
        ((-1 : ℝ) ^ (p - j) * (Nat.choose p j : ℝ) *
          ((Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') * (β * (j : ℝ)) ^ (j'))) :=
        Finset.sum_comm
    _ = _ := by
        apply Finset.sum_congr rfl
        intro j' hj'
        calc (∑ j ∈ Finset.range (p + 1), (-1 : ℝ) ^ (p - j) * (Nat.choose p j : ℝ) *
              ((Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') * (β * (j : ℝ)) ^ (j')))
            = ((Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') * β ^ (j')) *
              ∑ j ∈ Finset.range (p + 1), (-1 : ℝ) ^ (p - j) * (Nat.choose p j : ℝ) *
                  (j : ℝ) ^ (j') := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              rw [mul_pow]
              ring
          _ = _ := by
              rw [← stirlingSecond_mul_factorial_eq_sum j' p]
              ring

private theorem inner_vanish (α β : ℝ) (r k t : ℕ) (h : k < t) :
    ∑ j ∈ Finset.range (t + 1), (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
      ∏ i ∈ Finset.range k, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ)) = 0 := by
  have hexpR : ∀ j ∈ Finset.range (t + 1),
      (∏ i ∈ Finset.range k, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ)))
      = ∑ k' ∈ Finset.range (k + 1), (Nat.stirlingFirst k k' : ℝ) *
          (α * (r : ℝ) + β * (j : ℝ)) ^ (k') :=
    fun j _ => rising_eq k _
  calc (∑ j ∈ Finset.range (t + 1), (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
        ∏ i ∈ Finset.range k, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ)))
      = ∑ j ∈ Finset.range (t + 1), ∑ k' ∈ Finset.range (k + 1),
        ((-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
          ((Nat.stirlingFirst k k' : ℝ) * (α * (r : ℝ) + β * (j : ℝ)) ^ (k'))) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hexpR j hj, Finset.mul_sum]
    _ = ∑ k' ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (t + 1),
        ((-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
          ((Nat.stirlingFirst k k' : ℝ) * (α * (r : ℝ) + β * (j : ℝ)) ^ (k'))) :=
        Finset.sum_comm
    _ = 0 := by
        apply Finset.sum_eq_zero
        intro k' hk'
        have efac : (∑ j ∈ Finset.range (t + 1), (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
              ((Nat.stirlingFirst k k' : ℝ) * (α * (r : ℝ) + β * (j : ℝ)) ^ (k')))
            = (Nat.stirlingFirst k k' : ℝ) *
              ∑ j ∈ Finset.range (t + 1), (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
                (α * (r : ℝ) + β * (j : ℝ)) ^ (k') := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        have esum : (∑ j' ∈ Finset.range (k' + 1), (Nat.choose k' j' : ℝ) *
            (α * (r : ℝ)) ^ (k' - j') * β ^ (j') *
            ((Nat.factorial t : ℝ) * (Nat.stirlingSecond j' t : ℝ))) = 0 := by
          apply Finset.sum_eq_zero
          intro j' hj'
          have hk'k : k' ≤ k := by
            have := Finset.mem_range.mp hk'
            omega
          have hj'k : j' ≤ k := by
            have := Finset.mem_range.mp hj'
            omega
          have hjt : j' < t := by omega
          have hS : Nat.stirlingSecond j' t = 0 := Nat.stirlingSecond_eq_zero_of_lt hjt
          rw [hS, Nat.cast_zero]
          ring
        rw [efac, inner_eval α β r t k', esum, mul_zero]

private theorem master1 (α β : ℝ) (r n p : ℕ) :
    (∑ j ∈ Finset.range (p + 1), (-1 : ℝ) ^ (p - j) * (Nat.choose p j : ℝ) *
      ∏ i ∈ Finset.range n, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ)))
    = (Nat.factorial p : ℝ) * ∑ k' ∈ Finset.range (n + 1), ∑ j' ∈ Finset.range (k' + 1),
      (Nat.stirlingFirst n k' : ℝ) * (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') * β ^ (j') *
        (Nat.stirlingSecond j' p : ℝ) := by
  have hexpR : ∀ j ∈ Finset.range (p + 1),
      (∏ i ∈ Finset.range n, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ)))
      = ∑ k' ∈ Finset.range (n + 1), (Nat.stirlingFirst n k' : ℝ) *
          (α * (r : ℝ) + β * (j : ℝ)) ^ (k') :=
    fun j _ => rising_eq n _
  calc (∑ j ∈ Finset.range (p + 1), (-1 : ℝ) ^ (p - j) * (Nat.choose p j : ℝ) *
        ∏ i ∈ Finset.range n, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ)))
      = ∑ j ∈ Finset.range (p + 1), ∑ k' ∈ Finset.range (n + 1),
        ((-1 : ℝ) ^ (p - j) * (Nat.choose p j : ℝ) *
          ((Nat.stirlingFirst n k' : ℝ) * (α * (r : ℝ) + β * (j : ℝ)) ^ (k'))) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hexpR j hj, Finset.mul_sum]
    _ = ∑ k' ∈ Finset.range (n + 1), (Nat.stirlingFirst n k' : ℝ) *
        (∑ j ∈ Finset.range (p + 1), (-1 : ℝ) ^ (p - j) * (Nat.choose p j : ℝ) *
          (α * (r : ℝ) + β * (j : ℝ)) ^ (k')) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k' hk'
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = _ := by
        have hstep : ∀ k' ∈ Finset.range (n + 1),
            ((Nat.stirlingFirst n k' : ℝ) *
              ∑ j ∈ Finset.range (p + 1), (-1 : ℝ) ^ (p - j) * (Nat.choose p j : ℝ) *
                (α * (r : ℝ) + β * (j : ℝ)) ^ (k'))
            = (Nat.factorial p : ℝ) * ∑ j' ∈ Finset.range (k' + 1),
              (Nat.stirlingFirst n k' : ℝ) * (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') *
                β ^ (j') *
                (Nat.stirlingSecond j' p : ℝ) := by
          intro k' hk'
          rw [inner_eval α β r p k']
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j' hj'
          ring
        conv_rhs => rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k' hk' => hstep k' hk')

private theorem master1d (α β : ℝ) (r n p : ℕ) :
    (∑ j ∈ Finset.range (p + 1), (-1 : ℝ) ^ (p - j) * (Nat.choose p j : ℝ) *
      ∏ i ∈ Finset.range n, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ))) / (Nat.factorial p : ℝ)
    = ∑ k' ∈ Finset.range (n + 1), ∑ j' ∈ Finset.range (k' + 1),
      (Nat.stirlingFirst n k' : ℝ) * (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') * β ^ (j') *
        (Nat.stirlingSecond j' p : ℝ) := by
  have hm := master1 α β r n p
  have hfk : (Nat.factorial p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p)
  rw [hm, ← div_mul_eq_mul_div, div_self hfk, one_mul]

private theorem rising_neg_fall (k : ℕ) (c : ℝ) :
    ∏ i ∈ Finset.range k, (c + (i : ℝ)) = (-1 : ℝ) ^ k * ∏ i ∈ Finset.range k,
        ((-c) - (i : ℝ)) := by
  have h : ∏ i ∈ Finset.range k, (c + (i : ℝ))
      = ∏ i ∈ Finset.range k, ((-1 : ℝ) * (((-c)) - (i : ℝ))) := by
    apply Finset.prod_congr rfl
    intro i hi
    ring
  rw [h, Finset.prod_mul_distrib]
  simp [Finset.prod_const, Finset.card_range]

private theorem master2 (n : ℕ) (c : ℝ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ (n - k) * (Nat.stirlingSecond n k : ℝ) *
      ∏ i ∈ Finset.range k, (c + (i : ℝ)) = c ^ n := by
  have hsign : ∀ k ≤ n, (-1 : ℝ) ^ (n - k) * (-1 : ℝ) ^ k = (-1 : ℝ) ^ n := by
    intro k hk
    have hnk : n - k + k = n := by omega
    calc (-1 : ℝ) ^ (n - k) * (-1 : ℝ) ^ k = (-1 : ℝ) ^ (n - k + k) := by rw [pow_add]
      _ = (-1 : ℝ) ^ n := by rw [hnk]
  have e1 : ∀ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ (n - k) * (Nat.stirlingSecond n k : ℝ) *
      ∏ i ∈ Finset.range k, (c + (i : ℝ))
      = (-1 : ℝ) ^ n * ((Nat.stirlingSecond n k : ℝ) * ∏ i ∈ Finset.range k, ((-c) - (i : ℝ))) := by
    intro k hk
    have hkn : k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    rw [rising_neg_fall k c]
    linear_combination ((Nat.stirlingSecond n k : ℝ) * ∏ i ∈ Finset.range k, ((-c) - (i : ℝ))) *
      (hsign k hkn)
  have hsq : (-1 : ℝ) ^ n * (-c) ^ n = c ^ n := by
    have hnp : (-c) ^ n = (-1 : ℝ) ^ n * c ^ n := by
      have hneg : (-c) = (-1 : ℝ) * c := by ring
      rw [hneg, mul_pow]
    have hss : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      rw [← pow_add]
      have hnn : n + n = 2 * n := by omega
      rw [hnn, pow_mul]
      simp
    linear_combination c ^ n * hss
  calc (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ (n - k) * (Nat.stirlingSecond n k : ℝ) *
        ∏ i ∈ Finset.range k, (c + (i : ℝ)))
      = (-1 : ℝ) ^ n * ∑ k ∈ Finset.range (n + 1),
        ((Nat.stirlingSecond n k : ℝ) * ∏ i ∈ Finset.range k, ((-c) - (i : ℝ))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k hk => e1 k hk)
    _ = (-1 : ℝ) ^ n * (-c) ^ n := by rw [falling_pow n (-c)]
    _ = c ^ n := hsq

private theorem master2c (α β : ℝ) (r n t : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ (n - k) * (Nat.stirlingSecond n k : ℝ) *
      (∑ j ∈ Finset.range (t + 1), (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
        ∏ i ∈ Finset.range k, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ))))
    = (Nat.factorial t : ℝ) * ∑ k' ∈ Finset.range (n + 1), (Nat.choose n k' : ℝ) *
      (α * (r : ℝ)) ^ (n - k') *
      β ^ (k') * (Nat.stirlingSecond k' t : ℝ) := by
  calc (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ (n - k) * (Nat.stirlingSecond n k : ℝ) *
        (∑ j ∈ Finset.range (t + 1), (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
          ∏ i ∈ Finset.range k, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ))))
      = ∑ j ∈ Finset.range (t + 1), (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
        (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ (n - k) * (Nat.stirlingSecond n k : ℝ) *
          ∏ i ∈ Finset.range k, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ))) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        ring
    _ = ∑ j ∈ Finset.range (t + 1), (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
        (α * (r : ℝ) + β * (j : ℝ)) ^ n := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [master2 n (α * (r : ℝ) + β * (j : ℝ))]
    _ = _ := by
        have hstep : ∀ j ∈ Finset.range (t + 1),
            (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) * (α * (r : ℝ) + β * (j : ℝ)) ^ n
            = ∑ k' ∈ Finset.range (n + 1), (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
              ((Nat.choose n k' : ℝ) * (α * (r : ℝ)) ^ (n - k') * (β * (j : ℝ)) ^ (k')) := by
          intro j hj
          rw [binom_expand (α * (r : ℝ)) (β * (j : ℝ)) n, Finset.mul_sum]
        have hfin : ∀ k' ∈ Finset.range (n + 1),
            (∑ j ∈ Finset.range (t + 1), (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
              ((Nat.choose n k' : ℝ) * (α * (r : ℝ)) ^ (n - k') * (β * (j : ℝ)) ^ (k')))
            = (Nat.factorial t : ℝ) * ((Nat.choose n k' : ℝ) * (α * (r : ℝ)) ^ (n - k') * β ^ (k') *
              (Nat.stirlingSecond k' t : ℝ)) := by
          intro k' hk'
          calc (∑ j ∈ Finset.range (t + 1), (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
                ((Nat.choose n k' : ℝ) * (α * (r : ℝ)) ^ (n - k') * (β * (j : ℝ)) ^ (k')))
              = ((Nat.choose n k' : ℝ) * (α * (r : ℝ)) ^ (n - k') * β ^ (k')) *
                ∑ j ∈ Finset.range (t + 1), (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
                    (j : ℝ) ^ (k') := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                rw [mul_pow]
                ring
            _ = _ := by
                rw [← stirlingSecond_mul_factorial_eq_sum k' t]
                ring
        rw [Finset.sum_congr rfl (fun j hj => hstep j hj), Finset.sum_comm]
        conv_rhs => rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k' hk' => hfin k' hk')

private theorem sum_range_extend {f : ℕ → ℝ} (m n : ℕ) (hmn : m ≤ n)
    (h0 : ∀ j ∈ Finset.range (n + 1), j ∉ Finset.range (m + 1) → f j = 0) :
    ∑ j ∈ Finset.range (m + 1), f j = ∑ j ∈ Finset.range (n + 1), f j := by
  have hsub : Finset.range (m + 1) ⊆ Finset.range (n + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  exact Finset.sum_subset hsub (fun x hx hnx => h0 x hx hnx)

private theorem part1_thm (α β x : ℝ) (n r : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      ((∑ j ∈ Finset.range (k + 1),
        (-1 : ℝ) ^ (k - j) * (Nat.choose k j : ℝ) *
          ∏ i ∈ Finset.range n, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ))) /
        (Nat.factorial k : ℝ)) * x ^ k)
    = ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (k + 1),
      (Nat.stirlingFirst n k : ℝ) * (Nat.choose k j : ℝ) *
        (α * (r : ℝ)) ^ (k - j) * β ^ j *
        (∑ l ∈ Finset.range (j + 1), (Nat.stirlingSecond j l : ℝ) * x ^ l) := by
  have hL : (∑ k ∈ Finset.range (n + 1),
      ((∑ j ∈ Finset.range (k + 1),
        (-1 : ℝ) ^ (k - j) * (Nat.choose k j : ℝ) *
          ∏ i ∈ Finset.range n, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ))) /
        (Nat.factorial k : ℝ)) * x ^ k)
      = ∑ k ∈ Finset.range (n + 1), ∑ k' ∈ Finset.range (n + 1), ∑ j' ∈ Finset.range (n + 1),
        ((Nat.stirlingFirst n k' : ℝ) * (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') *
          β ^ (j') *
          (Nat.stirlingSecond j' k : ℝ) * x ^ k) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hle : k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    rw [master1d α β r n k]
    have hjext : (∑ k' ∈ Finset.range (n + 1), ∑ j' ∈ Finset.range (k' + 1),
          ((Nat.stirlingFirst n k' : ℝ) * (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') *
            β ^ (j') *
            (Nat.stirlingSecond j' k : ℝ)))
        = ∑ k' ∈ Finset.range (n + 1), ∑ j' ∈ Finset.range (n + 1),
          ((Nat.stirlingFirst n k' : ℝ) * (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') *
            β ^ (j') *
            (Nat.stirlingSecond j' k : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k' hk'
      have hle' : k' ≤ n := by
        have := Finset.mem_range.mp hk'
        omega
      have hzero : ∀ j' ∈ Finset.range (n + 1), j' ∉ Finset.range (k' + 1) →
          ((Nat.stirlingFirst n k' : ℝ) * (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') *
            β ^ (j') *
            (Nat.stirlingSecond j' k : ℝ)) = 0 := by
        intro j' hj' hjk'
        have hlt : k' < j' := by
          have h1 : j' < n + 1 := Finset.mem_range.mp hj'
          have h2 : ¬ j' < k' + 1 := fun h => hjk' (Finset.mem_range.mpr h)
          omega
        have hC : Nat.choose k' j' = 0 := Nat.choose_eq_zero_of_lt hlt
        rw [hC]
        simp
      exact sum_range_extend k' n hle' hzero
    rw [hjext]
    simp only [Finset.sum_mul]
  have hR : (∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (k + 1),
      (Nat.stirlingFirst n k : ℝ) * (Nat.choose k j : ℝ) *
        (α * (r : ℝ)) ^ (k - j) * β ^ j *
        (∑ l ∈ Finset.range (j + 1), (Nat.stirlingSecond j l : ℝ) * x ^ l))
      = ∑ l ∈ Finset.range (n + 1), ∑ k' ∈ Finset.range (n + 1), ∑ j' ∈ Finset.range (n + 1),
        (((Nat.stirlingFirst n k' : ℝ) * (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') *
          β ^ (j')) *
          ((Nat.stirlingSecond j' l : ℝ) * x ^ l)) := by
    have hBext : ∀ j' ∈ Finset.range (n + 1),
        (∑ l ∈ Finset.range (j' + 1), (Nat.stirlingSecond j' l : ℝ) * x ^ l)
        = ∑ l ∈ Finset.range (n + 1), (Nat.stirlingSecond j' l : ℝ) * x ^ l := by
      intro j' hj'
      have hle : j' ≤ n := by
        have := Finset.mem_range.mp hj'
        omega
      have hzero : ∀ l ∈ Finset.range (n + 1), l ∉ Finset.range (j' + 1) →
          ((Nat.stirlingSecond j' l : ℝ) * x ^ l) = 0 := by
        intro l hl hnl
        have hlj : j' < l := by
          have h1 : l < n + 1 := Finset.mem_range.mp hl
          have h2 : ¬ l < j' + 1 := fun h => hnl (Finset.mem_range.mpr h)
          omega
        have hS : Nat.stirlingSecond j' l = 0 := Nat.stirlingSecond_eq_zero_of_lt hlj
        rw [hS]
        simp
      exact sum_range_extend j' n hle hzero
    have hR1 : (∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (k + 1),
        (Nat.stirlingFirst n k : ℝ) * (Nat.choose k j : ℝ) *
          (α * (r : ℝ)) ^ (k - j) * β ^ j *
          (∑ l ∈ Finset.range (j + 1), (Nat.stirlingSecond j l : ℝ) * x ^ l))
        = ∑ k' ∈ Finset.range (n + 1), ∑ j' ∈ Finset.range (k' + 1),
          (((Nat.stirlingFirst n k' : ℝ) * (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') *
            β ^ (j')) *
            (∑ l ∈ Finset.range (n + 1), (Nat.stirlingSecond j' l : ℝ) * x ^ l)) := by
      apply Finset.sum_congr rfl
      intro k' hk'
      apply Finset.sum_congr rfl
      intro j' hj'
      have hj'n : j' ∈ Finset.range (n + 1) := by
        have h1 : j' < k' + 1 := Finset.mem_range.mp hj'
        have h2 : k' < n + 1 := Finset.mem_range.mp hk'
        exact Finset.mem_range.mpr (by omega)
      rw [hBext j' hj'n]
    have hR1b : (∑ k' ∈ Finset.range (n + 1), ∑ j' ∈ Finset.range (k' + 1),
          (((Nat.stirlingFirst n k' : ℝ) * (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') *
            β ^ (j')) *
            (∑ l ∈ Finset.range (n + 1), (Nat.stirlingSecond j' l : ℝ) * x ^ l)))
        = ∑ k' ∈ Finset.range (n + 1), ∑ j' ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          (((Nat.stirlingFirst n k' : ℝ) * (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') *
            β ^ (j')) *
            ((Nat.stirlingSecond j' l : ℝ) * x ^ l)) := by
      apply Finset.sum_congr rfl
      intro k' hk'
      have hle' : k' ≤ n := by
        have := Finset.mem_range.mp hk'
        omega
      have hjext : (∑ j' ∈ Finset.range (k' + 1),
            (((Nat.stirlingFirst n k' : ℝ) * (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') *
              β ^ (j')) *
              (∑ l ∈ Finset.range (n + 1), (Nat.stirlingSecond j' l : ℝ) * x ^ l)))
          = ∑ j' ∈ Finset.range (n + 1),
            (((Nat.stirlingFirst n k' : ℝ) * (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') *
              β ^ (j')) *
              (∑ l ∈ Finset.range (n + 1), (Nat.stirlingSecond j' l : ℝ) * x ^ l)) := by
        have hzero : ∀ j' ∈ Finset.range (n + 1), j' ∉ Finset.range (k' + 1) →
            (((Nat.stirlingFirst n k' : ℝ) * (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') *
              β ^ (j')) *
              (∑ l ∈ Finset.range (n + 1), (Nat.stirlingSecond j' l : ℝ) * x ^ l)) = 0 := by
          intro j' hj' hjk'
          have hlt : k' < j' := by
            have h1 : j' < n + 1 := Finset.mem_range.mp hj'
            have h2 : ¬ j' < k' + 1 := fun h => hjk' (Finset.mem_range.mpr h)
            omega
          have hC : Nat.choose k' j' = 0 := Nat.choose_eq_zero_of_lt hlt
          rw [hC]
          simp
        exact sum_range_extend k' n hle' hzero
      rw [hjext]
      apply Finset.sum_congr rfl
      intro j' hj'
      rw [Finset.mul_sum]
    have hR2 : (∑ k' ∈ Finset.range (n + 1), ∑ j' ∈ Finset.range (n + 1),
          ∑ l ∈ Finset.range (n + 1),
          (((Nat.stirlingFirst n k' : ℝ) * (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') *
            β ^ (j')) *
            ((Nat.stirlingSecond j' l : ℝ) * x ^ l)))
        = ∑ l ∈ Finset.range (n + 1), ∑ k' ∈ Finset.range (n + 1), ∑ j' ∈ Finset.range (n + 1),
          (((Nat.stirlingFirst n k' : ℝ) * (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') *
            β ^ (j')) *
            ((Nat.stirlingSecond j' l : ℝ) * x ^ l)) := by
      calc (∑ k' ∈ Finset.range (n + 1), ∑ j' ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
            (((Nat.stirlingFirst n k' : ℝ) * (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') *
              β ^ (j')) *
              ((Nat.stirlingSecond j' l : ℝ) * x ^ l)))
          = ∑ j' ∈ Finset.range (n + 1), ∑ k' ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
            (((Nat.stirlingFirst n k' : ℝ) * (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') *
              β ^ (j')) *
              ((Nat.stirlingSecond j' l : ℝ) * x ^ l)) := Finset.sum_comm
        _ = ∑ j' ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1), ∑ k' ∈ Finset.range (n + 1),
            (((Nat.stirlingFirst n k' : ℝ) * (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') *
              β ^ (j')) *
              ((Nat.stirlingSecond j' l : ℝ) * x ^ l)) :=
            Finset.sum_congr rfl (fun j' _ => Finset.sum_comm)
        _ = ∑ l ∈ Finset.range (n + 1), ∑ j' ∈ Finset.range (n + 1), ∑ k' ∈ Finset.range (n + 1),
            (((Nat.stirlingFirst n k' : ℝ) * (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') *
              β ^ (j')) *
              ((Nat.stirlingSecond j' l : ℝ) * x ^ l)) := Finset.sum_comm
        _ = ∑ l ∈ Finset.range (n + 1), ∑ k' ∈ Finset.range (n + 1), ∑ j' ∈ Finset.range (n + 1),
            (((Nat.stirlingFirst n k' : ℝ) * (Nat.choose k' j' : ℝ) * (α * (r : ℝ)) ^ (k' - j') *
              β ^ (j')) *
              ((Nat.stirlingSecond j' l : ℝ) * x ^ l)) :=
            Finset.sum_congr rfl (fun l _ => Finset.sum_comm)
    rw [hR1, hR1b, hR2]
  rw [hL, hR]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro k' hk'
  apply Finset.sum_congr rfl
  intro j' hj'
  ring

private theorem master2cd (α β : ℝ) (r n t : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ (n - k) * (Nat.stirlingSecond n k : ℝ) *
      (∑ j ∈ Finset.range (t + 1), (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
        ∏ i ∈ Finset.range k, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ)))) / (Nat.factorial t : ℝ)
    = ∑ k' ∈ Finset.range (n + 1), (Nat.choose n k' : ℝ) * (α * (r : ℝ)) ^ (n - k') *
      β ^ (k') * (Nat.stirlingSecond k' t : ℝ) := by
  have hm := master2c α β r n t
  have hfk : (Nat.factorial t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero t)
  rw [hm, ← div_mul_eq_mul_div, div_self hfk, one_mul]

private theorem part2_thm (α β x : ℝ) (n r : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ (n - k) * (Nat.stirlingSecond n k : ℝ) *
        (∑ t ∈ Finset.range (k + 1),
          ((∑ j ∈ Finset.range (t + 1),
            (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
              ∏ i ∈ Finset.range k, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ))) /
            (Nat.factorial t : ℝ)) * x ^ t))
    = ∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℝ) * (α * (r : ℝ)) ^ (n - k) * β ^ k *
        (∑ t ∈ Finset.range (k + 1), (Nat.stirlingSecond k t : ℝ) * x ^ t) := by
  have hE : ∀ k ∈ Finset.range (n + 1),
      (∑ t ∈ Finset.range (k + 1),
        ((∑ j ∈ Finset.range (t + 1),
          (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
            ∏ i ∈ Finset.range k, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ))) /
          (Nat.factorial t : ℝ)) * x ^ t)
      = ∑ t ∈ Finset.range (n + 1),
        ((∑ j ∈ Finset.range (t + 1),
          (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
            ∏ i ∈ Finset.range k, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ))) /
          (Nat.factorial t : ℝ)) * x ^ t := by
    intro k hk
    have hle : k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    have hzero : ∀ t ∈ Finset.range (n + 1), t ∉ Finset.range (k + 1) →
        (((∑ j ∈ Finset.range (t + 1),
          (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
            ∏ i ∈ Finset.range k, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ))) /
          (Nat.factorial t : ℝ)) * x ^ t) = 0 := by
      intro t ht htk
      have hkt : k < t := by
        have h1 : t < n + 1 := Finset.mem_range.mp ht
        have h2 : ¬ t < k + 1 := fun h => htk (Finset.mem_range.mpr h)
        omega
      have hv := inner_vanish α β r k t hkt
      rw [hv, zero_div, zero_mul]
    exact sum_range_extend k n hle hzero
  have hpt : ∀ t ∈ Finset.range (n + 1),
      (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ (n - k) * (Nat.stirlingSecond n k : ℝ) *
        (((∑ j ∈ Finset.range (t + 1),
          (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
            ∏ i ∈ Finset.range k, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ))) /
          (Nat.factorial t : ℝ)) * x ^ t))
      = ((∑ k' ∈ Finset.range (n + 1), (Nat.choose n k' : ℝ) * (α * (r : ℝ)) ^ (n - k') * β ^ (k') *
        (Nat.stirlingSecond k' t : ℝ)) * x ^ t) := by
    intro t ht
    have e1 : (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ (n - k) * (Nat.stirlingSecond n k : ℝ) *
        (((∑ j ∈ Finset.range (t + 1),
          (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
            ∏ i ∈ Finset.range k, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ))) /
          (Nat.factorial t : ℝ)) * x ^ t))
        = ∑ k ∈ Finset.range (n + 1),
          ((((-1 : ℝ) ^ (n - k) * (Nat.stirlingSecond n k : ℝ) *
            (∑ j ∈ Finset.range (t + 1),
              (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
                ∏ i ∈ Finset.range k, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ)))) /
            (Nat.factorial t : ℝ)) * x ^ t) :=
      Finset.sum_congr rfl (fun k hk => by ring)
    rw [e1, ← Finset.sum_mul, ← Finset.sum_div, master2cd α β r n t]
  have hL2 : (∑ k ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ (n - k) * (Nat.stirlingSecond n k : ℝ) *
        (∑ t ∈ Finset.range (k + 1),
          ((∑ j ∈ Finset.range (t + 1),
            (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
              ∏ i ∈ Finset.range k, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ))) /
            (Nat.factorial t : ℝ)) * x ^ t))
      = ∑ t ∈ Finset.range (n + 1),
        ((∑ k' ∈ Finset.range (n + 1), (Nat.choose n k' : ℝ) * (α * (r : ℝ)) ^ (n - k') * β ^ (k') *
          (Nat.stirlingSecond k' t : ℝ)) * x ^ t) := by
    have eL : (∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ (n - k) * (Nat.stirlingSecond n k : ℝ) *
          (∑ t ∈ Finset.range (k + 1),
            ((∑ j ∈ Finset.range (t + 1),
              (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
                ∏ i ∈ Finset.range k, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ))) /
              (Nat.factorial t : ℝ)) * x ^ t))
        = ∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ (n - k) * (Nat.stirlingSecond n k : ℝ) *
            (∑ t ∈ Finset.range (n + 1),
              ((∑ j ∈ Finset.range (t + 1),
                (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) *
                  ∏ i ∈ Finset.range k, (α * (r : ℝ) + β * (j : ℝ) + (i : ℝ))) /
                (Nat.factorial t : ℝ)) * x ^ t) :=
      Finset.sum_congr rfl (fun k hk => by rw [hE k hk])
    rw [eL]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun t ht => hpt t ht)
  have hR2 : (∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℝ) * (α * (r : ℝ)) ^ (n - k) * β ^ k *
        (∑ t ∈ Finset.range (k + 1), (Nat.stirlingSecond k t : ℝ) * x ^ t))
      = ∑ t ∈ Finset.range (n + 1),
        ((∑ k' ∈ Finset.range (n + 1), (Nat.choose n k' : ℝ) * (α * (r : ℝ)) ^ (n - k') * β ^ (k') *
          (Nat.stirlingSecond k' t : ℝ)) * x ^ t) := by
    have hBext : ∀ k ∈ Finset.range (n + 1),
        (∑ t ∈ Finset.range (k + 1), (Nat.stirlingSecond k t : ℝ) * x ^ t)
        = ∑ t ∈ Finset.range (n + 1), (Nat.stirlingSecond k t : ℝ) * x ^ t := by
      intro k hk
      have hle : k ≤ n := by
        have := Finset.mem_range.mp hk
        omega
      have hzero : ∀ t ∈ Finset.range (n + 1), t ∉ Finset.range (k + 1) →
          ((Nat.stirlingSecond k t : ℝ) * x ^ t) = 0 := by
        intro t ht htk
        have hkt : k < t := by
          have h1 : t < n + 1 := Finset.mem_range.mp ht
          have h2 : ¬ t < k + 1 := fun h => htk (Finset.mem_range.mpr h)
          omega
        have hS : Nat.stirlingSecond k t = 0 := Nat.stirlingSecond_eq_zero_of_lt hkt
        rw [hS]
        simp
      exact sum_range_extend k n hle hzero
    have eR : (∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℝ) * (α * (r : ℝ)) ^ (n - k) * β ^ k *
          (∑ t ∈ Finset.range (k + 1), (Nat.stirlingSecond k t : ℝ) * x ^ t))
        = ∑ k ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (n + 1),
          ((Nat.choose n k : ℝ) * (α * (r : ℝ)) ^ (n - k) * β ^ k *
            ((Nat.stirlingSecond k t : ℝ) * x ^ t)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hBext k hk, Finset.mul_sum]
    rw [eR, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    have e2 : (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * (α * (r : ℝ)) ^ (n - k) * β ^ k *
        ((Nat.stirlingSecond k t : ℝ) * x ^ t))
        = ((∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * (α * (r : ℝ)) ^ (n - k) * β ^ k *
          (Nat.stirlingSecond k t : ℝ)) * x ^ t) := by
      have er : ∀ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * (α * (r : ℝ)) ^ (n - k) * β ^ k *
          ((Nat.stirlingSecond k t : ℝ) * x ^ t)
          = (((Nat.choose n k : ℝ) * (α * (r : ℝ)) ^ (n - k) * β ^ k *
            (Nat.stirlingSecond k t : ℝ)) * x ^ t) := fun k _ => by ring
      rw [Finset.sum_congr rfl (fun k hk => er k hk), ← Finset.sum_mul]
    exact e2
  rw [hL2, hR2]

/-! # Stirling-Bell polynomial connection pair
-/

/--
**Laguerre–Stirling–Bell connection pair.** Let $\alpha$, $\beta$ and $x$ be real numbers, and
let $n$ and $r$ be natural numbers. Write $\binom{k}{j}$ for the binomial coefficients, $c(n,k)$
for the unsigned Stirling numbers of the first kind, $S(n,k)$ for the Stirling numbers of the
second kind, and $y^{\overline{m}} = y(y+1)\cdots(y+m-1)$ for the rising factorial. For natural
numbers $m$, $s$ and real $y$, let $B_m(y) = \sum_{l=0}^{m} S(m,l)\, y^l$ be the Bell polynomial
and
$$L_{m,s}(y) = \sum_{k=0}^{m} \frac{1}{k!} \sum_{j=0}^{k} (-1)^{k-j} \binom{k}{j}
(\alpha s + \beta j)^{\overline{m}}\, y^k$$
the generalized Laguerre polynomial. Then
$$L_{n,r}(x) = \sum_{k=0}^{n} \sum_{j=0}^{k} c(n,k) \binom{k}{j} (\alpha r)^{k-j} \beta^j B_j(x)$$
and
$$\sum_{k=0}^{n} (-1)^{n-k} S(n,k)\, L_{k,r}(x) =
\sum_{k=0}^{n} \binom{n}{k} (\alpha r)^{n-k} \beta^k B_k(x).$$

Source: Mark Shattuck, "Combinatorial Properties of a Generalized Class of
Laguerre Polynomials," Journal of Integer Sequences 24 (2021),
Article 21.2.1, Theorem (label `eqnpair`), equations (labels `eqnpaire1`)
and (`eqnpaire2`), lines 330–339,
https://cs.uwaterloo.ca/journals/JIS/VOL24/Shattuck/shattuck24.tex
-/
theorem stirling_bell_polynomial_connection_pair_general
    (α β x : ℝ) (n r : ℕ) :
    let bellPolynomial : ℕ → ℝ → ℝ := fun m y ↦
      ∑ l ∈ Finset.range (m + 1), (Nat.stirlingSecond m l : ℝ) * y ^ l
    let generalizedLaguerrePolynomial : ℕ → ℕ → ℝ → ℝ := fun m s y ↦
      ∑ k ∈ Finset.range (m + 1),
        ((∑ j ∈ Finset.range (k + 1),
            (-1 : ℝ) ^ (k - j) * (Nat.choose k j : ℝ) *
              ∏ i ∈ Finset.range m,
                (α * (s : ℝ) + β * (j : ℝ) + (i : ℝ))) /
          (Nat.factorial k : ℝ)) * y ^ k
    generalizedLaguerrePolynomial n r x =
        ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (k + 1),
          (Nat.stirlingFirst n k : ℝ) * (Nat.choose k j : ℝ) *
            (α * (r : ℝ)) ^ (k - j) * β ^ j * bellPolynomial j x ∧
      ∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ (n - k) * (Nat.stirlingSecond n k : ℝ) *
            generalizedLaguerrePolynomial k r x =
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℝ) * (α * (r : ℝ)) ^ (n - k) * β ^ k *
            bellPolynomial k x := by
  refine ⟨?_, ?_⟩
  · exact part1_thm α β x n r
  · exact part2_thm α β x n r

set_option linter.unusedVariables false in
/--
**Laguerre–Stirling–Bell connection pair, source form.** Let $\alpha$, $\beta$ and $x$ be real
numbers with $\beta \neq 0$, and let $n$ and $r$ be natural numbers. Write $\binom{k}{j}$ for the
binomial coefficients, $c(n,k)$ for the unsigned Stirling numbers of the first kind, $S(n,k)$ for
the Stirling numbers of the second kind, and $y^{\overline{m}} = y(y+1)\cdots(y+m-1)$ for the
rising factorial. For natural numbers $m$, $s$ and real $y$, let
$B_m(y) = \sum_{l=0}^{m} S(m,l)\, y^l$ be the Bell polynomial and
$$L_{m,s}(y) = \sum_{k=0}^{m} \frac{1}{k!} \sum_{j=0}^{k} (-1)^{k-j} \binom{k}{j}
(\alpha s + \beta j)^{\overline{m}}\, y^k$$
the generalized Laguerre polynomial. Then
$$L_{n,r}(x) = \sum_{k=0}^{n} \sum_{j=0}^{k} c(n,k) \binom{k}{j} (\alpha r)^{k-j} \beta^j B_j(x)$$
and
$$\sum_{k=0}^{n} (-1)^{n-k} S(n,k)\, L_{k,r}(x) =
\sum_{k=0}^{n} \binom{n}{k} (\alpha r)^{n-k} \beta^k B_k(x).$$

The hypothesis $\beta \neq 0$ is not used: the same two identities hold for every real $\beta$.

Source: Mark Shattuck, "Combinatorial Properties of a Generalized Class of
Laguerre Polynomials," Journal of Integer Sequences 24 (2021),
Article 21.2.1, Theorem (label `eqnpair`), equations (labels `eqnpaire1`)
and (`eqnpaire2`), lines 330–339,
https://cs.uwaterloo.ca/journals/JIS/VOL24/Shattuck/shattuck24.tex
-/
@[nolint unusedArguments]
theorem stirling_bell_polynomial_connection_pair
    (α β x : ℝ) (n r : ℕ) (hβ : β ≠ 0) :
    let bellPolynomial : ℕ → ℝ → ℝ := fun m y ↦
      ∑ l ∈ Finset.range (m + 1), (Nat.stirlingSecond m l : ℝ) * y ^ l
    let generalizedLaguerrePolynomial : ℕ → ℕ → ℝ → ℝ := fun m s y ↦
      ∑ k ∈ Finset.range (m + 1),
        ((∑ j ∈ Finset.range (k + 1),
            (-1 : ℝ) ^ (k - j) * (Nat.choose k j : ℝ) *
              ∏ i ∈ Finset.range m,
                (α * (s : ℝ) + β * (j : ℝ) + (i : ℝ))) /
          (Nat.factorial k : ℝ)) * y ^ k
    generalizedLaguerrePolynomial n r x =
        ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (k + 1),
          (Nat.stirlingFirst n k : ℝ) * (Nat.choose k j : ℝ) *
            (α * (r : ℝ)) ^ (k - j) * β ^ j * bellPolynomial j x ∧
      ∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ (n - k) * (Nat.stirlingSecond n k : ℝ) *
            generalizedLaguerrePolynomial k r x =
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℝ) * (α * (r : ℝ)) ^ (n - k) * β ^ k *
            bellPolynomial k x := by
  exact stirling_bell_polynomial_connection_pair_general α β x n r

end MetaMathlibExt
