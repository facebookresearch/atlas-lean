/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.PellLucasNumber
public import MathlibExt.NumberTheory.FibonacciCompanionCompositionSum
public import MathlibExt.NumberTheory.GibonacciCompositionSum
public import MathlibExt.NumberTheory.GibonacciNumber
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence
public import MathlibExt.NumberTheory.PellPellLucasCompositionSumsSqrtTwo
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Composition sums with linear and geometric weights

The weighted composition sum is expressed using Fibonacci and Lucas numbers.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 1, equation (8).
-/

namespace MetaMathlibExt

open Finset

private noncomputable def compSum (w : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ c : Composition n, (c.blocks.map w).prod

private lemma compSum_zero (w : ℕ → ℚ) : compSum w 0 = 1 := by
  simp [compSum, (Composition.blocks_eq_nil _).mpr rfl, composition_card]

private def prepend (n : ℕ) (p : Σ i : Fin (n + 1), Composition (n - i.val)) :
    Composition (n + 1) :=
  ((Composition.single (p.1.val + 1) (Nat.succ_pos _)).append p.2).cast (by
    have := p.1.isLt
    omega)

private lemma prepend_bijective (n : ℕ) : Function.Bijective (prepend n) := by
  constructor
  · rintro ⟨i, c⟩ ⟨j, d⟩ h
    have hblocks := congrArg Composition.blocks h
    change (i.val + 1) :: c.blocks = (j.val + 1) :: d.blocks at hblocks
    obtain ⟨hij, hcd⟩ := List.cons.inj hblocks
    have : i = j := Fin.ext (by omega)
    subst j
    rw [Composition.ext hcd]
  · rintro ⟨l, hpos, hsum⟩
    obtain _ | ⟨b, l⟩ := l
    · simp at hsum
    cases b with
    | zero => simp at hpos
    | succ i =>
      simp only [List.sum_cons] at hsum
      let c : Composition (n - i) :=
        ⟨l, fun h => hpos (List.mem_cons_of_mem _ h), by omega⟩
      exact ⟨⟨⟨i, by omega⟩, c⟩, rfl⟩

private lemma compSum_succ (w : ℕ → ℚ) (n : ℕ) :
    compSum w (n + 1) =
      ∑ i ∈ range (n + 1), w (i + 1) * compSum w (n - i) := by
  let e := Equiv.ofBijective (prepend n) (prepend_bijective n)
  unfold compSum
  rw [← e.sum_comp, Fintype.sum_sigma, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  change (((i.val + 1) :: c.blocks).map w).prod = _
  rw [List.map_cons, List.prod_cons]

private lemma sum_range_add_two (f : ℕ → ℚ) (n : ℕ) :
    ∑ i ∈ range (n + 2), f i = f 0 + f 1 + ∑ i ∈ range n, f (i + 2) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have h : (∑ i ∈ range n, f (i + 1 + 1)) = ∑ i ∈ range n, f (i + 2) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
  rw [h]
  change (∑ i ∈ range n, f (i + 2)) + f 1 + f 0 = f 0 + f 1 + ∑ i ∈ range n, f (i + 2)
  ring

private lemma compSum_recurrence (w : ℕ → ℚ) (a b : ℚ)
    (hw : ∀ j, 1 ≤ j → w (j + 2) = a * w (j + 1) + b * w j) (k : ℕ) :
    compSum w (k + 3) =
      (w 1 + a) * compSum w (k + 2) + (w 2 - a * w 1 + b) * compSum w (k + 1) := by
  have hS3 := compSum_succ w (k + 2)
  have hS2 := compSum_succ w (k + 1)
  have hS1 := compSum_succ w k
  have hexp : compSum w (k + 3) =
      w 1 * compSum w (k + 2) + w 2 * compSum w (k + 1) +
        ∑ i ∈ range (k + 1), w (i + 3) * compSum w (k - i) := by
    have h := sum_range_add_two (fun i => w (i + 1) * compSum w (k + 2 - i)) (k + 1)
    have htail : (∑ i ∈ range (k + 1), w (i + 2 + 1) * compSum w (k + 2 - (i + 2))) =
        ∑ i ∈ range (k + 1), w (i + 3) * compSum w (k - i) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 2; omega
    rw [hS3, h, htail, Nat.sub_zero, show k + 2 - 1 = k + 1 by omega]
  have hsplit2 : compSum w (k + 2) =
      (∑ i ∈ range (k + 1), w (i + 2) * compSum w (k - i)) +
        w 1 * compSum w (k + 1) := by
    rw [hS2, Finset.sum_range_succ']
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2; omega
  have hsumw : ∑ i ∈ range (k + 1), w (i + 3) * compSum w (k - i) =
      a * (∑ i ∈ range (k + 1), w (i + 2) * compSum w (k - i)) +
        b * compSum w (k + 1) := by
    have h1 : (∑ i ∈ range (k + 1), w (i + 3) * compSum w (k - i)) =
        ∑ i ∈ range (k + 1), (a * w (i + 2) + b * w (i + 1)) * compSum w (k - i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hw (i + 1) (by omega)]
    rw [h1]
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← hS1]
  linear_combination hexp + hsumw - a * hsplit2

private def weight (j : ℕ) : ℚ := ((j : ℚ) + 1) * 2 ^ j / 4

private lemma weight_eq (j : ℕ) :
    weight j = ((j : ℚ) + 1) * (2 : ℚ) ^ ((j : ℤ) - 2) := by
  rw [zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast, zpow_ofNat]
  norm_num [weight]
  ring

private lemma weight_recurrence (j : ℕ) (_hj : 1 ≤ j) :
    weight (j + 2) = 4 * weight (j + 1) + (-4) * weight j := by
  simp only [weight, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_succ]
  ring

private lemma compSum_weight_recurrence (k : ℕ) :
    compSum weight (k + 3) = 5 * compSum weight (k + 2) - 5 * compSum weight (k + 1) := by
  have h := compSum_recurrence weight 4 (-4) weight_recurrence k
  norm_num [weight] at h
  simpa only [sub_eq_add_neg] using h

private lemma compSum_weight_one : compSum weight 1 = 1 := by
  have h := compSum_succ weight 0
  norm_num [weight, compSum_zero] at h
  exact h

private lemma compSum_weight_two : compSum weight 2 = 4 := by
  have h := compSum_succ weight 1
  norm_num [sum_range_succ, weight, compSum_zero, compSum_weight_one] at h
  exact h

private lemma lucas_rel (k : ℕ) : lucasNumber (k + 1) = Nat.fib k + Nat.fib (k + 2) := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih₀ ih₁ =>
    have hL : lucasNumber (k + 3) = lucasNumber (k + 2) + lucasNumber (k + 1) := rfl
    have ih₁' : lucasNumber (k + 2) = Nat.fib (k + 1) + Nat.fib (k + 3) := ih₁
    have hF : Nat.fib (k + 4) = Nat.fib (k + 2) + Nat.fib (k + 3) :=
      Nat.fib_add_two (n := k + 2)
    have hF' := Nat.fib_add_two (n := k)
    change lucasNumber (k + 3) = Nat.fib (k + 2) + Nat.fib (k + 4)
    omega

private lemma lucas_add (k : ℕ) :
    lucasNumber (k + 2) + lucasNumber k = 5 * Nat.fib (k + 1) := by
  cases k with
  | zero => rfl
  | succ k =>
    have h₁ : lucasNumber (k + 3) = Nat.fib (k + 2) + Nat.fib (k + 4) :=
      lucas_rel (k + 2)
    have h₂ := lucas_rel k
    have h₃ : Nat.fib (k + 4) = Nat.fib (k + 2) + Nat.fib (k + 3) :=
      Nat.fib_add_two (n := k + 2)
    have h₄ : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) :=
      Nat.fib_add_two (n := k + 1)
    have h₅ := Nat.fib_add_two (n := k)
    change lucasNumber (k + 3) + lucasNumber (k + 1) = 5 * Nat.fib (k + 2)
    omega

private noncomputable def target (n : ℕ) : ℚ :=
  if Odd n then 5 ^ ((n - 1) / 2) * (Nat.fib (n + 1) : ℚ)
  else 5 ^ ((n - 2) / 2) * (lucasNumber (n + 1) : ℚ)

private lemma target_recurrence (n : ℕ) :
    target (n + 3) = 5 * target (n + 2) - 5 * target (n + 1) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hodd₁ : Odd (n + 1) := ⟨k, by omega⟩
    have hnot₂ : ¬ Odd (n + 2) := by
      rw [Nat.not_odd_iff_even]
      exact ⟨k + 1, by omega⟩
    have hodd₃ : Odd (n + 3) := ⟨k + 1, by omega⟩
    simp only [target, hodd₁, hnot₂, hodd₃, ite_true, ite_false]
    have hL : (lucasNumber (n + 3) : ℚ) =
        (Nat.fib (n + 2) : ℚ) + Nat.fib (n + 4) := by
      exact_mod_cast lucas_rel (n + 2)
    rw [show (n + 3 - 1) / 2 = k + 1 by omega,
      show (n + 2 - 2) / 2 = k by omega,
      show (n + 1 - 1) / 2 = k by omega, pow_succ]
    linear_combination -(5 ^ k * 5) * hL
  · have hnot₁ : ¬ Odd (n + 1) := by
      rw [Nat.not_odd_iff_even]
      exact ⟨k + 1, by omega⟩
    have hodd₂ : Odd (n + 2) := ⟨k + 1, by omega⟩
    have hnot₃ : ¬ Odd (n + 3) := by
      rw [Nat.not_odd_iff_even]
      exact ⟨k + 2, by omega⟩
    simp only [target, hnot₁, hodd₂, hnot₃, ite_true, ite_false]
    have hL : (lucasNumber (n + 4) : ℚ) + lucasNumber (n + 2) =
        5 * (Nat.fib (n + 3) : ℚ) := by
      exact_mod_cast lucas_add (n + 2)
    rw [show (n + 3 - 2) / 2 = k + 1 by omega,
      show (n + 2 - 1) / 2 = k + 1 by omega,
      show (n + 1 - 2) / 2 = k by omega, pow_succ]
    linear_combination (5 ^ k * 5) * hL

private lemma compSum_weight_eq (k : ℕ) :
    compSum weight (k + 1) = target (k + 1) ∧
      compSum weight (k + 2) = target (k + 2) := by
  induction k with
  | zero =>
    constructor
    · rw [compSum_weight_one]
      norm_num [target, Nat.fib]
    · rw [compSum_weight_two]
      norm_num [target, lucasNumber]
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    change compSum weight (k + 3) = target (k + 3)
    rw [compSum_weight_recurrence, target_recurrence, ih.1, ih.2]

private lemma compSum_eq (n : ℕ) :
    compSum weight n = ∑ c : Composition n, ∏ i : Fin c.length,
      ((c.blocksFun i : ℚ) + 1) * (2 : ℚ) ^ ((c.blocksFun i : ℤ) - 2) := by
  unfold compSum
  apply Finset.sum_congr rfl
  intro c _
  rw [← c.ofFn_blocksFun, List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply, weight_eq]

/-- **A composition sum with weights $(c_i + 1) 2^{c_i - 2}$ in terms of Fibonacci and Lucas
numbers.** Let $F_k$ be the Fibonacci numbers and $L_k$ the Lucas numbers. For every $n \ge 1$,
the sum of $\prod_{i=1}^{r} (c_i + 1) 2^{c_i - 2}$ over all compositions $(c_1, \dots, c_r)$ of
$n$ (tuples of positive integers with $c_1 + \dots + c_r = n$) equals $5^{(n-1)/2} F_{n+1}$ if $n$
is odd and $5^{(n-2)/2} L_{n+1}$ if $n$ is even.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 1, equation (8). -/
public theorem composition_sum_succ_mul_two_zpow (n : ℕ) (hn : 1 ≤ n) :
    ∑ c : Composition n, ∏ i : Fin c.length,
        ((c.blocksFun i : ℚ) + 1) * (2 : ℚ) ^ ((c.blocksFun i : ℤ) - 2) =
      if Odd n then 5 ^ ((n - 1) / 2) * (Nat.fib (n + 1) : ℚ)
      else 5 ^ ((n - 2) / 2) * (lucasNumber (n + 1) : ℚ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, (Nat.sub_add_cancel hn).symm⟩
  rw [← compSum_eq]
  exact (compSum_weight_eq k).1

end MetaMathlibExt
