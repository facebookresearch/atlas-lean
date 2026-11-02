/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

private lemma klamkin_choose_ne (x m : ℕ) (h : m ≤ x) : ((Nat.choose x m : ℕ) : ℚ) ≠ 0 := by
  have hpos : 0 < Nat.choose x m := Nat.choose_pos h
  exact Nat.cast_ne_zero.mpr (by omega)

private lemma klamkin_S_rec (n b x : ℕ) (_h : n + 1 + b ≤ x) :
    ∑ k ∈ Finset.range (n + 1 + 1),
        (Nat.choose (n + 1) k : ℚ) / (Nat.choose x (k + b) : ℚ) =
      (∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℚ) / (Nat.choose x (k + b) : ℚ)) +
      (∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℚ) / (Nat.choose x (k + (b + 1)) : ℚ)) := by
  have hadd : ∀ k : ℕ, (k + 1) + b = k + (b + 1) := fun k => by omega
  have hC0 : ∀ k : ℕ, Nat.choose (n + 1) (k + 1)
      = Nat.choose n k + Nat.choose n (k + 1) := fun k => Nat.choose_succ_succ n k
  have hlast : ((Nat.choose n (n + 1) : ℕ) : ℚ) / ((Nat.choose x (n + (b + 1)) : ℕ) : ℚ) = 0 := by
    have h0 : Nat.choose n (n + 1) = 0 := Nat.choose_succ_self n
    rw [h0]
    simp
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (Nat.choose (n + 1) (k + 1) : ℚ) / (Nat.choose x ((k + 1) + b) : ℚ)
      = (Nat.choose n k : ℚ) / (Nat.choose x (k + (b + 1)) : ℚ)
      + (Nat.choose n (k + 1) : ℚ) / (Nat.choose x (k + (b + 1)) : ℚ) := by
    intro k _
    have e : Nat.choose x ((k + 1) + b) = Nat.choose x (k + (b + 1)) := by rw [hadd k]
    rw [hC0 k, Nat.cast_add, e, add_div]
  have hT : (∑ k ∈ Finset.range (n + 1),
        (Nat.choose n (k + 1) : ℚ) / (Nat.choose x (k + (b + 1)) : ℚ))
      = (∑ k ∈ Finset.range n,
        (Nat.choose n (k + 1) : ℚ) / (Nat.choose x (k + (b + 1)) : ℚ)) := by
    rw [Finset.sum_range_succ
      (fun k => (Nat.choose n (k + 1) : ℚ) / (Nat.choose x (k + (b + 1)) : ℚ)) n,
      hlast, add_zero]
  have hS1 : (∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℚ) / (Nat.choose x (k + b) : ℚ))
      = (∑ k ∈ Finset.range n,
        (Nat.choose n (k + 1) : ℚ) / (Nat.choose x (k + (b + 1)) : ℚ))
      + (Nat.choose n 0 : ℚ) / (Nat.choose x (0 + b) : ℚ) := by
    rw [Finset.sum_range_succ' (fun k => (Nat.choose n k : ℚ) / (Nat.choose x (k + b) : ℚ)) n]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [hadd k]
  have h00 : (Nat.choose (n + 1) 0 : ℚ) / (Nat.choose x (0 + b) : ℚ)
      = (Nat.choose n 0 : ℚ) / (Nat.choose x (0 + b) : ℚ) := by simp
  rw [Finset.sum_range_succ'
      (fun k => (Nat.choose (n + 1) k : ℚ) / (Nat.choose x (k + b) : ℚ)) (n + 1),
    Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hT, hS1, h00]
  abel

private lemma klamkin_R_rec (n b x : ℕ) (_h : n + 1 + b ≤ x) :
    ((x + 1 : ℕ) : ℚ) / (((x - (n + 1) + 1 : ℕ) : ℚ) * (Nat.choose (x - (n + 1)) b : ℚ)) =
      ((x + 1 : ℕ) : ℚ) / (((x - n + 1 : ℕ) : ℚ) * (Nat.choose (x - n) b : ℚ)) +
      ((x + 1 : ℕ) : ℚ) / (((x - n + 1 : ℕ) : ℚ) * (Nat.choose (x - n) (b + 1) : ℚ)) := by
  have hbn : b ≤ x - n := by omega
  have hbn1 : b + 1 ≤ x - n := by omega
  have hbu : b ≤ x - (n + 1) := by omega
  rw [Nat.cast_choose ℚ hbn, Nat.cast_choose ℚ hbn1, Nat.cast_choose ℚ hbu]
  have f4 : x - (n + 1) + 1 = x - n := by omega
  have f6 : x - n - (b + 1) = x - (n + 1) - b := by omega
  have f1 : x - n = (x - (n + 1)) + 1 := by omega
  have f2 : x - n - b = (x - (n + 1) - b) + 1 := by omega
  have g1 : ((x - n - b : ℕ).factorial : ℚ)
      = ((((x - (n + 1) - b : ℕ)) : ℚ) + 1) * (((x - (n + 1) - b : ℕ).factorial : ℚ)) := by
    rw [f2, Nat.factorial_succ]
    push_cast
    ring
  have g2 : ((x - n : ℕ).factorial : ℚ)
      = ((((x - (n + 1) : ℕ)) : ℚ) + 1) * (((x - (n + 1) : ℕ).factorial : ℚ)) := by
    rw [f1, Nat.factorial_succ]
    push_cast
    ring
  have g3 : ((b + 1 : ℕ).factorial : ℚ)
      = ((((b : ℕ)) : ℚ) + 1) * (((b : ℕ).factorial : ℚ)) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have g4 : ((x - n : ℕ) : ℚ) = (((x - (n + 1) : ℕ)) : ℚ) + 1 := by
    rw [f1]
    push_cast
    ring
  have g5 : ((x - n + 1 : ℕ) : ℚ) = (((x - n : ℕ)) : ℚ) + 1 := by
    push_cast
    ring
  have gr : ((x - (n + 1) - b : ℕ) : ℚ)
      = (((x - (n + 1) : ℕ)) : ℚ) - (((b : ℕ)) : ℚ) := Nat.cast_sub hbu
  rw [f4, f6, g1, g2, g3, g5, g4, gr]
  have hnn_u : (0:ℚ) ≤ (((x - (n + 1) : ℕ)) : ℚ) := Nat.cast_nonneg _
  have hnn_b : (0:ℚ) ≤ (((b : ℕ)) : ℚ) := Nat.cast_nonneg _
  have n1 : (((x - (n + 1) : ℕ)) : ℚ) + 1 ≠ 0 := ne_of_gt (by linarith)
  have n2 : ((((x - (n + 1) : ℕ)) : ℚ) + 1) + 1 ≠ 0 := ne_of_gt (by linarith)
  have n3 : (((b : ℕ)) : ℚ) + 1 ≠ 0 := ne_of_gt (by linarith)
  have n4' : (((x - (n + 1) : ℕ)) : ℚ) - (((b : ℕ)) : ℚ) + 1 ≠ 0 := by
    have hrr : (((x - (n + 1) : ℕ)) : ℚ) - (((b : ℕ)) : ℚ) + 1
        = (((x - (n + 1) - b : ℕ)) : ℚ) + 1 := by rw [gr]
    rw [hrr]
    have hnn : (0:ℚ) ≤ (((x - (n + 1) - b : ℕ)) : ℚ) := Nat.cast_nonneg _
    exact ne_of_gt (by linarith)
  have nq : (((x - (n + 1) : ℕ)).factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have ns : (((x - (n + 1) - b : ℕ)).factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have nt : (((b : ℕ)).factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp [n1, n2, n3, n4', nq, ns, nt]
  ring

private lemma klamkin_aux : ∀ (n b x : ℕ), n + b ≤ x →
    ∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℚ) / (Nat.choose x (k + b) : ℚ) =
      ((x + 1 : ℕ) : ℚ) / (((x - n + 1 : ℕ) : ℚ) * (Nat.choose (x - n) b : ℚ)) := by
  intro n
  induction n with
  | zero =>
    intro b x h
    have hb : b ≤ x := by omega
    have hCb : ((Nat.choose x b : ℕ) : ℚ) ≠ 0 := klamkin_choose_ne x b hb
    have hx1 : ((x + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [Nat.zero_add, Nat.sub_zero, Finset.sum_range_one,
      Nat.choose_zero_right, Nat.cast_one]
    field_simp
  | succ n ih =>
    intro b x h
    have h1 : n + b ≤ x := by omega
    have h2 : n + (b + 1) ≤ x := by omega
    have e1 := ih b x h1
    have e2 := ih (b + 1) x h2
    have hS := klamkin_S_rec n b x (by omega)
    have hR := klamkin_R_rec n b x (by omega)
    rw [hS, e1, e2]
    exact hR.symm

/--
**Klamkin's binomial reciprocal identity.** For natural numbers $n$, $b$ and $x$ with
$n + b \le x$, the following equality of rational numbers holds:

$$\sum_{k=0}^{n} \frac{\binom{n}{k}}{\binom{x}{k+b}} = \frac{x+1}{(x-n+1)\binom{x-n}{b}}.$$

Proves `Wanted` entry `klamkin_binomial_reciprocal_identity`.

Source: H. W. Gould and Jocelyn Quaintance, "On the Binomial Identities of Frisch and
Klamkin," Journal of Integer Sequences 19 (2016), Article 16.7.7, Eq. `klam1a`,
lines 105–107, <https://cs.uwaterloo.ca/journals/JIS/VOL19/Gould/gould8.tex>.
-/
theorem klamkin_binomial_reciprocal_identity
    (n b x : ℕ) (h : n + b ≤ x) :
    ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℚ) / (Nat.choose x (k + b) : ℚ) =
      ((x + 1 : ℕ) : ℚ) /
        (((x - n + 1 : ℕ) : ℚ) * (Nat.choose (x - n) b : ℚ)) := by
  exact klamkin_aux n b x h

end MetaMathlibExt
