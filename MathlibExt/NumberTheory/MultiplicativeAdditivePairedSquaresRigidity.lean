/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.PNat.Basic
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# Rigidity of multiplicative functions additive on paired squares

Following the first-difference argument in Jewel Mahajan,
*Multiplicative functions additive on partitions of 2k nonzero squares*
(https://arxiv.org/abs/2606.29507), we first show that the function is eventually affine.
The neighboring sums of squares used here are `17 = 1² + 4²` and `18 = 3² + 3²`.
-/

namespace MetaMathlibExt

open ArithmeticFunction

namespace multiplicative_additive_paired_squares_eq_id_of_ne_zero

private abbrev Pair := ℕ+ × ℕ+

private def weight (p : Pair) : ℕ := (p.1 : ℕ) ^ 2 + (p.2 : ℕ) ^ 2

private def Represented (k n : ℕ) : Prop :=
  ∃ A : Fin k → Pair, ∑ i, weight (A i) = n

private theorem two_pairs (p q : Pair) : Represented 2 (weight p + weight q) := by
  exact ⟨![p, q], by simp [Fin.sum_univ_two]⟩

private theorem four_pairs (p q r s : Pair) :
    Represented 4 (weight p + weight q + weight r + weight s) := by
  exact ⟨![p, q, r, s], by simp [Fin.sum_univ_four]⟩

private theorem pad {k n : ℕ} (h : Represented k n) (j : ℕ) :
    Represented (k + j) (n + 2 * j) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    obtain ⟨A, hA⟩ := ih
    change Represented ((k + j) + 1) _
    refine ⟨Fin.cons (1, 1) A, ?_⟩
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hA]
    change 2 + (n + 2 * j) = n + 2 * (j + 1)
    omega

-- Start with four squares for n - 22. Replacing each zero root by one leaves
-- between 18 and 22 to supply using four more positive squares.
private theorem eight_squares {n : ℕ} (hn : 22 ≤ n) : Represented 4 n := by
  obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares (n - 22)
  have positiveRoot (x : ℕ) : ∃ u : ℕ+, x ^ 2 ≤ (u : ℕ) ^ 2 ∧ (u : ℕ) ^ 2 ≤ x ^ 2 + 1 := by
    cases x with
    | zero => exact ⟨1, by decide, by decide⟩
    | succ x => exact ⟨⟨x + 1, Nat.succ_pos x⟩, le_rfl, Nat.le_succ _⟩
  obtain ⟨a', ha, ha'⟩ := positiveRoot a
  obtain ⟨b', hb, hb'⟩ := positiveRoot b
  obtain ⟨c', hc, hc'⟩ := positiveRoot c
  obtain ⟨d', hd, hd'⟩ := positiveRoot d
  let m := weight (a', b') + weight (c', d')
  have bounds : m + 18 ≤ n ∧ n ≤ m + 22 := by dsimp [m, weight]; omega
  have fill (r : ℕ) (h₁ : 18 ≤ r) (h₂ : r ≤ 22) : ∃ p q : Pair, weight p + weight q = r := by
    interval_cases r
    · exact ⟨(1, 2), (2, 3), rfl⟩
    · exact ⟨(1, 1), (1, 4), rfl⟩
    · exact ⟨(1, 1), (3, 3), rfl⟩
    · exact ⟨(2, 2), (2, 3), rfl⟩
    · exact ⟨(1, 1), (2, 4), rfl⟩
  obtain ⟨p, q, hpq⟩ := fill (n - m) (by omega) (by omega)
  have eq : m + weight p + weight q = n := by omega
  exact eq ▸ four_pairs (a', b') (c', d') p q

private theorem represented_of_large {k n : ℕ} (hk : 4 ≤ k) (hn : 2 * k + 14 ≤ n) :
    Represented k n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h := pad (eight_squares (n := n - 2 * j) (by omega)) j
  rwa [Nat.sub_add_cancel (by omega : 2 * j ≤ n)] at h

private theorem represented_of_offset {k t : ℕ} (hk : 2 ≤ k)
    (ht : t ∈ ({0, 3, 6, 8, 9, 11, 12} : Finset ℕ)) : Represented k (2 * k + t) := by
  have h : Represented 2 (4 + t) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact two_pairs (1, 1) (1, 1)
    · exact two_pairs (1, 1) (1, 2)
    · exact two_pairs (1, 1) (2, 2)
    · exact two_pairs (1, 1) (1, 3)
    · exact two_pairs (1, 2) (2, 2)
    · exact two_pairs (1, 2) (1, 3)
    · exact two_pairs (2, 2) (2, 2)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  convert pad h j using 1
  omega

private def AdditiveOnPairs (k : ℕ) (f : ArithmeticFunction ℂ) : Prop :=
  ∀ A : Fin k → Pair, f (∑ i, weight (A i)) = ∑ i, f (weight (A i))

private theorem linear_on_pairs {j : ℕ} (hj : 4 ≤ j) {f : ArithmeticFunction ℂ}
    (hadd : AdditiveOnPairs (j + 1) f) : ∃ c : ℂ, ∀ p, f (weight p) = c * weight p := by
  -- The same j pairs can accompany any choice of the last pair.
  have shift (s : ℕ) (hs : 2 * j + 14 ≤ s) :
      ∃ z : ℂ, ∀ p, f (s + weight p) = z + f (weight p) := by
    obtain ⟨A, hA⟩ := represented_of_large hj hs
    refine ⟨∑ i, f (weight (A i)), fun p ↦ ?_⟩
    simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hA, add_comm] using
      hadd (Fin.cons p A)
  let N := 2 * j + 31
  let c := f 18 - f 17
  have step (n : ℕ) (hn : N ≤ n) : f (n + 1) = f n + c := by
    obtain ⟨z, hz⟩ := shift (n - 17) (by dsimp [N] at hn; omega)
    have h₁ : f (n - 17 + 17) = z + f 17 := hz (1, 4)
    have h₂ : f (n - 17 + 18) = z + f 18 := hz (3, 3)
    rw [show n - 17 + 17 = n by dsimp [N] at hn; omega] at h₁
    rw [show n - 17 + 18 = n + 1 by dsimp [N] at hn; omega] at h₂
    dsimp [c]
    linear_combination h₂ - h₁
  let d := f N - c * N
  have affine (n : ℕ) (hn : N ≤ n) : f n = c * n + d := by
    induction n, hn using Nat.le_induction with
    | base => simp [d]
    | succ n hn ih => rw [step n hn, ih, Nat.cast_succ]; ring
  -- Evaluating at a sum of j + 1 identical large pairs kills the constant term.
  let p : Pair := (⟨N + 1, Nat.succ_pos _⟩, 1)
  have hp : N ≤ weight p := by dsimp [p, weight]; nlinarith
  have hsum := hadd (fun _ ↦ p)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_id] at hsum
  rw [affine _ (hp.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos j))), affine _ hp,
    Nat.cast_mul, Nat.cast_succ] at hsum
  have hd : d = 0 := by
    have h : (j : ℂ) * d = 0 := by linear_combination -hsum
    exact (mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr (by omega))
  -- Compare a translated arbitrary pair with the translated large pair.
  obtain ⟨z, hz⟩ := shift N (by dsimp [N]; omega)
  refine ⟨c, fun q ↦ ?_⟩
  have eq₁ := hz p
  have eq₂ := hz q
  rw [affine _ (Nat.le_add_right ..), affine _ hp, Nat.cast_add, hd] at eq₁
  rw [affine _ (Nat.le_add_right ..), Nat.cast_add, hd] at eq₂
  linear_combination eq₁ - eq₂

end multiplicative_additive_paired_squares_eq_id_of_ne_zero

open multiplicative_additive_paired_squares_eq_id_of_ne_zero in
/-- **A nonzero value in the vanishing range of the dichotomy forces the identity.** Let
$k \ge 5$ and let $f$ be a complex-valued multiplicative function such that
$$f\Big(\sum_{j=1}^{k} (x_j^2 + y_j^2)\Big) = \sum_{j=1}^{k} f(x_j^2 + y_j^2)$$
for all positive integers $x_1, \dots, x_k, y_1, \dots, y_k$. Suppose that $f(\beta) \ne 0$ for some
positive integer $\beta$ that is of the form $a^2 + b^2$ with integers $a, b \ge 1$, or of the
form $2k + t$ with $t \in \{0, 3, 6, 8, 9, 11, 12\}$, or satisfies $\beta \ge 2k + 14$. Then
$f(n) = n$ for every positive integer $n$.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Corollary 2 (`integers-2026-A121-cor-2`). -/
public theorem multiplicative_additive_paired_squares_eq_id_of_ne_zero
    (k : ℕ) (hk : 5 ≤ k) (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ x y : Fin k → ℕ, (∀ j, 0 < x j) → (∀ j, 0 < y j) →
      f (∑ j, (x j ^ 2 + y j ^ 2)) = ∑ j, f (x j ^ 2 + y j ^ 2))
    (β : ℕ) (hβ : (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ β = a ^ 2 + b ^ 2) ∨
      (∃ t ∈ ({0, 3, 6, 8, 9, 11, 12} : Finset ℕ), β = 2 * k + t) ∨ 2 * k + 14 ≤ β)
    (hfβ : f β ≠ 0) :
    ∀ n : ℕ, 0 < n → f n = n := by
  have addPairs : AdditiveOnPairs k f := fun A ↦
    hadd (fun i ↦ (A i).1) (fun i ↦ (A i).2) (fun i ↦ (A i).1.2) (fun i ↦ (A i).2.2)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨c, hc⟩ := linear_on_pairs (by omega : 4 ≤ j) addPairs
  have onSum {n : ℕ} (h : Represented (j + 1) n) : f n = c * n := by
    obtain ⟨A, rfl⟩ := h
    simp only [addPairs A, hc, Nat.cast_sum, Finset.mul_sum]
  let B := 2 * (j + 1) + 14
  have large (n : ℕ) (hn : B ≤ n) : f n = c * n :=
    onSum (represented_of_large (by omega) hn)
  have hβval : f β = c * β := by
    rcases hβ with ⟨a, b, ha, hb, rfl⟩ | ⟨t, ht, rfl⟩ | h
    · exact hc (⟨a, ha⟩, ⟨b, hb⟩)
    · exact onSum (represented_of_offset (by omega) ht)
    · exact large _ h
  have hne : c ≠ 0 := fun h ↦ hfβ (by rw [hβval, h, zero_mul])
  -- A large factor congruent to one modulo n lets us cancel the nonzero slope.
  intro n hn
  let m := n * B + 1
  have hm : B ≤ m := (Nat.le_mul_of_pos_left B hn).trans (Nat.le_succ _)
  have hcop : n.Coprime m := (Nat.coprime_mul_left_add_right n 1 B).mpr (Nat.coprime_one_right _)
  have eq := hf.map_mul_of_coprime hcop
  rw [large _ (hm.trans (Nat.le_mul_of_pos_left m hn)), large _ hm, Nat.cast_mul] at eq
  apply mul_right_cancel₀ (mul_ne_zero hne (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (n * B))))
  linear_combination -eq

end MetaMathlibExt
