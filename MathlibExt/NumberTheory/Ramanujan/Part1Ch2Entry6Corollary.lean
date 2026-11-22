/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.GroupTheory.Finiteness
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Parity

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Corollary to Entry 6

Harmonic sum from 1 equals r plus a weighted 27k³-3k reciprocal sum.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry6Corollary

/-- **The tripling sequence starting at zero.** For a natural number $k$, let
$A(k) = (3^k - 1)/2 = 1 + 3 + \cdots + 3^{k-1}$, a natural number with $A(0) = 0$. -/
def A (k : ℕ) : ℕ := (3 ^ k - 1) / 2

/-- **Twice the tripling sequence plus one is a power of three.** For every natural number
$k$, $2A(k) + 1 = 3^k$, where $A(k) = (3^k - 1)/2$; in particular the division by $2$ in the
definition of $A(k)$ is exact. -/
theorem A_two_mul_add_one (k : ℕ) : 2 * A k + 1 = 3 ^ k := by
  have hodd : Odd (3 ^ k) := Odd.pow (by norm_num)
  obtain ⟨t, ht⟩ := hodd
  unfold A
  rw [ht]
  omega

@[simp] theorem A_zero : A 0 = 0 := by simp [A]

@[simp] theorem A_succ (k : ℕ) : A (k + 1) = 3 * A k + 1 := by
  have h1 := A_two_mul_add_one k
  have h2 := A_two_mul_add_one (k + 1)
  have h3 : 3 ^ (k + 1) = 3 ^ k * 3 := pow_succ 3 k
  omega

private lemma partial_frac (m : ℕ) (hm : 0 < m) :
    (1 : ℚ) / (3 * (m : ℚ) - 1) + 1 / (3 * (m : ℚ) + 1)
      = 2 / (3 * (m : ℚ)) + 2 / ((3 * (m : ℚ)) ^ 3 - 3 * (m : ℚ)) := by
  have hle : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have h1 : (3 : ℚ) * (m : ℚ) - 1 ≠ 0 := by
    have h3 : (3 : ℚ) ≤ 3 * (m : ℚ) := by linarith
    intro h
    have := sub_eq_zero.mp h
    linarith
  have h2 : (3 : ℚ) * (m : ℚ) + 1 ≠ 0 := by positivity
  have h3 : (3 : ℚ) * (m : ℚ) ≠ 0 := by positivity
  have e : (3 * (m : ℚ)) ^ 3 - 3 * (m : ℚ)
      = (3 * (m : ℚ) - 1) * (3 * (m : ℚ)) * (3 * (m : ℚ) + 1) := by ring
  rw [e]
  field_simp
  ring

private lemma step_arith (N : ℕ) :
    (1 : ℚ) / (((3 * (N + 1) - 1 : ℕ)) : ℚ) + 1 / ((((3 * (N + 1) : ℕ))) : ℚ)
      + 1 / ((((3 * (N + 1) + 1 : ℕ))) : ℚ)
      = 1 / ((((N + 1 : ℕ))) : ℚ)
        + 2 / ((3 * ((((N + 1 : ℕ))) : ℚ)) ^ 3 - 3 * ((((N + 1 : ℕ))) : ℚ)) := by
  have hm : 0 < N + 1 := Nat.succ_pos N
  have c1 : (((3 * (N + 1) - 1 : ℕ)) : ℚ) = 3 * (((N + 1 : ℕ)) : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 3 * (N + 1))]
    push_cast
    ring
  have c2 : (((3 * (N + 1) : ℕ)) : ℚ) = 3 * (((N + 1 : ℕ)) : ℚ) := by push_cast; ring
  have c3 : (((3 * (N + 1) + 1 : ℕ)) : ℚ) = 3 * (((N + 1 : ℕ)) : ℚ) + 1 := by
    push_cast; ring
  rw [c1, c2, c3]
  have hp := partial_frac (N + 1) hm
  have hmne : ((((N + 1 : ℕ))) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h3m : 3 * ((((N + 1 : ℕ))) : ℚ) ≠ 0 := mul_ne_zero (by norm_num) hmne
  have hmul : (1 : ℚ) / (3 * ((((N + 1 : ℕ))) : ℚ))
      + 2 / (3 * ((((N + 1 : ℕ))) : ℚ)) = 1 / ((((N + 1 : ℕ))) : ℚ) := by
    field_simp
    ring
  linear_combination hp + hmul

private lemma peel3 (f : ℕ → ℚ) (M : ℕ) (hM : 1 ≤ M) :
    ∑ j ∈ Finset.Icc 1 (M + 3), f j
      = ∑ j ∈ Finset.Icc 1 M, f j + (f (M + 1) + f (M + 2) + f (M + 3)) := by
  have s1 := Finset.sum_Icc_succ_top (a := 1) (b := M + 2) (by omega) f
  have s2 := Finset.sum_Icc_succ_top (a := 1) (b := M + 1) (by omega) f
  have s3 := Finset.sum_Icc_succ_top (a := 1) (b := M) (by omega) f
  have e1 : M + 2 + 1 = M + 3 := by omega
  have e2 : M + 1 + 1 = M + 2 := by omega
  rw [e1] at s1
  rw [e2] at s2
  rw [s1, s2, s3]
  ring

private lemma triple (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 (3 * N + 1), (1 : ℚ) / (j : ℚ)
      = ∑ j ∈ Finset.Icc 1 N, (1 : ℚ) / (j : ℚ) + 1
        + 2 * ∑ i ∈ Finset.Icc 1 N, (1 : ℚ) / ((3 * (i : ℚ)) ^ 3 - 3 * (i : ℚ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have eb : 3 * (N + 1) + 1 = (3 * N + 1) + 3 := by ring
    rw [eb]
    have pe := peel3 (fun j => (1 : ℚ) / (j : ℚ)) (3 * N + 1) (by omega)
    rw [pe]
    have q1 := Finset.sum_Icc_succ_top (a := 1) (b := N) (by omega : 1 ≤ N + 1)
      (fun j => (1 : ℚ) / (j : ℚ))
    have q2 := Finset.sum_Icc_succ_top (a := 1) (b := N) (by omega : 1 ≤ N + 1)
      (fun i => (1 : ℚ) / ((3 * (i : ℚ)) ^ 3 - 3 * (i : ℚ)))
    rw [q1, q2, ih]
    have n1 : 3 * N + 1 + 1 = 3 * (N + 1) - 1 := by omega
    have n2 : 3 * N + 1 + 2 = 3 * (N + 1) := by omega
    have n3 : 3 * N + 1 + 3 = 3 * (N + 1) + 1 := by omega
    rw [n1, n2, n3]
    have st := step_arith N
    linear_combination st

private lemma block (r : ℕ) :
    ∑ i ∈ Finset.Icc 1 (A r), (1 : ℚ) / ((3 * (i : ℚ)) ^ 3 - 3 * (i : ℚ))
      = ∑ k ∈ Finset.Icc 1 r,
          ∑ j ∈ Finset.Icc (A (k - 1) + 1) (A k),
            (1 : ℚ) / ((3 * (j : ℚ)) ^ 3 - 3 * (j : ℚ)) := by
  induction r with
  | zero => rw [A_zero]; simp
  | succ r ih =>
    have hle : A r ≤ A (r + 1) := by rw [A_succ]; omega
    have hsplit : Finset.Icc 1 (A (r + 1))
        = Finset.Icc 1 (A r) ∪ Finset.Icc (A r + 1) (A (r + 1)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    have hdisj : Disjoint (Finset.Icc 1 (A r)) (Finset.Icc (A r + 1) (A (r + 1))) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_Icc] at hx1 hx2
      omega
    rw [hsplit, Finset.sum_union hdisj, ih]
    have qr := Finset.sum_Icc_succ_top (a := 1) (b := r) (by omega : 1 ≤ r + 1)
      (fun k => ∑ j ∈ Finset.Icc (A (k - 1) + 1) (A k),
        (1 : ℚ) / ((3 * (j : ℚ)) ^ 3 - 3 * (j : ℚ)))
    rw [qr]
    have er : r + 1 - 1 = r := by omega
    rw [er]

private lemma weight (f : ℕ → ℚ) (r : ℕ) :
    ∑ k ∈ Finset.Icc 1 r, ((((r + 1 - k : ℕ))) : ℚ) * f k
      = ∑ k ∈ Finset.Icc 1 (r - 1), ((((r - k : ℕ))) : ℚ) * f k
        + ∑ k ∈ Finset.Icc 1 r, f k := by
  cases r with
  | zero => simp
  | succ m =>
    have em : m + 1 - 1 = m := by omega
    rw [em]
    have peel1 := Finset.sum_Icc_succ_top (a := 1) (b := m) (by omega : 1 ≤ m + 1)
      (fun k => ((((m + 1 + 1 - k : ℕ))) : ℚ) * f k)
    have peel2 := Finset.sum_Icc_succ_top (a := 1) (b := m) (by omega : 1 ≤ m + 1) f
    rw [peel1, peel2]
    have pw : ∀ k ∈ Finset.Icc 1 m,
        ((((m + 1 + 1 - k : ℕ))) : ℚ) * f k
          = ((((m + 1 - k : ℕ))) : ℚ) * f k + f k := by
      intro k hk
      have hkm : k ≤ m := (Finset.mem_Icc.mp hk).2
      have h : m + 1 + 1 - k = (m + 1 - k) + 1 := by omega
      rw [h]
      push_cast
      ring
    have pc : ∑ k ∈ Finset.Icc 1 m, ((((m + 1 + 1 - k : ℕ))) : ℚ) * f k
        = ∑ k ∈ Finset.Icc 1 m, (((((m + 1 - k : ℕ))) : ℚ) * f k + f k) :=
      Finset.sum_congr rfl pw
    rw [pc, Finset.sum_add_distrib]
    have elast : m + 1 + 1 - (m + 1) = 1 := by omega
    have elast' : ((((m + 1 + 1 - (m + 1) : ℕ))) : ℚ) * f (m + 1) = f (m + 1) := by
      rw [elast]
      simp
    rw [elast']
    ring

private lemma main_aux (r : ℕ) :
    ∑ j ∈ Finset.Icc 1 (A r), (1 : ℚ) / (j : ℚ)
      = (r : ℚ) + 2 * ∑ k ∈ Finset.Icc 1 (r - 1),
        ((((r - k : ℕ))) : ℚ) *
            ∑ j ∈ Finset.Icc (A (k - 1) + 1) (A k),
              (1 : ℚ) / ((3 * (j : ℚ)) ^ 3 - 3 * (j : ℚ)) := by
  induction r with
  | zero => rw [A_zero]; simp
  | succ r ih =>
    have hA : A (r + 1) = 3 * A r + 1 := A_succ r
    have htr := triple (A r)
    have hbl := block r
    have hw := weight
      (fun k => ∑ j ∈ Finset.Icc (A (k - 1) + 1) (A k),
        (1 : ℚ) / ((3 * (j : ℚ)) ^ 3 - 3 * (j : ℚ))) r
    have er : r + 1 - 1 = r := by omega
    have cr : ((((r + 1 : ℕ))) : ℚ) = (r : ℚ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [hA, htr, hbl, ih, er, cr]
    linear_combination -2 * hw

/-- **Ramanujan's harmonic sum identity (corollary to Entry 6, general form).** For every
natural number $r$, the following identity holds in $\mathbb{Q}$:
$$
\sum_{j=1}^{A(r)} \frac{1}{j} = r + 2 \sum_{k=1}^{r-1} (r - k)
\sum_{j=A(k-1)+1}^{A(k)} \frac{1}{(3j)^3 - 3j},
$$
where $A(k) = (3^k - 1)/2$ and a sum over an empty range is $0$. For $r = 0$ both sides are $0$.
-/
theorem ramanujan_part1_ch2_entry6_corollary_general (r : ℕ) :
    ∑ j ∈ Finset.Icc 1 (A r), (1 : ℚ) / (j : ℚ) = (r : ℚ) + 2 * ∑ k ∈ Finset.Icc 1 (r - 1),
        ((r - k : ℕ) : ℚ) *
            ∑ j ∈ Finset.Icc (A (k - 1) + 1) (A k), (1 : ℚ) / ((3 * (j : ℚ)) ^ 3 - 3 * (j : ℚ)) := by
  exact main_aux r

set_option linter.unusedVariables false in
/-- **Ramanujan's harmonic sum identity (corollary to Entry 6).** For every natural number
$r > 0$, the following identity holds in $\mathbb{Q}$:
$$
\sum_{j=1}^{A(r)} \frac{1}{j} = r + 2 \sum_{k=1}^{r-1} (r - k)
\sum_{j=A(k-1)+1}^{A(k)} \frac{1}{(3j)^3 - 3j},
$$
where $A(k) = (3^k - 1)/2 = 1 + 3 + \cdots + 3^{k-1}$ and a sum over an empty range is $0$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 2,
    corollary to Entry 6, printed p. 33 / PDF p. 43.
Proves `Wanted` entry `ramanujan_part1_ch2_entry6_corollary`.
-/
theorem ramanujan_part1_ch2_entry6_corollary (r : ℕ) (hr : 0 < r) :
    ∑ j ∈ Finset.Icc 1 (A r), (1 : ℚ) / (j : ℚ) = (r : ℚ) + 2 * ∑ k ∈ Finset.Icc 1 (r - 1),
        ((r - k : ℕ) : ℚ) *
            ∑ j ∈ Finset.Icc (A (k - 1) + 1) (A k), (1 : ℚ) / ((3 * (j : ℚ)) ^ 3 - 3 * (j : ℚ)) :=
  ramanujan_part1_ch2_entry6_corollary_general ..

end Entry6Corollary

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
