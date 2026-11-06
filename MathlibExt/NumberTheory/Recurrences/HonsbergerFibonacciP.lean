/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
import Lean.Elab.Tactic.Omega

/-! # Honsberger's identity for Fibonacci p-numbers

This file defines the Fibonacci `p`-numbers, proves their basic recurrence properties and their
specialization to the ordinary Fibonacci numbers, and proves Honsberger's identity.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Fibonacci p-numbers.** For a natural number $p$, the Fibonacci $p$-numbers are the
natural numbers $F_p(r)$, $r \in \mathbb{N}$, given by $F_p(0) = 0$, $F_p(r) = 1$ for
$1 \le r \le p$, and $F_p(r) = F_p(r-1) + F_p(r-p-1)$ for $r > p$.

Source: Definition binds source lines 79-85
with source-text SHA-256 `d9bb7efe9d48a303e5c3db6559ba63bcbaf2967585215ca8b11ee32311955a00`.
From `https://cs.uwaterloo.ca/journals/JIS/VOL27/Kuhapatanakul/kuha13.tex`,
source-file SHA-256 `dad9ca89271449561bda39a96e5705728a24469f6106405f6b2cc021c3d16524`,
stable ID `jis_grounded_9dbbcac802edaa76c96bd1ff`. Corrected accounting:
2 mentions / 1 paper / 1 proof use. Excludes the downstream generalized
Leonardo identity and the separate finite-sum identity. -/
def fibonacciP (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 =>
    if r + 1 ≤ p then 1 else fibonacciP p r + fibonacciP p (r - p)
termination_by r => r
decreasing_by
  · exact Nat.lt_succ_self _
  · exact Nat.lt_succ_of_le (Nat.sub_le _ _)

/-- **Zeroth Fibonacci p-number.** For every natural number $p$, the Fibonacci $p$-number
$F_p(0)$ equals $0$. -/
@[simp]
theorem fibonacciP_zero (p : ℕ) : fibonacciP p 0 = 0 := by
  rw [fibonacciP]

/-- **Initial Fibonacci p-numbers equal one.** For all natural numbers $p$ and $r$ with
$1 \le r \le p$, the Fibonacci $p$-number $F_p(r)$ equals $1$. -/
theorem fibonacciP_eq_one (p r : ℕ) (hr : 1 ≤ r) (hrp : r ≤ p) : fibonacciP p r = 1 := by
  cases r with
  | zero => omega
  | succ r => simp [fibonacciP, hrp]

/-- **Recurrence for Fibonacci p-numbers.** For all natural numbers $p$ and $r$ with $p < r$,
the Fibonacci $p$-numbers satisfy $F_p(r) = F_p(r-1) + F_p(r-p-1)$. -/
theorem fibonacciP_rec (p r : ℕ) (hpr : p < r) :
    fibonacciP p r = fibonacciP p (r - 1) + fibonacciP p (r - p - 1) := by
  cases r with
  | zero => omega
  | succ r =>
    have hnot : ¬r + 1 ≤ p := by omega
    have hsub : r + 1 - p - 1 = r - p := by omega
    simp [fibonacciP, hnot, hsub]

/-- **Fibonacci 1-numbers are the Fibonacci numbers.** For every natural number $n$, the
Fibonacci $1$-number $F_1(n)$ equals the $n$-th Fibonacci number $f_n$, where $f_0 = 0$,
$f_1 = 1$ and $f_{k+2} = f_{k+1} + f_k$. -/
theorem fibonacciP_one (n : ℕ) : fibonacciP 1 n = Nat.fib n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      cases n with
      | zero => simp [fibonacciP]
      | succ n =>
        change fibonacciP 1 (n + 2) = Nat.fib (n + 2)
        rw [fibonacciP_rec 1 (n + 2) (by omega)]
        rw [show n + 2 - 1 = n + 1 by omega]
        rw [show n + 1 - 1 = n by omega]
        rw [ih (n + 1) (by omega), ih n (by omega), Nat.fib_add_two]
        omega

private theorem honsberger_uniform_recurrence
    (p : ℕ) (f : ℕ → ℕ)
    (hzero : f 0 = 0)
    (hone : ∀ r, 1 ≤ r → r ≤ p → f r = 1)
    (hrec : ∀ r, p < r → f r = f (r - 1) + f (r - p - 1))
    (r : ℕ) (hr : 1 ≤ r) :
    f (r + 1) = f r + f (r - p) := by
  by_cases hle : r + 1 ≤ p
  · have hrp : r ≤ p := by omega
    have hsub : r - p = 0 := by omega
    rw [hone (r + 1) (by omega) hle, hone r hr hrp, hsub, hzero]
  · have hgt : p < r + 1 := by omega
    rw [hrec (r + 1) hgt]
    have hpred : r + 1 - 1 = r := by omega
    have hsub : r + 1 - p - 1 = r - p := by omega
    rw [hpred, hsub]

private theorem honsberger_telescope
    (p n k : ℕ) (f : ℕ → ℕ)
    (hzero : f 0 = 0)
    (hone : ∀ r, 1 ≤ r → r ≤ p → f r = 1)
    (hrec : ∀ r, p < r → f r = f (r - 1) + f (r - p - 1)) :
    f (n + 2) + ∑ j ∈ Finset.range k, f (n + j + 2 - p) = f (n + k + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    rw [← honsberger_uniform_recurrence p f hzero hone hrec (n + k + 2) (by omega)]
    congr 1

private theorem honsberger_base
    (p m n : ℕ) (f : ℕ → ℕ) (hp : 0 < p)
    (hzero : f 0 = 0)
    (hone : ∀ r, 1 ≤ r → r ≤ p → f r = 1)
    (hrec : ∀ r, p < r → f r = f (r - 1) + f (r - p - 1))
    (hm : m ≤ p) :
    f (m + 1) * f (n + 2) +
        ∑ j ∈ Finset.range p, f (m + 1 - (j + 1)) * f (n + (j + 1) + 1 - p) =
      f (m + n + 2) := by
  have hfm1 : f (m + 1) = 1 := by
    by_cases hmp : m < p
    · exact hone (m + 1) (by omega) (by omega)
    · have hmp_eq : m = p := by omega
      subst m
      rw [honsberger_uniform_recurrence p f hzero hone hrec p hp]
      rw [hone p hp le_rfl, Nat.sub_self, hzero]
  have hsubset : Finset.range m ⊆ Finset.range p := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  have hsum :
      (∑ j ∈ Finset.range p,
          f (m + 1 - (j + 1)) * f (n + (j + 1) + 1 - p)) =
        ∑ j ∈ Finset.range m, f (n + j + 2 - p) := by
    calc
      (∑ j ∈ Finset.range p,
          f (m + 1 - (j + 1)) * f (n + (j + 1) + 1 - p)) =
          ∑ j ∈ Finset.range m,
            f (m + 1 - (j + 1)) * f (n + (j + 1) + 1 - p) := by
            symm
            apply Finset.sum_subset hsubset
            intro j hjp hjm
            simp only [Finset.mem_range] at hjp hjm
            have hidx : m + 1 - (j + 1) = 0 := by omega
            rw [hidx, hzero, zero_mul]
      _ = ∑ j ∈ Finset.range m, f (n + j + 2 - p) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < m := Finset.mem_range.mp hj
        have hfirst : m + 1 - (j + 1) = m - j := by omega
        have hpos : 1 ≤ m - j := by omega
        have hle : m - j ≤ p := by omega
        have hsecond : n + (j + 1) + 1 - p = n + j + 2 - p := by omega
        rw [hfirst, hone (m - j) hpos hle, one_mul, hsecond]
  rw [hfm1, one_mul, hsum]
  rw [honsberger_telescope p n m f hzero hone hrec]
  congr 1
  omega

private theorem honsberger_induction_step
    (p m n : ℕ) (f : ℕ → ℕ)
    (hzero : f 0 = 0)
    (hone : ∀ r, 1 ≤ r → r ≤ p → f r = 1)
    (hrec : ∀ r, p < r → f r = f (r - 1) + f (r - p - 1))
    (hpm : p < m)
    (hprev :
      f ((m - 1) + 1) * f (n + 2) +
          ∑ j ∈ Finset.range p,
            f ((m - 1) + 1 - (j + 1)) * f (n + (j + 1) + 1 - p) =
        f ((m - 1) + n + 2))
    (hback :
      f ((m - p - 1) + 1) * f (n + 2) +
          ∑ j ∈ Finset.range p,
            f ((m - p - 1) + 1 - (j + 1)) * f (n + (j + 1) + 1 - p) =
        f ((m - p - 1) + n + 2)) :
    f (m + 1) * f (n + 2) +
        ∑ j ∈ Finset.range p,
          f (m + 1 - (j + 1)) * f (n + (j + 1) + 1 - p) =
      f (m + n + 2) := by
  have hfm := honsberger_uniform_recurrence p f hzero hone hrec m (by omega)
  have hsum :
      (∑ j ∈ Finset.range p,
          f (m + 1 - (j + 1)) * f (n + (j + 1) + 1 - p)) =
        (∑ j ∈ Finset.range p,
          f ((m - 1) + 1 - (j + 1)) * f (n + (j + 1) + 1 - p)) +
        ∑ j ∈ Finset.range p,
          f ((m - p - 1) + 1 - (j + 1)) * f (n + (j + 1) + 1 - p) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjp : j < p := Finset.mem_range.mp hj
    have hr : 1 ≤ m - 1 - j := by omega
    have hleft : m + 1 - (j + 1) = (m - 1 - j) + 1 := by omega
    have hprev_index : (m - 1) + 1 - (j + 1) = m - 1 - j := by omega
    have hback_index : (m - p - 1) + 1 - (j + 1) = m - 1 - j - p := by omega
    rw [hleft, honsberger_uniform_recurrence p f hzero hone hrec (m - 1 - j) hr]
    rw [add_mul, hprev_index, hback_index]
  have hm_prev_index : m = (m - 1) + 1 := by omega
  have hm_back_index : m - p = (m - p - 1) + 1 := by omega
  have hfm_prev : f m = f ((m - 1) + 1) := congrArg f hm_prev_index
  have hfm_back : f (m - p) = f ((m - p - 1) + 1) := congrArg f hm_back_index
  have hprev' := hprev
  have hback' := hback
  have hprev_result : (m - 1) + n + 2 = m + n + 1 := by omega
  have hback_result : (m - p - 1) + n + 2 = m + n + 1 - p := by omega
  rw [hprev_result] at hprev'
  rw [hback_result] at hback'
  have hfinal :=
    honsberger_uniform_recurrence p f hzero hone hrec (m + n + 1) (by omega)
  have hfinal_index : m + n + 1 + 1 = m + n + 2 := by omega
  rw [hfinal_index] at hfinal
  rw [hfm, hsum, add_mul, hfm_prev, hfm_back]
  omega

private theorem honsberger_generic
    (p m n : ℕ) (f : ℕ → ℕ) (hp : 0 < p)
    (hzero : f 0 = 0)
    (hone : ∀ r, 1 ≤ r → r ≤ p → f r = 1)
    (hrec : ∀ r, p < r → f r = f (r - 1) + f (r - p - 1)) :
    f (m + 1) * f (n + 2) +
        ∑ j ∈ Finset.range p,
          f (m + 1 - (j + 1)) * f (n + (j + 1) + 1 - p) =
      f (m + n + 2) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m ≤ p
    · exact honsberger_base p m n f hp hzero hone hrec hm
    · exact honsberger_induction_step p m n f hzero hone hrec (by omega)
        (ih (m - 1) (by omega)) (ih (m - p - 1) (by omega))

/-- **Honsberger identity for Fibonacci p-numbers.** Let $p$, $m$ and $n$ be positive integers
with $p \le m + 1$ and $p \le n + 2$, and write $F_p(r)$ for the Fibonacci $p$-numbers. Suppose
that $F_p(0) = 0$, that $F_p(r) = 1$ for $1 \le r \le p$, and that
$F_p(r) = F_p(r-1) + F_p(r-p-1)$ for $r > p$ (these hold by definition). Then
$$F_p(m+1)\,F_p(n+2) + \sum_{i=1}^{p} F_p(m+1-i)\,F_p(n+i+1-p) = F_p(m+n+2).$$

All indices in the sum are natural numbers, since $i \le p \le m + 1$ and
$n + i + 1 \ge n + 2 \ge p$.

Proof: by strong induction on $m$ from a uniform form of the recurrence, with a telescoping
base case.

Source: Binds source lines 425-449
with source-text SHA-256 `754dee8cf3e11595590ad2539aee76a3ad6d7ffcb80282b6a4488271f6392bd9`.
From `https://cs.uwaterloo.ca/journals/JIS/VOL27/Kuhapatanakul/kuha13.tex`,
source-file SHA-256 `dad9ca89271449561bda39a96e5705728a24469f6106405f6b2cc021c3d16524`,
stable ID `jis_grounded_9dbbcac802edaa76c96bd1ff`. Corrected accounting:
2 mentions / 1 paper / 1 proof use. Excludes the downstream generalized
Leonardo identity and the separate finite-sum identity. Definition from lines 79-85.
Proves `Wanted` entry `honsberger_fibonacciP`.
-/
theorem honsberger_fibonacciP
    (p m n : ℕ) (hp : 0 < p) (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hm : p ≤ m + 1) (hn : p ≤ n + 2) :
    fibonacciP p 0 = 0 →
    (∀ r, 1 ≤ r → r ≤ p → fibonacciP p r = 1) →
    (∀ r, p < r →
      fibonacciP p r =
        fibonacciP p (r - 1) + fibonacciP p (r - p - 1)) →
    fibonacciP p (m + 1) * fibonacciP p (n + 2) +
        ∑ j ∈ Finset.range p,
          fibonacciP p (m + 1 - (j + 1)) *
            fibonacciP p (n + (j + 1) + 1 - p) =
      fibonacciP p (m + n + 2) := by
  intro hzero hone hrec
  exact honsberger_generic p m n (fibonacciP p) hp hzero hone hrec

end

end MetaMathlibExt
