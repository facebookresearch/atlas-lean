/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import MathlibExt.NumberTheory.GenLeonardo
import Mathlib.Tactic.Ring

/-!
# Hyper-Leonardo numbers

Statements from Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino,
*A Note on Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48.

The Leonardo numbers are `genLeonardo 1` (`Le₀ = Le₁ = 1`, `Le_{n+2} = Le_{n+1} + Le_n + 1`).
The hyper-Leonardo numbers are their iterated partial sums,
`Le^{(0)}_n = Le_n` and `Le^{(r)}_n = ∑_{k=0}^{n} Le^{(r-1)}_k`; the hyper-Fibonacci numbers
`F^{(r)}_n` are the iterated partial sums of `Nat.fib`.
-/

namespace MetaMathlibExt

@[expose] public section

open PowerSeries

/-- **Hyper-Leonardo numbers.** Let $Le_n$ be the Leonardo numbers, defined by
$Le_0 = Le_1 = 1$ and $Le_{n+2} = Le_{n+1} + Le_n + 1$. The hyper-Leonardo numbers are the
integers $Le^{(r)}_n$, for $r, n \ge 0$, defined by $Le^{(0)}_n = Le_n$ and
$Le^{(r+1)}_n = \sum_{k=0}^{n} Le^{(r)}_k$.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Definition 1, as displayed in
the derivation `Le^{(1)}_n = ∑_{k=0}^{n} Le^{(0)}_k` after Proposition 5
(`integers-2026-A48-prop-5`). -/
def hyperLeonardo : ℕ → ℕ → ℤ
  | 0, n => genLeonardo 1 n
  | r + 1, n => ∑ k ∈ Finset.range (n + 1), hyperLeonardo r k

/-- **Hyper-Leonardo numbers of order zero.** For every natural number $n$, the hyper-Leonardo
number $Le^{(0)}_n$ equals the Leonardo number $L_{1,n}$, the generalized Leonardo number with
$k = 1$, given by $L_{1,0} = L_{1,1} = 1$ and $L_{1,n+2} = L_{1,n+1} + L_{1,n} + 1$.

Source: Spreafico and Catarino, INTEGERS 26 (2026), Article A48, Definition 1. -/
theorem hyperLeonardo_zero (n : ℕ) : hyperLeonardo 0 n = genLeonardo 1 n := rfl

/-- **Hyper-Leonardo numbers as partial sums.** For all natural numbers $r$ and $n$, the
hyper-Leonardo numbers $Le^{(r)}_n$ satisfy $Le^{(r+1)}_n = \sum_{k=0}^{n} Le^{(r)}_k$.

Source: Spreafico and Catarino, INTEGERS 26 (2026), Article A48, Definition 1. -/
theorem hyperLeonardo_succ (r n : ℕ) :
    hyperLeonardo (r + 1) n = ∑ k ∈ Finset.range (n + 1), hyperLeonardo r k := rfl

/-- **First hyper-Leonardo numbers of order one.** The hyper-Leonardo numbers $Le^{(1)}_n$ of
order $1$ satisfy $Le^{(1)}_0 = 1$, $Le^{(1)}_1 = 2$, $Le^{(1)}_2 = 5$ and $Le^{(1)}_3 = 10$.

Source: Spreafico and Catarino, INTEGERS 26 (2026), Article A48, Proposition 1
(`Le^{(1)}_0 = 1`, `Le^{(1)}_1 = 2`). -/
theorem hyperLeonardo_one_small :
    hyperLeonardo 1 0 = 1 ∧ hyperLeonardo 1 1 = 2 ∧ hyperLeonardo 1 2 = 5 ∧
      hyperLeonardo 1 3 = 10 := by
  simp [hyperLeonardo, Finset.sum_range_succ, genLeonardo]

/-- **Hyper-Fibonacci numbers.** The hyper-Fibonacci numbers $F^{(r)}_n$, for natural numbers $r$
and $n$, are the natural numbers defined by $F^{(0)}_n = F_n$, the $n$-th Fibonacci number
(with $F_0 = 0$ and $F_1 = 1$), and $F^{(r+1)}_n = \sum_{k=0}^{n} F^{(r)}_k$.

Source: Spreafico and Catarino, INTEGERS 26 (2026), Article A48, the hyper-Fibonacci
numbers `F^{(r)}_{n+1} = ∑_{k=0}^{n+1} F^{(r-1)}_k` displayed after Proposition 5
(`integers-2026-A48-prop-5`). -/
def hyperFibonacci : ℕ → ℕ → ℕ
  | 0, n => Nat.fib n
  | r + 1, n => ∑ k ∈ Finset.range (n + 1), hyperFibonacci r k

/-- **Hyper-Fibonacci numbers of order zero.** For every natural number $n$, the hyper-Fibonacci
number $F^{(0)}_n$ equals the $n$-th Fibonacci number $F_n$ (with $F_0 = 0$ and $F_1 = 1$).

Source: Spreafico and Catarino, INTEGERS 26 (2026), Article A48, after Proposition 5. -/
theorem hyperFibonacci_zero (n : ℕ) : hyperFibonacci 0 n = Nat.fib n := rfl

/-- **Hyper-Fibonacci numbers as partial sums.** For all natural numbers $r$ and $n$, the
hyper-Fibonacci numbers $F^{(r)}_n$ satisfy $F^{(r+1)}_n = \sum_{k=0}^{n} F^{(r)}_k$.

Source: Spreafico and Catarino, INTEGERS 26 (2026), Article A48, after Proposition 5. -/
theorem hyperFibonacci_succ (r n : ℕ) :
    hyperFibonacci (r + 1) n = ∑ k ∈ Finset.range (n + 1), hyperFibonacci r k := rfl

/-- **Small values of the hyper-Fibonacci numbers of order one.** The hyper-Fibonacci numbers
$F^{(1)}_n$ of order $1$ satisfy $F^{(1)}_0 = 0$, $F^{(1)}_1 = 1$, $F^{(1)}_2 = 2$ and
$F^{(1)}_3 = 4$.

Source: Spreafico and Catarino, INTEGERS 26 (2026), Article A48, after Proposition 5
(`F^{(r)}_0 = 0`). -/
theorem hyperFibonacci_one_small :
    hyperFibonacci 1 0 = 0 ∧ hyperFibonacci 1 1 = 1 ∧ hyperFibonacci 1 2 = 2 ∧
      hyperFibonacci 1 3 = 4 := by
  simp [hyperFibonacci, Finset.sum_range_succ, Nat.fib_add_two]

/-- **Generating function of shifted binomial coefficients.** For every natural number $r$, the
formal power series $\sum_{n \ge 0} \binom{n+r}{r} t^n$ with integer coefficients satisfies
$\left(\sum_{n \ge 0} \binom{n+r}{r} t^n\right)(1-t)^{r+1} = 1$ in $\mathbb{Z}[[t]]$, that is,
$\sum_{n \ge 0} \binom{n+r}{r} t^n = 1/(1-t)^{r+1}$.

The paper states this for positive $r$; it holds for every $r \ge 0$ and is stated so.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Lemma 2
(`integers-2026-A48-lem-2`). -/
public theorem choose_add_powerSeries_mul_one_sub_pow (r : ℕ) :
    PowerSeries.mk (fun n => (((n + r).choose r : ℕ) : ℤ)) * (1 - X) ^ (r + 1) = 1 := by
  have h : PowerSeries.mk (fun n => (((n + r).choose r : ℕ) : ℤ)) =
      (PowerSeries.mk 1 : ℤ⟦X⟧) ^ (r + 1) := by
    rw [PowerSeries.mk_one_pow_eq_mk_choose_add]
    congr 1
    funext n
    rw [add_comm]
  rw [h, ← mul_pow, PowerSeries.mk_one_mul_one_sub_eq_one, one_pow]

/-- **Generating function of the hyper-Leonardo numbers.** For every natural number $r$, the
formal power series $\sum_{n \ge 0} \mathrm{Le}^{(r)}_n t^n$ of the hyper-Leonardo numbers of
order $r$ satisfies
$\left(\sum_{n \ge 0} \mathrm{Le}^{(r)}_n t^n\right)(1-2t+t^3)(1-t)^r = 1-t+t^2$ in
$\mathbb{Z}[[t]]$, that is,
$\sum_{n \ge 0} \mathrm{Le}^{(r)}_n t^n = \frac{1-t+t^2}{(1-2t+t^3)(1-t)^r}$.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Theorem 1, Equation (10)
(`integers-2026-A48-thm-1`). -/
theorem hyperLeonardo_generatingFunction (r : ℕ) :
    PowerSeries.mk (fun n => hyperLeonardo r n) * ((1 - 2 * X + X ^ 3) * (1 - X) ^ r) =
      1 - X + X ^ 2 := by
  let F (r : ℕ) := PowerSeries.mk (hyperLeonardo r)
  change F r * _ = _
  induction r with
  | zero =>
    rw [pow_zero, mul_one, two_mul, mul_add, mul_sub, mul_add, mul_one]
    apply PowerSeries.ext
    rintro (_ | _ | _ | n)
    -- From degree three on, the coefficient is the difference of two consecutive recurrences.
    all_goals simp [F, coeff_mul_X_pow', coeff_X, hyperLeonardo_zero, genLeonardo]
    omega
  | succ r ih =>
    have step : F (r + 1) * (1 - X) = F r := by
      rw [mul_sub, mul_one]
      apply PowerSeries.ext
      intro n
      cases n with
      | zero => simp [F, hyperLeonardo_succ]
      | succ n =>
        simp only [map_sub, coeff_succ_mul_X, F, coeff_mk, hyperLeonardo_succ]
        rw [Finset.sum_range_succ, add_sub_cancel_left]
    rw [pow_succ' _ r, mul_left_comm _ (1 - X : ℤ⟦X⟧), ← mul_assoc, step, ih]

/-- **Generating function of the Leonardo numbers.** Let $Le_n$ be the Leonardo numbers
($Le_0 = Le_1 = 1$ and $Le_{n+2} = Le_{n+1} + Le_n + 1$), and let
$L(t) = \sum_{n \ge 0} Le_n t^n$ in the ring $\mathbb{Z}[[t]]$ of formal power series. Then
$L(t)(1 - 2t + t^3) = 1 - t + t^2$ and $L(t)(1 - t - t^2)(1 - t) = 2(1 - t) - (1 - t - t^2)$.

Equivalently, $L(t) = \frac{2}{1-t-t^2} - \frac{1}{1-t} = \frac{1-t+t^2}{1-2t+t^3}$; the
identities above are this equality with the denominators cleared.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Corollary 2
(`integers-2026-A48-cor-2`). -/
theorem leonardo_generatingFunction :
    PowerSeries.mk (fun n => genLeonardo 1 n) * (1 - 2 * X + X ^ 3) = 1 - X + X ^ 2 ∧
      PowerSeries.mk (fun n => genLeonardo 1 n) * ((1 - X - X ^ 2) * (1 - X)) =
        2 * (1 - X) - (1 - X - X ^ 2) := by
  have h := hyperLeonardo_generatingFunction 0
  simp only [hyperLeonardo_zero, pow_zero, mul_one] at h
  refine ⟨h, ?_⟩
  calc
    _ = PowerSeries.mk (genLeonardo 1) * (1 - 2 * X + X ^ 3) := by ring
    _ = 1 - X + X ^ 2 := h
    _ = _ := by ring

/-- **Generating functions of the hyper-Leonardo numbers of orders one and two.** In the ring
$\mathbb{Z}[[t]]$ of formal power series, the hyper-Leonardo numbers $Le^{(r)}_n$ satisfy
$\left(\sum_{n \ge 0} Le^{(1)}_n t^n\right)(1 - 2t + t^3)(1 - t) = 1 - t + t^2$ and
$\left(\sum_{n \ge 0} Le^{(2)}_n t^n\right)(1 - 2t + t^3)(1 - t)^2 = 1 - t + t^2$.

Equivalently, the two generating functions are $\frac{1 - t + t^2}{(1 - 2t + t^3)(1 - t)}$ and
$\frac{1 - t + t^2}{(1 - 2t + t^3)(1 - t)^2}$.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Corollary 3
(`integers-2026-A48-cor-3`). -/
theorem hyperLeonardo_one_two_generatingFunction :
    PowerSeries.mk (fun n => hyperLeonardo 1 n) * ((1 - 2 * X + X ^ 3) * (1 - X)) =
        1 - X + X ^ 2 ∧
      PowerSeries.mk (fun n => hyperLeonardo 2 n) * ((1 - 2 * X + X ^ 3) * (1 - X) ^ 2) =
        1 - X + X ^ 2 := by
  exact ⟨by simpa using hyperLeonardo_generatingFunction 1, hyperLeonardo_generatingFunction 2⟩

end

end MetaMathlibExt
