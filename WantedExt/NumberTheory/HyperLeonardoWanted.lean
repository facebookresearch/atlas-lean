/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import WantedExt.NumberTheory.GenLeonardoWanted

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

/-- The hyper-Leonardo numbers `Le^{(r)}_n`: `Le^{(0)}_n` is the Leonardo number
`genLeonardo 1 n`, and `Le^{(r+1)}_n = ∑_{k=0}^{n} Le^{(r)}_k`.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Definition 1, as displayed in
the derivation `Le^{(1)}_n = ∑_{k=0}^{n} Le^{(0)}_k` after Proposition 5
(`integers-2026-A48-prop-5`). -/
def hyperLeonardo : ℕ → ℕ → ℤ
  | 0, n => genLeonardo 1 n
  | r + 1, n => ∑ k ∈ Finset.range (n + 1), hyperLeonardo r k

/-- `Le^{(0)}_n = Le_n`.

Source: Spreafico and Catarino, INTEGERS 26 (2026), Article A48, Definition 1. -/
theorem hyperLeonardo_zero (n : ℕ) : hyperLeonardo 0 n = genLeonardo 1 n := rfl

/-- `Le^{(r+1)}_n = ∑_{k=0}^{n} Le^{(r)}_k`.

Source: Spreafico and Catarino, INTEGERS 26 (2026), Article A48, Definition 1. -/
theorem hyperLeonardo_succ (r n : ℕ) :
    hyperLeonardo (r + 1) n = ∑ k ∈ Finset.range (n + 1), hyperLeonardo r k := rfl

/-- Small values: `Le^{(1)}_0, …, Le^{(1)}_3 = 1, 2, 5, 10`.

Source: Spreafico and Catarino, INTEGERS 26 (2026), Article A48, Proposition 1
(`Le^{(1)}_0 = 1`, `Le^{(1)}_1 = 2`). -/
theorem hyperLeonardo_one_small :
    hyperLeonardo 1 0 = 1 ∧ hyperLeonardo 1 1 = 2 ∧ hyperLeonardo 1 2 = 5 ∧
      hyperLeonardo 1 3 = 10 := by
  simp [hyperLeonardo, Finset.sum_range_succ, genLeonardo]

/-- The hyper-Fibonacci numbers `F^{(r)}_n`: `F^{(0)}_n = F_n` and
`F^{(r+1)}_n = ∑_{k=0}^{n} F^{(r)}_k`.

Source: Spreafico and Catarino, INTEGERS 26 (2026), Article A48, the hyper-Fibonacci
numbers `F^{(r)}_{n+1} = ∑_{k=0}^{n+1} F^{(r-1)}_k` displayed after Proposition 5
(`integers-2026-A48-prop-5`). -/
def hyperFibonacci : ℕ → ℕ → ℕ
  | 0, n => Nat.fib n
  | r + 1, n => ∑ k ∈ Finset.range (n + 1), hyperFibonacci r k

/-- `F^{(0)}_n = F_n`.

Source: Spreafico and Catarino, INTEGERS 26 (2026), Article A48, after Proposition 5. -/
theorem hyperFibonacci_zero (n : ℕ) : hyperFibonacci 0 n = Nat.fib n := rfl

/-- `F^{(r+1)}_n = ∑_{k=0}^{n} F^{(r)}_k`.

Source: Spreafico and Catarino, INTEGERS 26 (2026), Article A48, after Proposition 5. -/
theorem hyperFibonacci_succ (r n : ℕ) :
    hyperFibonacci (r + 1) n = ∑ k ∈ Finset.range (n + 1), hyperFibonacci r k := rfl

/-- Small values: `F^{(1)}_0, …, F^{(1)}_3 = 0, 1, 2, 4`.

Source: Spreafico and Catarino, INTEGERS 26 (2026), Article A48, after Proposition 5
(`F^{(r)}_0 = 0`). -/
theorem hyperFibonacci_one_small :
    hyperFibonacci 1 0 = 0 ∧ hyperFibonacci 1 1 = 1 ∧ hyperFibonacci 1 2 = 2 ∧
      hyperFibonacci 1 3 = 4 := by
  simp [hyperFibonacci, Finset.sum_range_succ, Nat.fib_add_two]

/-- Proposition 1: `Le_n = Le_{n-1} + Le_{n-2} + 1`;
`Le^{(1)}_n = Le^{(1)}_{n-1} + Le^{(1)}_{n-2} + C(n-1, 1) + 1` with `Le^{(1)}_0 = 1`,
`Le^{(1)}_1 = 2`; and `Le^{(2)}_n = Le^{(2)}_{n-1} + Le^{(2)}_{n-2} + C(n, 2) + C(n-1, 1) + 2`
with `Le^{(2)}_0 = 1`, `Le^{(2)}_1 = 3`, all for `n ≥ 2` (written with `n + 2`).

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 1
(`integers-2026-A48-prop-1`). -/
public theorem_wanted hyperLeonardo_recurrence_small_order :
    (∀ n, hyperLeonardo 0 (n + 2) = hyperLeonardo 0 (n + 1) + hyperLeonardo 0 n + 1) ∧
    hyperLeonardo 0 0 = 1 ∧ hyperLeonardo 0 1 = 1 ∧
    (∀ n, hyperLeonardo 1 (n + 2) =
      hyperLeonardo 1 (n + 1) + hyperLeonardo 1 n + ((n + 1).choose 1 : ℕ) + 1) ∧
    hyperLeonardo 1 0 = 1 ∧ hyperLeonardo 1 1 = 2 ∧
    (∀ n, hyperLeonardo 2 (n + 2) = hyperLeonardo 2 (n + 1) + hyperLeonardo 2 n +
      ((n + 2).choose 2 : ℕ) + ((n + 1).choose 1 : ℕ) + 2) ∧
    hyperLeonardo 2 0 = 1 ∧ hyperLeonardo 2 1 = 3

/-- Proposition 2: for `r ≥ 0` and `n ≥ 2`,
`Le^{(r)}_n = r + Le^{(r)}_{n-1} + Le^{(r)}_{n-2} + C(n+r-2, r) + ∑_{j=1}^{r-1} j C(n+r-2-j, r-j)`,
with `Le^{(r)}_0 = 1` and `Le^{(r)}_1 = r + 1` (written with `n + 2`).

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 2
(`integers-2026-A48-prop-2`). -/
public theorem_wanted hyperLeonardo_recurrence (r : ℕ) :
    (∀ n, hyperLeonardo r (n + 2) = r + hyperLeonardo r (n + 1) + hyperLeonardo r n +
      ((n + r).choose r : ℕ) +
        ∑ j ∈ Finset.Ico 1 r, (j * (n + r - j).choose (r - j) : ℕ)) ∧
    hyperLeonardo r 0 = 1 ∧ hyperLeonardo r 1 = r + 1

/-- Proposition 3: `Le^{(r)}_n = Le^{(r)}_{n-1} + Le^{(r-1)}_n` for `r ≥ 1` and `n ≥ 1`
(the cases `r = 0` or `n = 0` refer to undefined terms and are omitted).

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 3, Equation (4)
(`integers-2026-A48-prop-3`). -/
public theorem_wanted hyperLeonardo_succ_succ (r n : ℕ) :
    hyperLeonardo (r + 1) (n + 1) = hyperLeonardo (r + 1) n + hyperLeonardo r (n + 1)

/-- Corollary 1: `Le^{(1)}_n = Le^{(1)}_{n-1} + Le_n` for `n ≥ 1`, the case `r = 1` of
Equation (4). The extraction drops the superscript `(1)` on `Le_{n-1}`; as printed
(`Le^{(1)}_n = Le_{n-1} + Le_n`) it fails at `n = 2` (`5 ≠ 1 + 3`).

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Corollary 1, Equation (5)
(`integers-2026-A48-cor-1`). -/
public theorem_wanted hyperLeonardo_one_succ (n : ℕ) :
    hyperLeonardo 1 (n + 1) = hyperLeonardo 1 n + genLeonardo 1 (n + 1)

/-- Lemma 2: `∑_{n ≥ 0} C(n+r, r) tⁿ = 1/(1-t)^{r+1}`, stated as
`(∑ C(n+r, r) tⁿ) (1-t)^{r+1} = 1` in `ℤ⟦t⟧`. The paper says `r` positive; the statement
holds for every `r ≥ 0` and is stated so. Proved from Mathlib's
`PowerSeries.mk_one_pow_eq_mk_choose_add` and `PowerSeries.mk_one_mul_one_sub_eq_one`.

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

/-- Lemma 3: the ordinary convolution `z_n = ∑_{k=0}^{n} x_k y_{n-k}` of two log-concave
sequences of positive reals (`x_{j-1} x_{j+1} ≤ x_j²` for `j ≥ 1`) is log-concave.
Positivity is the paper's standing assumption on log-concave sequences.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Lemma 3, quoting [1]
(`integers-2026-A48-lem-3`). -/
public theorem_wanted logConcave_convolution (x y : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hy : ∀ n, 0 < y n) (hxlc : ∀ j, 1 ≤ j → x (j - 1) * x (j + 1) ≤ x j ^ 2)
    (hylc : ∀ j, 1 ≤ j → y (j - 1) * y (j + 1) ≤ y j ^ 2) (j : ℕ) (hj : 1 ≤ j) :
    (∑ k ∈ Finset.range j, x k * y (j - 1 - k)) *
        (∑ k ∈ Finset.range (j + 2), x k * y (j + 1 - k)) ≤
      (∑ k ∈ Finset.range (j + 1), x k * y (j - k)) ^ 2

/-- Corollary 2: `∑ Le_n tⁿ = 2/(1-t-t²) - 1/(1-t) = (1-t+t²)/(1-2t+t³)`, stated as
`(∑ Le_n tⁿ)(1-2t+t³) = 1-t+t²` and `(∑ Le_n tⁿ)(1-t-t²)(1-t) = 2(1-t) - (1-t-t²)` in `ℤ⟦t⟧`.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Corollary 2
(`integers-2026-A48-cor-2`). -/
public theorem_wanted leonardo_generatingFunction :
    PowerSeries.mk (fun n => genLeonardo 1 n) * (1 - 2 * X + X ^ 3) = 1 - X + X ^ 2 ∧
      PowerSeries.mk (fun n => genLeonardo 1 n) * ((1 - X - X ^ 2) * (1 - X)) =
        2 * (1 - X) - (1 - X - X ^ 2)

/-- Corollary 3: the generating functions of `Le^{(1)}` and `Le^{(2)}` are
`(1-t+t²)/((1-2t+t³)(1-t))` and `(1-t+t²)/((1-2t+t³)(1-t)²)`, stated after clearing
denominators in `ℤ⟦t⟧`. The intermediate partial-fraction forms are not restated.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Corollary 3
(`integers-2026-A48-cor-3`). -/
public theorem_wanted hyperLeonardo_one_two_generatingFunction :
    PowerSeries.mk (fun n => hyperLeonardo 1 n) * ((1 - 2 * X + X ^ 3) * (1 - X)) =
        1 - X + X ^ 2 ∧
      PowerSeries.mk (fun n => hyperLeonardo 2 n) * ((1 - 2 * X + X ^ 3) * (1 - X) ^ 2) =
        1 - X + X ^ 2

/-- Theorem 1: `∑_{n ≥ 0} Le^{(r)}_n tⁿ = (1-t+t²)/((1-2t+t³)(1-t)^r)`, stated after
clearing denominators in `ℤ⟦t⟧`.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Theorem 1, Equation (10)
(`integers-2026-A48-thm-1`). -/
public theorem_wanted hyperLeonardo_generatingFunction (r : ℕ) :
    PowerSeries.mk (fun n => hyperLeonardo r n) * ((1 - 2 * X + X ^ 3) * (1 - X) ^ r) =
      1 - X + X ^ 2

/-- Proposition 6: `Le^{(r)}_n = 2F^{(r)}_{n+1} - C(n+r, r)` for all `n, r ≥ 0`.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 6, Equation (9)
(`integers-2026-A48-prop-6`). -/
public theorem_wanted hyperLeonardo_eq_hyperFibonacci (r n : ℕ) :
    hyperLeonardo r n = 2 * (hyperFibonacci r (n + 1) : ℤ) - ((n + r).choose r : ℕ)

/-- Proposition 10: the Leonardo numbers satisfy the log-convexity inequality
`Le_{n-1} Le_{n+1} ≥ Le_n²` at `n = 1, 3`, equality at `n = 5`, and the log-concavity
inequality `Le_n² ≥ Le_{n-1} Le_{n+1}` at `n = 2, 4` and every `n ≥ 6`. The paper's "the
sequence is log-convex for `n = 1`" is read as the defining inequality at index `n`.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 10
(`integers-2026-A48-prop-10`). -/
public theorem_wanted leonardo_logConvex_logConcave_pointwise :
    (∀ n ∈ ({1, 3} : Finset ℕ),
      genLeonardo 1 n ^ 2 ≤ genLeonardo 1 (n - 1) * genLeonardo 1 (n + 1)) ∧
    genLeonardo 1 5 ^ 2 = genLeonardo 1 4 * genLeonardo 1 6 ∧
    (∀ n, n = 2 ∨ n = 4 ∨ 6 ≤ n →
      genLeonardo 1 (n - 1) * genLeonardo 1 (n + 1) ≤ genLeonardo 1 n ^ 2)

/-- Proposition 11: the Leonardo numbers are log-balanced at `n = 3`:
`Le_2 Le_4 ≥ Le_3²` and `(Le_3/3!)² ≥ (Le_2/2!)(Le_4/4!)`.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 11, with the
definition of log-balanced displayed before Proposition 10 (`integers-2026-A48-prop-11`). -/
public theorem_wanted leonardo_logBalanced_three :
    genLeonardo 1 3 ^ 2 ≤ genLeonardo 1 2 * genLeonardo 1 4 ∧
      ((genLeonardo 1 2 : ℝ) / Nat.factorial 2) * ((genLeonardo 1 4 : ℝ) / Nat.factorial 4) ≤
        ((genLeonardo 1 3 : ℝ) / Nat.factorial 3) ^ 2

/-- Proposition 12: at `n = 1`, `Le^{(1)}` satisfies the log-convexity inequality
`Le^{(1)}_0 Le^{(1)}_2 ≥ (Le^{(1)}_1)²`, and `Le^{(r)}` for `r ≥ 2` the log-concavity
inequality `(Le^{(r)}_1)² ≥ Le^{(r)}_0 Le^{(r)}_2`.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 12
(`integers-2026-A48-prop-12`). -/
public theorem_wanted hyperLeonardo_logConvex_logConcave_one :
    hyperLeonardo 1 1 ^ 2 ≤ hyperLeonardo 1 0 * hyperLeonardo 1 2 ∧
      ∀ r, 2 ≤ r → hyperLeonardo r 0 * hyperLeonardo r 2 ≤ hyperLeonardo r 1 ^ 2

/-- Proposition 13: `Le^{(1)}` is log-concave from `n = 2` on:
`Le^{(1)}_{n-1} Le^{(1)}_{n+1} ≤ (Le^{(1)}_n)²` for `n ≥ 2`.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 13
(`integers-2026-A48-prop-13`). -/
public theorem_wanted hyperLeonardo_one_logConcave (n : ℕ) (hn : 2 ≤ n) :
    hyperLeonardo 1 (n - 1) * hyperLeonardo 1 (n + 1) ≤ hyperLeonardo 1 n ^ 2

/-- Proposition 4: for `r ≥ 1` and `n ≥ 1`,
`Le^{(r)}_{n-1} Le^{(r)}_{n+1} - (Le^{(r)}_n)² = Le^{(r)}_n Le^{(r-1)}_{n+1} - Le^{(r-1)}_n Le^{(r)}_{n+1}`
(written with `r + 1` and `n + 1`; `n = 0` would use the undefined term `Le^{(r)}_{-1}`).

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 4
(`integers-2026-A48-prop-4`). -/
public theorem_wanted hyperLeonardo_mul_sub_sq (r n : ℕ) :
    hyperLeonardo (r + 1) n * hyperLeonardo (r + 1) (n + 2) - hyperLeonardo (r + 1) (n + 1) ^ 2 =
      hyperLeonardo (r + 1) (n + 1) * hyperLeonardo r (n + 2) -
        hyperLeonardo r (n + 1) * hyperLeonardo (r + 1) (n + 2)

/-- Proposition 14, for `r ≥ 1`: `Le^{(r)}` is log-concave from `n = 2` on,
`Le^{(r)}_{n-1} Le^{(r)}_{n+1} ≤ (Le^{(r)}_n)²` for `n ≥ 2`. The printed range `r ≥ 0` fails
at `r = 0`, `n = 3` (`Le₂ Le₄ = 27 > 25 = Le₃²`, the log-convexity of Proposition 10); the
paper's proof starts its induction at `r = 1` (Proposition 13).

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 14
(`integers-2026-A48-prop-14`). -/
public theorem_wanted hyperLeonardo_logConcave {r : ℕ} (hr : 1 ≤ r) {n : ℕ} (hn : 2 ≤ n) :
    hyperLeonardo r (n - 1) * hyperLeonardo r (n + 1) ≤ hyperLeonardo r n ^ 2

/-- Theorem 3: `Le^{(r)}` is convex: `Le^{(r)}_{n-1} + Le^{(r)}_{n+1} ≥ 2 Le^{(r)}_n` for
`r ≥ 0` and `n ≥ 1`.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Theorem 3, with the definition
of convexity displayed before it (`integers-2026-A48-thm-3`). -/
public theorem_wanted hyperLeonardo_convex (r n : ℕ) (hn : 1 ≤ n) :
    2 * hyperLeonardo r n ≤ hyperLeonardo r (n - 1) + hyperLeonardo r (n + 1)

end

end MetaMathlibExt
