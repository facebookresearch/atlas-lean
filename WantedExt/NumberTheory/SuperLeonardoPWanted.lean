/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Supergeneralized Leonardo `p`-numbers

Statements from Clemens Schütz and Kristian Kelly, *An Explicit Formula for
Supergeneralized Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025),
Article 25.8.2 (<https://cs.uwaterloo.ca/journals/JIS/VOL28/Schutz/schutz3.tex>).

The supergeneralized Leonardo `p`-numbers `𝓛_{p,k,x}` take the `p + 1` initial values
`x_0, …, x_p` freely and satisfy `𝓛(n) = 𝓛(n-1) + 𝓛(n-p-1) + k` for `n > p`; they are
`superLeonardoP`. With `x` constantly `1` they are the generalized Leonardo `p`-numbers
`MathlibExt.NumberTheory.LeonardoPWanted.leonardoPK`. The Fibonacci `p`-numbers are the
existing `MetaMathlibExt.fibonacciP`.

The paper's auxiliary vector `y` is printed as `(1, …, p)`, which has only `p` of the
`p + 1` entries a supergeneralized Leonardo `p`-sequence needs; the paper's table of
`q_{p+j}` (`q_{2p+1} = p + 1`) and Theorem 5 at `n = p` both force `y_p = p + 1`, so `y`
is read here as `(1, …, p + 1)`, i.e. `y_i = i + 1`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Basic.Real.Basic
public import MathlibExt.NumberTheory.Recurrences.HonsbergerFibonacciP

namespace MetaMathlibExt

@[expose] public section

/-- The supergeneralized Leonardo `p`-numbers `𝓛_{p,k,x}(n)`: `x n` for `n ≤ p`, and
`𝓛(n-1) + 𝓛(n-p-1) + k` for `n > p`. Only the initial values `x 0, …, x p` are used.

Source: Clemens Schütz and Kristian Kelly, *An Explicit Formula for Supergeneralized
Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025), Article 25.8.2,
Definition 1. -/
noncomputable def superLeonardoP (p k : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  if _h : n ≤ p then x n
  else superLeonardoP p k x (n - 1) + superLeonardoP p k x (n - p - 1) + k
termination_by n
decreasing_by all_goals omega

/-- The initial values: `𝓛_{p,k,x}(n) = x_n` for `n ≤ p`.

Source: Schütz and Kelly, Journal of Integer Sequences 28 (2025), Article 25.8.2,
Definition 1. -/
theorem superLeonardoP_of_le (p k : ℕ) (x : ℕ → ℝ) {n : ℕ} (hn : n ≤ p) :
    superLeonardoP p k x n = x n := by
  rw [superLeonardoP]; simp [hn]

/-- The recurrence: `𝓛_{p,k,x}(n) = 𝓛_{p,k,x}(n-1) + 𝓛_{p,k,x}(n-p-1) + k` for `n > p`.

Source: Schütz and Kelly, Journal of Integer Sequences 28 (2025), Article 25.8.2,
Definition 1. -/
theorem superLeonardoP_of_lt (p k : ℕ) (x : ℕ → ℝ) {n : ℕ} (hn : p < n) :
    superLeonardoP p k x n =
      superLeonardoP p k x (n - 1) + superLeonardoP p k x (n - p - 1) + k := by
  rw [superLeonardoP]; simp [show ¬n ≤ p by omega]

/-- **Theorem 3**: `𝓛_{p,k,x}(n) = 𝓛_{p,0,x}(n) + max{0, 𝓛_{p,1,y}(n-(p+1))} · k` with
`y = (1, …, p + 1)`. The paper sets `𝓛 ≤ 0` at negative indices, so the correction term is
`0` for `n ≤ p`; for `n > p` the `max` is redundant since `𝓛_{p,1,y}` is positive.

Source: Clemens Schütz and Kristian Kelly, *An Explicit Formula for Supergeneralized
Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025), Article 25.8.2,
Theorem 3. -/
public theorem_wanted superLeonardoP_eq_add_mul (p k : ℕ) (hp : 1 ≤ p) (x : ℕ → ℝ) (n : ℕ) :
    superLeonardoP p k x n =
      superLeonardoP p 0 x n +
        (if p < n then superLeonardoP p 1 (fun i => (i : ℝ) + 1) (n - (p + 1)) else 0) *
          k

/-- **Theorem 4**: the homogeneous case `k = 0`: `𝓛_{p,0,x}(n) = x_n` for `n ≤ p` and
`F_p(n-p+1) x_p + ∑_{i=0}^{min(p-1, n-p-1)} F_p(n-p-i) x_i` for `n > p`.

Source: Clemens Schütz and Kristian Kelly, *An Explicit Formula for Supergeneralized
Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025), Article 25.8.2,
Theorem 4. -/
public theorem_wanted superLeonardoP_zero_eq (p : ℕ) (hp : 1 ≤ p) (x : ℕ → ℝ) (n : ℕ) :
    superLeonardoP p 0 x n =
      if n ≤ p then x n
      else (fibonacciP p (n - p + 1) : ℝ) * x p +
        ∑ i ∈ Finset.range (min (p - 1) (n - p - 1) + 1),
          (fibonacciP p (n - p - i) : ℝ) * x i

/-- **Theorem 5**: with `y = (1, …, p + 1)`,
`𝓛_{p,1,y}(n) = ∑_{i=0}^{⌊(n+1)/(p+1)⌋} C(n+1-pi, i+1)`.

Source: Clemens Schütz and Kristian Kelly, *An Explicit Formula for Supergeneralized
Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025), Article 25.8.2,
Theorem 5. -/
public theorem_wanted superLeonardoP_one_succ_eq_sum_choose (p : ℕ) (hp : 1 ≤ p) (n : ℕ) :
    superLeonardoP p 1 (fun i => (i : ℝ) + 1) n =
      ∑ i ∈ Finset.range ((n + 1) / (p + 1) + 1), ((n + 1 - p * i).choose (i + 1) : ℝ)

/-- **Lemma 6**: `1 + ∑_{i=0}^{J} C(n-pi, i+1) + ∑_{i=0}^{J-1} C(n-pi-p, i+1) =
∑_{i=0}^{J} C(n-pi+1, i+1)`, with natural-number subtraction (a negative upper index gives
`C(0, i+1) = 0`, matching the paper's binomials). Stated for all `J, n, p ∈ ℕ`, which
includes the value `0` beyond the paper's positive range.

Source: Clemens Schütz and Kristian Kelly, *An Explicit Formula for Supergeneralized
Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025), Article 25.8.2,
Lemma 6. -/
public theorem_wanted one_add_sum_choose_add_sum_choose (J n p : ℕ) :
    1 + (∑ i ∈ Finset.range (J + 1), (n - p * i).choose (i + 1)) +
        ∑ i ∈ Finset.range J, (n - p * i - p).choose (i + 1) =
      ∑ i ∈ Finset.range (J + 1), (n - p * i + 1).choose (i + 1)

/-- **Corollary 7** (with the factor `k` restored): for `n > p`,
`𝓛_{p,k,x}(n) = F_p(n-p+1) x_p + ∑_{i=0}^{min(p-1,n-p-1)} F_p(n-p-i) x_i +
max{0, ∑_{j=0}^{⌊(n-p)/(p+1)⌋} C(n-p-pj, j+1)} · k`. The printed corollary omits the
factor `k` on the last term (and reuses `k` as the summation index); without it the
identity fails, e.g. at `p = 1`, `k = 2`, `n = 2`, `x = (1, 1)`: `𝓛 = 4` but the printed
right side is `3`. The factor is the one in Theorem 3, of which the corollary is stated to
be an immediate combination with Theorems 4 and 5.

Source: Clemens Schütz and Kristian Kelly, *An Explicit Formula for Supergeneralized
Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025), Article 25.8.2,
Corollary 7. -/
public theorem_wanted superLeonardoP_eq_fibonacciP_sum (p k : ℕ) (hp : 1 ≤ p) (x : ℕ → ℝ) (n : ℕ)
    (hn : p < n) :
    superLeonardoP p k x n =
      (fibonacciP p (n - p + 1) : ℝ) * x p +
        (∑ i ∈ Finset.range (min (p - 1) (n - p - 1) + 1),
          (fibonacciP p (n - p - i) : ℝ) * x i) +
        max 0 (∑ j ∈ Finset.range ((n - p) / (p + 1) + 1),
          ((n - p - p * j).choose (j + 1) : ℝ)) * k

/-- **Theorem 8** (Kuhapatanakul, quoted): `F_p(n+1) = ∑_{i=0}^{⌊n/(p+1)⌋} C(n-ip, i)` for
`p ≥ 1` and `n ≥ 0`; the paper's second form `F_p(n) = ∑_{i=0}^{⌊(n-1)/(p+1)⌋} C(n-1-ip, i)` is
the same identity with `n` shifted by one. The paper allows all nonnegative `p`, but at `p = 0`
the sequence is identically zero (`F_0(1) = F_0(0) + F_0(0) = 0`) while the sum at `n = 0` is
`C(0, 0) = 1`, so `p ≥ 1` is assumed.

Source: Clemens Schütz and Kristian Kelly, *An Explicit Formula for Supergeneralized
Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025), Article 25.8.2,
Theorem 8 (Kuhapatanakul). -/
public theorem_wanted fibonacciP_succ_eq_sum_choose (p n : ℕ) (hp : 1 ≤ p) :
    fibonacciP p (n + 1) = ∑ i ∈ Finset.range (n / (p + 1) + 1), (n - i * p).choose i

/-- **Theorem 9** (explicit formula, with the factor `k` restored): for `n > p`,
`𝓛_{p,k,x}(n) = (∑_{i=0}^{⌊(n-p)/(p+1)⌋} C(n-p-ip, i)) x_p +
∑_{i=0}^{min(p-1,n-p-1)} (∑_{j=0}^{⌊(n-p-i-1)/(p+1)⌋} C(n-p-i-1-jp, j)) x_i +
max{0, ∑_{j=0}^{⌊(n-p)/(p+1)⌋} C(n-p-pj, j+1)} · k`. As in Corollary 7, the printed
theorem omits the factor `k` on the last term and is false without it (same
counterexample: `p = 1`, `k = 2`, `n = 2`, `x = (1, 1)` gives `4` versus `3`).

Source: Clemens Schütz and Kristian Kelly, *An Explicit Formula for Supergeneralized
Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025), Article 25.8.2,
Theorem 9. -/
public theorem_wanted superLeonardoP_eq_sum_choose (p k : ℕ) (hp : 1 ≤ p) (x : ℕ → ℝ) (n : ℕ)
    (hn : p < n) :
    superLeonardoP p k x n =
      (∑ i ∈ Finset.range ((n - p) / (p + 1) + 1), ((n - p - i * p).choose i : ℝ)) * x p +
        (∑ i ∈ Finset.range (min (p - 1) (n - p - 1) + 1),
          (∑ j ∈ Finset.range ((n - p - i - 1) / (p + 1) + 1),
            ((n - p - i - 1 - j * p).choose j : ℝ)) * x i) +
        max 0 (∑ j ∈ Finset.range ((n - p) / (p + 1) + 1),
          ((n - p - p * j).choose (j + 1) : ℝ)) * k

end

end MetaMathlibExt
