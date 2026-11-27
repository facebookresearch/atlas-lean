/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Tactic.IntervalCases
public import MathlibExt.NumberTheory.AscFactorialBounds
public import MathlibExt.NumberTheory.ComplementarySequences
public import MathlibExt.NumberTheory.NonSecondPentagonal
public import MathlibExt.NumberTheory.ComplementarySequencesNthNonCenteredPolygonal

/-!
# Algorithms for complementary sequences (wanted statements)

For a sequence `f : ℕ → ℕ` read on the indices `m ≥ 1` (the paper's `f_{¬P}`), the
complementary sequence `f_P` lists the positive integers that are not values `f m`,
`m ≥ 1`. The paper computes its `n`-th term from the counting function
`C_{¬P}(x) = #{m ≥ 1 : f m ≤ x}` or from an easily inverted interleaving function, and
derives closed formulas for the complements of polygonal, second polygonal, centered
polygonal, pyramidal, sum-of-powers and simplex numbers. The theorem
`nth_nonCenteredPolygonal` is proved in
`MathlibExt.NumberTheory.ComplementarySequencesNthNonCenteredPolygonal`.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Complementary sequences in two Lambek–Moser steps.** Let $f : \mathbb{N} \to \mathbb{N}$
satisfy $f(1) \ge 1$ and $f(m + 1) \ge f(m) + m$ for all $m \ge 1$, let $C(x)$ be the number of
$m$ with $1 \le m \le x$ and $f(m) \le x$, and for $n \ge 1$ let $f_P(n)$ be the $n$-th positive
integer that is not a value $f(m)$ with $m \ge 1$. Then $f_P(n) = n + C(n + C(n))$ for every
$n \ge 1$.

Under the hypotheses, $f(m) \ge m$ for all $m \ge 1$, so $C(x)$ is the number of all $m \ge 1$
with $f(m) \le x$, the counting function of the values of $f$.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 1. -/
public theorem_wanted nthNonValue_eq_two_step (f : ℕ → ℕ) (hf1 : 1 ≤ f 1)
    (hgap : ∀ m, 1 ≤ m → f m + m ≤ f (m + 1)) (n : ℕ) (hn : 1 ≤ n) :
    let C : ℕ → ℕ := fun x => ((Finset.Icc 1 x).filter (fun m => f m ≤ x)).card
    nthNonValue f n = n + C (n + C n)

/-- **Interleaving formula when $f(m) - \alpha(m) < m$.** Let
$f : \mathbb{N} \to \mathbb{N}$ satisfy $f(1) \ge 1$ and $f(m + 1) \ge f(m) + m$ for all $m \ge 1$,
and for $n \ge 1$ let $f_P(n)$ be the $n$-th positive integer that is not a value $f(m)$ with
$m \ge 1$. Let $\alpha : \mathbb{N} \to \mathbb{R}$ satisfy $f(m - 1) \le \alpha(m) \le f(m)$ for
all $m \ge 2$, and let $h : \mathbb{N} \to \mathbb{N}$ satisfy $h(n) \ge 1$ and
$\alpha(h(n)) \le n < \alpha(h(n) + 1)$ for all $n \ge 1$.
Suppose moreover that $f(m) - \alpha(m) < m$ for all $m \ge 1$. Then for every $n \ge 1$,
$f_P(n) = n + h(n) + 1$ if $f(h(n) + 1) \le n + h(n)$, and $f_P(n) = n + h(n)$ otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Corollary 1. -/
public theorem_wanted nthNonValue_eq_interleave_of_sub_lt (f : ℕ → ℕ) (hf1 : 1 ≤ f 1)
    (hgap : ∀ m, 1 ≤ m → f m + m ≤ f (m + 1)) (α : ℕ → ℝ)
    (hα : ∀ m, 2 ≤ m → (f (m - 1) : ℝ) ≤ α m ∧ α m ≤ f m) (h : ℕ → ℕ)
    (hh : ∀ n, 1 ≤ n → 1 ≤ h n ∧ α (h n) ≤ n ∧ (n : ℝ) < α (h n + 1))
    (hclose : ∀ m : ℕ, 1 ≤ m → (f m : ℝ) - α m < m) (n : ℕ) (hn : 1 ≤ n) :
    nthNonValue f n = if f (h n + 1) ≤ n + h n then n + h n + 1 else n + h n

/-- **Interleaving formula when $f(m) - \alpha(m) \ge m$.** Let
$f : \mathbb{N} \to \mathbb{N}$ satisfy $f(1) \ge 1$ and $f(m + 1) \ge f(m) + m$ for all $m \ge 1$,
and for $n \ge 1$ let $f_P(n)$ be the $n$-th positive integer that is not a value $f(m)$ with
$m \ge 1$. Let $\alpha : \mathbb{N} \to \mathbb{R}$ satisfy $f(m - 1) \le \alpha(m) \le f(m)$ for
all $m \ge 2$, and let $h : \mathbb{N} \to \mathbb{N}$ satisfy $h(n) \ge 1$ and
$\alpha(h(n)) \le n < \alpha(h(n) + 1)$ for all $n \ge 1$.
Suppose moreover that $f(m) - \alpha(m) \ge m$ for all $m \ge 2$. Then for every $n \ge 1$,
$f_P(n) = n + h(n)$ if $f(h(n)) < n + h(n)$, and $f_P(n) = n + h(n) - 1$ otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Corollary 2. -/
public theorem_wanted nthNonValue_eq_interleave_of_le_sub (f : ℕ → ℕ) (hf1 : 1 ≤ f 1)
    (hgap : ∀ m, 1 ≤ m → f m + m ≤ f (m + 1)) (α : ℕ → ℝ)
    (hα : ∀ m, 2 ≤ m → (f (m - 1) : ℝ) ≤ α m ∧ α m ≤ f m) (h : ℕ → ℕ)
    (hh : ∀ n, 1 ≤ n → 1 ≤ h n ∧ α (h n) ≤ n ∧ (n : ℝ) < α (h n + 1))
    (hfar : ∀ m : ℕ, 2 ≤ m → (m : ℝ) ≤ f m - α m) (n : ℕ) (hn : 1 ≤ n) :
    nthNonValue f n = if f (h n) < n + h n then n + h n else n + h n - 1

/-- **Formula for the non-polygonal numbers.** Let $k \ge 3$, and for $j \ge 1$ let
$T(k, j) = (k - 2) j (j - 1)/2 + j$ be the $k$-gonal numbers. For every integer $n \ge 1$, put
$s = \lfloor \sqrt{2n/(k - 2)} \rfloor$. Then the $n$-th positive integer that is not of the form
$T(k, j)$ with $j \ge 1$ equals $n + s + 1$ if $(k - 2) s (s + 1) < 2n$, and $n + s$ otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 4, Equation (3). -/
public theorem_wanted nthNonValue_polygonal (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    let s := Nat.sqrt (2 * n / (k - 2))
    nthNonValue (fun j => (k - 2) * j * (j - 1) / 2 + j) n =
      if (k - 2) * s * (s + 1) < 2 * n then n + s + 1 else n + s

/-- **Rounding formula for the non-$k$-gonal numbers, $3 \le k \le 10$.** Let $3 \le k \le 10$;
the $k$-gonal numbers are $(k - 2) j (j - 1)/2 + j$ for $j \ge 1$. For every $n \ge 1$, the $n$-th
positive integer that is not a $k$-gonal number equals
$n + \lfloor \sqrt{2n/(k - 2)} + 1/2 \rfloor$.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 4 (last sentence). -/
public theorem_wanted nthNonValue_polygonal_eq_round (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 10)
    (n : ℕ) (hn : 1 ≤ n) :
    nthNonValue (fun j => (k - 2) * j * (j - 1) / 2 + j) n =
      n + ⌊Real.sqrt (2 * n / ((k : ℝ) - 2)) + 1 / 2⌋₊

/-- **Shifted formula for the non-polygonal numbers.** Let $k \ge 3$, let $r$ be a real number
with $-1 \le r \le k - 4$, and for $j \ge 1$ let $T(k, j) = (k - 2) j (j - 1)/2 + j$ be the
$k$-gonal numbers. For every integer $n \ge 1$, put $s = \lfloor \sqrt{(2n + r)/(k - 2)} \rfloor$.
Then the $n$-th positive integer that is not of the form $T(k, j)$ with $j \ge 1$ equals
$n + s + 1$ if $(k - 2) s (s + 1) < 2n$, and $n + s$ otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 5, Equation (4). -/
public theorem_wanted nthNonValue_polygonal_shift (k : ℕ) (hk : 3 ≤ k) (r : ℝ) (hr : -1 ≤ r)
    (hr' : r ≤ (k : ℝ) - 4) (n : ℕ) (hn : 1 ≤ n) :
    let s := ⌊Real.sqrt ((2 * n + r) / ((k : ℝ) - 2))⌋₊
    nthNonValue (fun j => (k - 2) * j * (j - 1) / 2 + j) n =
      if (k - 2) * s * (s + 1) < 2 * n then n + s + 1 else n + s

/-- **Rounding formula for the non-$k$-gonal numbers, every $k \ge 3$.** Let $k \ge 3$; the
$k$-gonal numbers are $(k - 2) j (j - 1)/2 + j$ for $j \ge 1$. For every $n \ge 1$, the $n$-th
positive integer that is not a $k$-gonal number equals
$n + \lfloor \sqrt{(2n - 2 + \lfloor (k + 1)/4 \rfloor)/(k - 2)} + 1/2 \rfloor$.

This corresponds to the shift $r = \lfloor (k + 1)/4 \rfloor - 2$ in the source.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 5 (last sentence). -/
public theorem_wanted nthNonValue_polygonal_eq_round_shift (k : ℕ) (hk : 3 ≤ k) (n : ℕ)
    (hn : 1 ≤ n) :
    nthNonValue (fun j => (k - 2) * j * (j - 1) / 2 + j) n =
      n + ⌊Real.sqrt ((2 * n - 2 + ((k + 1) / 4 : ℕ)) / ((k : ℝ) - 2)) + 1 / 2⌋₊

/-- **Formula for the non-second-polygonal numbers.** Let $k > 5$, and for $j \ge 1$ let
$S(k, j) = ((k - 2) j^2 + (k - 4) j)/2$ be the second $k$-gonal numbers. For every integer
$n \ge 1$, put $s = \lfloor \sqrt{2n/(k - 2)} \rfloor$. Then the $n$-th positive integer that is
not of the form $S(k, j)$ with $j \ge 1$ equals $n + s$ if $(k - 2) s (s + 1) < 2n + 4s$, and
$n + s - 1$ otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 7, Equation (5). -/
public theorem_wanted nthNonValue_secondPolygonal (k : ℕ) (hk : 5 < k) (n : ℕ) (hn : 1 ≤ n) :
    let s := Nat.sqrt (2 * n / (k - 2))
    nthNonValue (fun j => ((k - 2) * j ^ 2 + (k - 4) * j) / 2) n =
      if (k - 2) * s * (s + 1) < 2 * n + 4 * s then n + s else n + s - 1

/-- **Formula for the non-pyramidal numbers.** Let $3 \le k \le 8$, and for $j \ge 1$ let
$P(k, j) = j (j + 1) ((k - 2) j - (k - 5))/6$ be the $k$-gonal pyramidal numbers. For every
integer $n \ge 1$, put $s = \lfloor \sqrt[3]{6n/(k - 2)} \rfloor$. Then the $n$-th positive
integer that is not of the form $P(k, j)$ with $j \ge 1$ equals $n + s + 1$ if
$6n \ge s^3 (k - 2) + 3 s^2 (k - 1) + s (2k - 1) + 6$; otherwise it equals $n + s - 1$ if
$6n \le s (s - 1) (s (k - 2) + k + 1)$, and $n + s$ if not.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 9, Equation (6). -/
public theorem_wanted nthNonValue_pyramidal (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8) (n : ℕ)
    (hn : 1 ≤ n) :
    let s := Nat.nthRoot 3 (6 * n / (k - 2))
    nthNonValue (fun j => j * (j + 1) * ((k - 2) * j + 5 - k) / 6) n =
      if s ^ 3 * (k - 2) + 3 * s ^ 2 * (k - 1) + s * (2 * k - 1) + 6 ≤ 6 * n then n + s + 1
      else if 6 * n ≤ s * (s - 1) * (s * (k - 2) + k + 1) then n + s - 1
      else n + s

/-- **Two-case formula for the non-pyramidal numbers when $k \le 5$.** Let $3 \le k \le 5$, and
for $j \ge 1$ let $P(k, j) = j (j + 1) ((k - 2) j - (k - 5))/6$ be the $k$-gonal pyramidal
numbers. For every integer $n \ge 1$, put $s = \lfloor \sqrt[3]{6n/(k - 2)} \rfloor$. Then the
$n$-th positive integer that is not of the form $P(k, j)$ with $j \ge 1$ equals $n + s - 1$ if
$6n \le s (s - 1) (s (k - 2) + k + 1)$, and $n + s$ otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Corollary 4, Equation (7). -/
public theorem_wanted nthNonValue_pyramidal_two_case (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 5)
    (n : ℕ) (hn : 1 ≤ n) :
    let s := Nat.nthRoot 3 (6 * n / (k - 2))
    nthNonValue (fun j => j * (j + 1) * ((k - 2) * j + 5 - k) / 6) n =
      if 6 * n ≤ s * (s - 1) * (s * (k - 2) + k + 1) then n + s - 1 else n + s

/-- **Integers missed by the sums $1^k + \dots + j^k$.** Let $k > 1$ and $n \ge 1$ be integers,
and let $h = \lfloor ((k+1)n)^{1/(k+1)} \rfloor$. Then the $n$-th smallest positive integer that
is not of the form $\sum_{i=1}^{j} i^k$ with $j \ge 1$ is $n + h - 1$ if
$n \le \sum_{i=1}^{h} (i^k - 1)$, and $n + h$ otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 10 (third equivalent form). -/
public theorem_wanted nthNonValue_sumPow (k : ℕ) (hk : 1 < k) (n : ℕ) (hn : 1 ≤ n) :
    let h := Nat.nthRoot (k + 1) ((k + 1) * n)
    nthNonValue (fun j => ∑ i ∈ Finset.Icc 1 j, i ^ k) n =
      if n ≤ ∑ i ∈ Finset.Icc 1 h, (i ^ k - 1) then n + h - 1 else n + h

/-- **Integers not of the form $m + 1^k + \cdots + m^k$.** Let $k > 1$. For $n \ge 1$ let $a(n)$
be the $n$-th positive integer that is not of the form $m + \sum_{i=1}^m i^k$ with $m \ge 1$, and
let $h = \lfloor ((k + 1) n)^{1/(k+1)} \rfloor$. Then $a(n) = n + h - 1$ if
$n \le \sum_{i=1}^h i^k$, and $a(n) = n + h$ otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 11 (third equivalent form). -/
public theorem_wanted nthNonValue_add_sumPow (k : ℕ) (hk : 1 < k) (n : ℕ) (hn : 1 ≤ n) :
    let h := Nat.nthRoot (k + 1) ((k + 1) * n)
    nthNonValue (fun j => j + ∑ i ∈ Finset.Icc 1 j, i ^ k) n =
      if n ≤ ∑ i ∈ Finset.Icc 1 h, i ^ k then n + h - 1 else n + h

/-- **Formula for the non-simplex numbers.** Let $k$ satisfy $1 < k \le 5$, $k = 7$ or $k = 9$.
For every integer $n \ge 1$, put $R = \lfloor (k!\, n)^{1/k} \rfloor$ and let
$t = n + R - \lfloor k/2 \rfloor$, an integer. Then the $n$-th positive integer that is not a
$k$-simplex number $\binom{j + k - 1}{k}$ with $j \ge 1$ equals $t + 2$ if
$\binom{R + \lceil k/2 \rceil + 1}{k} \le t + 1$; otherwise it equals $t$ if
$t < \binom{R + \lceil k/2 \rceil}{k}$, and $t + 1$ if not.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 12, Equation (9). -/
public theorem_wanted nthNonValue_simplex (k : ℕ) (hk : 1 < k ∧ k ≤ 5 ∨ k = 7 ∨ k = 9) (n : ℕ)
    (hn : 1 ≤ n) :
    let R := Nat.nthRoot k (k.factorial * n)
    let t : ℤ := n + R - (k / 2 : ℕ)
    (nthNonValue (fun j => (j + k - 1).choose k) n : ℤ) =
      if ((R + (k + 1) / 2 + 1).choose k : ℤ) ≤ t + 1 then t + 2
      else if t < ((R + (k + 1) / 2).choose k : ℤ) then t
      else t + 1

/-- **Formula for the non-simplex numbers when $k \le 15$.** Let $1 < k \le 15$. For every
integer $n \ge 1$, put $R = \lfloor (k!\, n)^{1/k} \rfloor$ and let
$t = n + R - \lfloor k/2 \rfloor$, an integer. Then the $n$-th positive integer that is not a
$k$-simplex number $\binom{j + k - 1}{k}$ with $j \ge 1$ equals $t + 2$ if
$\binom{R + \lceil k/2 \rceil + 1}{k} \le t + 1$; otherwise it equals $t$ if
$t < \binom{R + \lceil k/2 \rceil}{k}$, and $t + 1$ if not.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Corollary 5. -/
public theorem_wanted nthNonValue_simplex_le_fifteen (k : ℕ) (hk : 1 < k) (hk' : k ≤ 15) (n : ℕ)
    (hn : 1 ≤ n) :
    let R := Nat.nthRoot k (k.factorial * n)
    let t : ℤ := n + R - (k / 2 : ℕ)
    (nthNonValue (fun j => (j + k - 1).choose k) n : ℤ) =
      if ((R + (k + 1) / 2 + 1).choose k : ℤ) ≤ t + 1 then t + 2
      else if t < ((R + (k + 1) / 2).choose k : ℤ) then t
      else t + 1

end

end MetaMathlibExt
