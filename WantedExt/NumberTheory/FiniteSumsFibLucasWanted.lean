/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite sums involving Fibonacci and Lucas numbers

Statements from Fatima Zohra Bensaci, Rachid Boumahdi, and
Laala Khaldi, "Finite Sums Involving Fibonacci and Lucas
Numbers", *Journal of Integer Sequences* 27 (2024), Article
24.7.2
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Boumahdi/boumahdi12.tex>).

Notation: `α = (1 + √5)/2` and `β = (1 - √5)/2` are
`fibAlpha`/`fibBeta`; `Fₙ` is `Nat.fib`, `Lₙ` is
MathlibExt's `lucasNumber`, `Bₙ` is Mathlib's `bernoulli`,
`Gₙ` is MathlibExt's `genocchiNumber`, and the Euler
(secant) numbers `Eₙ` (exponential generating function
`2/(eᵗ + e⁻ᵗ)`) are `eulerSecNumber`, wrapping MathlibExt's
`chapter5EulerEven`. Several printed statements are false
as printed; each is stated below in a corrected form verified
by exact symbolic evaluation in `ℚ(√5)`, with the correction
documented at the declaration:

* Corollary 2's factor `β⁻ⁿ` gives the sum `2ᵐ`, not `0`;
  the `x = -β` specialization of Theorem 1 has `(-β)^{m-n}`.
* Corollary 4's falling factorial `(m-n+1)(s)` should be
  `(m-n)(s)` (it comes from differentiating `s` times).
* Corollary 6 needs `m ≥ 1` (at `m = 0` the sum is `2`).
* Theorem 11's inner sum omits the contribution of the
  `2/D` term of `(e^{αD} + e^{βD})/D`; the corrected inner
  coefficient (with the extra `2√5^{n+1} G_{n+1}/(n+1)`
  term) is `genLucasCoeff`. Corollaries 12–14 and Theorem 20
  inherit this correction; Corollary 12 also has
  `β^{m-n}` for `(-β)^{m-n}` as printed.
* Theorems 15 and 18 need the full multinomial coefficient
  `n! / (∏ jᵢ! ∏ ℓᵢ!)`; the paper's displayed definition
  omits the `ℓᵢ!` factors.
* Theorem 20's factors `L_{n-jᵢ+1}/(n-jᵢ+1)` are also wrong;
  the corrected form convolves `genLucasCoeff`.
* Theorem 23 is ill-formed as printed (the summation index
  `n` collides with the free `n` of the left side) and is
  not stated; see the source-audit ledger.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.NumberTheory.Bernoulli
public import MathlibExt.Analysis.Ramanujan.Part1Ch5Entry10bEuleriansymmetry
public import MathlibExt.NumberTheory.GenocchiNumber
public import MathlibExt.NumberTheory.LucasSequence

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FiniteSumsFibLucasWanted

open MetaMathlibExt

/-- **The square root of five.** This is the real number $\sqrt{5}$, the nonnegative real square
root of $5$. -/
noncomputable def sqrt5 : ℝ := Real.sqrt 5

/-- **The golden ratio $\alpha$.** The golden ratio is the real number
$\alpha = (1 + \sqrt{5})/2$. -/
noncomputable def fibAlpha : ℝ := (1 + Real.sqrt 5) / 2

/-- **The conjugate golden ratio $\beta$.** The real number $\beta = (1 - \sqrt{5})/2$, the
conjugate of the golden ratio $(1 + \sqrt{5})/2$. -/
noncomputable def fibBeta : ℝ := (1 - Real.sqrt 5) / 2

/-- **Euler numbers.** For a natural number $n$, the Euler number $E_n \in \mathbb{Q}$ is $0$ when
$n$ is odd, and when $n = 2k$ is even it is the even-index Euler number $E_{2k}$, where
$E_0 = 1$ and $\sum_{i=0}^{k} \binom{2k}{2i} E_{2i} = 0$ for $k \ge 1$. The first values are
$E_0 = 1$, $E_2 = -1$, $E_4 = 5$.

These are the Euler (secant) numbers, with exponential generating function $2/(e^t + e^{-t})$. -/
noncomputable def eulerSecNumber (n : ℕ) : ℚ :=
  if n % 2 = 1 then 0
  else ((MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry10bEuleriansymmetry.chapter5EulerEven (n / 2) : ℤ) : ℚ)

/-- **Genocchi–Lucas coefficients.** For a natural number $n$, the Genocchi–Lucas coefficient is
the real number
$$
c_n = \sum_{k=0}^{n} \sqrt{5}^{\,k} \binom{n}{k} G_k \frac{L_{n-k+1}}{n-k+1} +
2 \sqrt{5}^{\,n+1} \frac{G_{n+1}}{n+1},
$$
where $G_k$ are the Genocchi numbers and $L_k$ the Lucas numbers.

These are the inner coefficients of the corrected Theorem 11 of Bensaci, Boumahdi and Khaldi,
"Finite Sums Involving Fibonacci and Lucas Numbers"; the paper's printed coefficient omits the
last term. -/
noncomputable def genLucasCoeff (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1), (Real.sqrt 5) ^ k *
      (Nat.choose n k : ℝ) * (genocchiNumber k : ℝ) *
      ((lucasNumber (n - k + 1) : ℝ) / (n - k + 1 : ℕ))) +
    2 * (Real.sqrt 5) ^ (n + 1) *
      ((genocchiNumber (n + 1) : ℝ) / (n + 1 : ℕ))

/-- **Bernoulli–Fibonacci expansion of $(x + \beta)^m$.** Let $\beta = (1 - \sqrt{5})/2$, let
$B_k$ be the Bernoulli numbers, normalized so that $B_1 = -1/2$, and let $F_k$ be the Fibonacci
numbers ($F_0 = 0$, $F_1 = 1$). Then for every natural number $m$ and every real number $x$,
$$
(x + \beta)^m = \sum_{n=0}^{m} \sum_{k=0}^{n} \sqrt{5}^{\,k} \binom{n}{k} \binom{m}{n} B_k
\frac{F_{n-k+1}}{n-k+1} x^{m-n}.
$$

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Theorem 1. -/
theorem_wanted add_fibBeta_pow_eq_sum (m : ℕ) (x : ℝ) :
    (x + fibBeta) ^ m =
      ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
        (Real.sqrt 5) ^ k * (Nat.choose n k : ℝ) *
          (Nat.choose m n : ℝ) * (bernoulli k : ℝ) *
          ((Nat.fib (n - k + 1) : ℝ) / (n - k + 1 : ℕ)) *
          x ^ (m - n)

/-- **A vanishing double sum of Bernoulli and Fibonacci numbers.** Let $\beta = (1 - \sqrt{5})/2$,
let $F_n$ be the Fibonacci numbers, and let $B_k$ be the Bernoulli numbers, with
$B_1 = -\tfrac{1}{2}$. For every natural number $m \ge 1$,
$$\sum_{n=0}^{m} \sum_{k=0}^{n} \sqrt{5}^{\,k} \binom{n}{k} \binom{m}{n} B_k
\frac{F_{n-k+1}}{n-k+1} (-\beta)^{m-n} = 0.$$

This is the case $x = -\beta$ of Theorem 1, the expansion of $(x + \beta)^m$. The paper prints
the factor $\beta^{-n}$ in place of $(-\beta)^{m-n}$, which makes the sum equal to $2^m$.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 2. -/
theorem_wanted sum_bernoulli_fib_neg_fibBeta (m : ℕ) (hm : 1 ≤ m) :
    ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
        (Real.sqrt 5) ^ k * (Nat.choose n k : ℝ) *
          (Nat.choose m n : ℝ) * (bernoulli k : ℝ) *
          ((Nat.fib (n - k + 1) : ℝ) / (n - k + 1 : ℕ)) *
          (-fibBeta) ^ (m - n) = 0

/-- **Bernoulli–Fibonacci double sum with weights $(-2)^n$.** Let $B_k$ be the Bernoulli
numbers, with $B_1 = -1/2$, and let $F_k$ be the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$). For every
natural number $m$,
$$\sum_{n=0}^{m} \sum_{k=0}^{n} (-2)^n (\sqrt{5})^k \binom{n}{k} \binom{m}{n} B_k
\frac{F_{n-k+1}}{n-k+1} = (\sqrt{5})^m.$$

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 3. -/
theorem_wanted sum_neg_two_pow_bernoulli_fib (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
        (-2 : ℝ) ^ n * (Real.sqrt 5) ^ k * (Nat.choose n k : ℝ) *
          (Nat.choose m n : ℝ) * (bernoulli k : ℝ) *
          ((Nat.fib (n - k + 1) : ℝ) / (n - k + 1 : ℕ)) =
      (Real.sqrt 5) ^ m

/-- **Derivatives of the Bernoulli–Fibonacci expansion of $(x + \beta)^m$.** Let
$\beta = (1 - \sqrt{5})/2$, let $B_k$ be the Bernoulli numbers with $B_1 = -1/2$, let $F_k$ be the
Fibonacci numbers, and write $a^{\underline{s}} = a(a-1)\cdots(a-s+1)$ for the falling factorial.
Then for all natural numbers $s \le m$ and every real number $x$,
$$
m^{\underline{s}} (x + \beta)^{m-s} = \sum_{n=0}^{m} \sum_{k=0}^{n} \sqrt{5}^{\,k} \binom{n}{k}
\binom{m}{n} B_k \frac{F_{n-k+1}}{n-k+1} (m-n)^{\underline{s}} x^{m-n-s},
$$
where the terms with $m - n < s$ are $0$ because $(m-n)^{\underline{s}} = 0$ there.

This is the paper's Corollary 4, obtained by differentiating Theorem 1 $s$ times; the printed
falling factorial of $m - n + 1$ is off by one, and the identity is written here multiplied
through by $m^{\underline{s}}$.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 4. -/
theorem_wanted descFactorial_mul_add_fibBeta_pow (m s : ℕ)
    (hs : s ≤ m) (x : ℝ) :
    (Nat.descFactorial m s : ℝ) * (x + fibBeta) ^ (m - s) =
      ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
        (Real.sqrt 5) ^ k * (Nat.choose n k : ℝ) *
          (Nat.choose m n : ℝ) * (bernoulli k : ℝ) *
          ((Nat.fib (n - k + 1) : ℝ) / (n - k + 1 : ℕ)) *
          (Nat.descFactorial (m - n) s : ℝ) * x ^ (m - n - s)

/-- **Euler–Lucas expansion of $(x + 1/2)^m$.** Let $E_k$ be the Euler (secant) numbers, which
vanish at odd $k$ and begin $E_0 = 1$, $E_2 = -1$, $E_4 = 5$, and let $L_k$ be the Lucas numbers.
Then for every natural number $m$ and every real number $x$,
$$
\left(x + \frac{1}{2}\right)^m = \frac{1}{2} \sum_{n=0}^{m} \sum_{k=0}^{n}
\left(\frac{\sqrt{5}}{2}\right)^{k} \binom{n}{k} \binom{m}{n} x^{m-n} E_k L_{n-k}.
$$

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Theorem 5. -/
theorem_wanted add_half_pow_eq_sum (m : ℕ) (x : ℝ) :
    (x + 1 / 2) ^ m =
      (1 / 2) * ∑ n ∈ Finset.range (m + 1),
        ∑ k ∈ Finset.range (n + 1),
          ((Real.sqrt 5) / 2) ^ k * (Nat.choose n k : ℝ) *
            (Nat.choose m n : ℝ) * x ^ (m - n) *
            (eulerSecNumber k : ℝ) * (lucasNumber (n - k) : ℝ)

/-- **The alternating Euler–Lucas double sum vanishes.** Let $E_k$ be the Euler (secant)
numbers, with exponential generating function $2/(e^t + e^{-t})$, and let $L_k$ be the Lucas
numbers ($L_0 = 2$, $L_1 = 1$, $L_{k+2} = L_{k+1} + L_k$). For every natural number $m \ge 1$,
$$\sum_{n=0}^{m} \sum_{k=0}^{n} (-1)^n \frac{(\sqrt{5})^k}{2^{k+m-n}} \binom{n}{k} \binom{m}{n}
E_k L_{n-k} = 0.$$

The hypothesis $m \ge 1$ is needed: for $m = 0$ the sum is $2$.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 6. -/
theorem_wanted sum_neg_one_pow_eulerSec_lucas (m : ℕ)
    (hm : 1 ≤ m) :
    ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ n * (Real.sqrt 5) ^ k / 2 ^ (k + m - n) *
          (Nat.choose n k : ℝ) * (Nat.choose m n : ℝ) *
          (eulerSecNumber k : ℝ) * (lucasNumber (n - k) : ℝ) = 0

/-- **A double sum of Euler and Lucas numbers equal to two.** Let $L_n$ be the Lucas numbers and
let $E_k$ be the Euler (secant) numbers, given by $2/(e^t + e^{-t}) = \sum_{k \ge 0} E_k t^k / k!$.
For every natural number $m$,
$$\sum_{n=0}^{m} \sum_{k=0}^{n} \frac{\sqrt{5}^{\,k}}{2^{k+m-n}} \binom{n}{k} \binom{m}{n}
E_k L_{n-k} = 2.$$

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 7. -/
theorem_wanted sum_eulerSec_lucas (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
        (Real.sqrt 5) ^ k / 2 ^ (k + m - n) *
          (Nat.choose n k : ℝ) * (Nat.choose m n : ℝ) *
          (eulerSecNumber k : ℝ) * (lucasNumber (n - k) : ℝ) = 2

/-- **Powers of the golden ratio from Euler and Lucas numbers.** Let $\alpha = (1 + \sqrt{5})/2$,
let $L_n$ be the Lucas numbers, and let $E_k$ be the Euler (secant) numbers, given by
$2/(e^t + e^{-t}) = \sum_{k \ge 0} E_k t^k / k!$. For every natural number $m$,
$$\sum_{n=0}^{m} \sum_{k=0}^{n} \left(\frac{\sqrt{5}}{2}\right)^{k+m-n} \binom{n}{k}
\binom{m}{n} E_k L_{n-k} = 2\alpha^m.$$

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 8. -/
theorem_wanted sum_eulerSec_lucas_eq_two_fibAlpha_pow (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
        ((Real.sqrt 5) / 2) ^ (k + m - n) *
          (Nat.choose n k : ℝ) * (Nat.choose m n : ℝ) *
          (eulerSecNumber k : ℝ) * (lucasNumber (n - k) : ℝ) =
      2 * fibAlpha ^ m

/-- **Powers of the conjugate golden ratio from Euler and Lucas numbers.** Let
$\beta = (1 - \sqrt{5})/2$, let $L_n$ be the Lucas numbers, and let $E_k$ be the Euler (secant)
numbers, given by $2/(e^t + e^{-t}) = \sum_{k \ge 0} E_k t^k / k!$. For every natural number $m$,
$$\sum_{n=0}^{m} \sum_{k=0}^{n} (-1)^{m-n} \left(\frac{\sqrt{5}}{2}\right)^{k+m-n}
\binom{n}{k} \binom{m}{n} E_k L_{n-k} = 2\beta^m.$$

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 9. -/
theorem_wanted sum_eulerSec_lucas_eq_two_fibBeta_pow (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ (m - n) * ((Real.sqrt 5) / 2) ^ (k + m - n) *
          (Nat.choose n k : ℝ) * (Nat.choose m n : ℝ) *
          (eulerSecNumber k : ℝ) * (lucasNumber (n - k) : ℝ) =
      2 * fibBeta ^ m

/-- **A binomial sum of Euler and Lucas numbers.** Let $L_n$ be the Lucas numbers and let $E_k$
be the Euler (secant) numbers, given by $2/(e^t + e^{-t}) = \sum_{k \ge 0} E_k t^k / k!$. For
every natural number $n$,
$$\sum_{k=0}^{n} \binom{n}{k} \left(\frac{\sqrt{5}}{2}\right)^{k} E_k L_{n-k} = \frac{2}{2^n}.$$

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 10. -/
theorem_wanted sum_choose_eulerSec_lucas (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℝ) * ((Real.sqrt 5) / 2) ^ k *
          (eulerSecNumber k : ℝ) * (lucasNumber (n - k) : ℝ) =
      2 / 2 ^ n

/-- **Genocchi–Lucas expansion of $(x + \beta)^m$.** Let $\beta = (1 - \sqrt{5})/2$, and for every
natural number $n$ let
$$
c_n = \sum_{k=0}^{n} \sqrt{5}^{\,k} \binom{n}{k} G_k \frac{L_{n-k+1}}{n-k+1} +
2 \sqrt{5}^{\,n+1} \frac{G_{n+1}}{n+1}
$$
be the Genocchi–Lucas coefficient, where $G_k$ are the Genocchi numbers and $L_k$ the Lucas
numbers. Then for every natural number $m$ and every real number $x$,
$$
(x + \beta)^m = \frac{1}{2\sqrt{5}} \sum_{n=0}^{m} \binom{m}{n} c_n x^{m-n}.
$$

This corrects the paper's Theorem 11, whose inner sum omits the term
$2 \sqrt{5}^{\,n+1} G_{n+1}/(n+1)$; without it the identity already fails at $m = 0$, giving $0$
instead of $1$.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Theorem 11. -/
theorem_wanted add_fibBeta_pow_eq_sum_genLucasCoeff (m : ℕ)
    (x : ℝ) :
    (x + fibBeta) ^ m =
      (1 / (2 * Real.sqrt 5)) * ∑ n ∈ Finset.range (m + 1),
        (Nat.choose m n : ℝ) * genLucasCoeff n * x ^ (m - n)

/-- **A vanishing sum of the corrected Genocchi–Lucas coefficients.** Let
$\beta = (1 - \sqrt{5})/2$, let $G_k$ be the Genocchi numbers and $L_n$ the Lucas numbers, and for
each natural number $n$ let
$$c_n = \sum_{k=0}^{n} \sqrt{5}^{\,k} \binom{n}{k} G_k \frac{L_{n-k+1}}{n-k+1} +
2\sqrt{5}^{\,n+1} \frac{G_{n+1}}{n+1}.$$
For every natural number $m \ge 1$, $\sum_{n=0}^{m} \binom{m}{n} c_n (-\beta)^{m-n} = 0$.

This is the case $x = -\beta$ of the corrected Theorem 11. As printed, with $\beta^{m-n}$ in place
of $(-\beta)^{m-n}$ and without the last term of $c_n$, the sum at $m = 2$ is $-10 + 4\sqrt{5}$.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 12. -/
theorem_wanted sum_genLucasCoeff_neg_fibBeta (m : ℕ)
    (hm : 1 ≤ m) :
    ∑ n ∈ Finset.range (m + 1),
        (Nat.choose m n : ℝ) * genLucasCoeff n *
          (-fibBeta) ^ (m - n) = 0

/-- **A weighted sum of the corrected Genocchi–Lucas coefficients.** Let $G_k$ be the Genocchi
numbers and $L_n$ the Lucas numbers, and for each natural number $n$ let
$$c_n = \sum_{k=0}^{n} \sqrt{5}^{\,k} \binom{n}{k} G_k \frac{L_{n-k+1}}{n-k+1} +
2\sqrt{5}^{\,n+1} \frac{G_{n+1}}{n+1}.$$
For every natural number $m$,
$$\sum_{n=0}^{m} \left(\frac{2}{\sqrt{5}}\right)^{n} \binom{m}{n} c_n =
\frac{2\sqrt{5}}{\sqrt{5}^{\,m}}.$$

Expanding $c_n$ splits the left side into the paper's printed double sum
$\sum_{n,k} 2^n \sqrt{5}^{\,k-n} \binom{n}{k} \binom{m}{n} G_k \frac{L_{n-k+1}}{n-k+1}$ and a
correction term; the printed double sum alone gives the right side only for odd $m$ (at $m = 2$
it is $12\sqrt{5}/5$, not $2\sqrt{5}/5$).

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 13. -/
theorem_wanted sum_genLucasCoeff_weighted (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1),
        (2 / Real.sqrt 5) ^ n * (Nat.choose m n : ℝ) *
          genLucasCoeff n =
      2 * Real.sqrt 5 / (Real.sqrt 5) ^ m

/-- **Genocchi–Lucas sum for powers of the conjugate golden ratio.** Let
$\beta = (1 - \sqrt{5})/2$, let $G_k$ be the Genocchi numbers and let $L_k$ be the Lucas numbers
($L_0 = 2$, $L_1 = 1$, $L_{k+2} = L_{k+1} + L_k$). For every natural number $n$,
$$\sum_{k=0}^{n} (\sqrt{5})^k \binom{n}{k} G_k \frac{L_{n-k+1}}{n-k+1} +
2 (\sqrt{5})^{n+1} \frac{G_{n+1}}{n+1} = 2 \sqrt{5} \, \beta^n.$$

This is the paper's printed identity $\sum_{k} (\sqrt{5})^{k-1} \cdots = 2 \beta^n$ multiplied by
$\sqrt{5}$, with the term $2 (\sqrt{5})^{n+1} G_{n+1}/(n+1)$ restored. The printed form holds only
for even $n \ge 2$; at $n = 1$ it gives $1$ instead of $2 \beta = 1 - \sqrt{5}$.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 14. -/
theorem_wanted sum_genocchi_lucas_add (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (Real.sqrt 5) ^ k *
        (Nat.choose n k : ℝ) * (genocchiNumber k : ℝ) *
        ((lucasNumber (n - k + 1) : ℝ) / (n - k + 1 : ℕ))) +
      2 * (Real.sqrt 5) ^ (n + 1) *
        ((genocchiNumber (n + 1) : ℝ) / (n + 1 : ℕ)) =
    2 * Real.sqrt 5 * fibBeta ^ n

/-- **Multinomial Bernoulli–Fibonacci expansion of $(x + q\beta)^m$.** Let
$\beta = (1 - \sqrt{5})/2$, let $B_k$ be the Bernoulli numbers with $B_1 = -1/2$, and let $F_k$ be
the Fibonacci numbers. For every natural number $q \ge 1$, every natural number $m$ and every real
number $x$, the power $(x + q\beta)^m$ equals the sum, over $0 \le n \le m$ and over all pairs of
tuples of natural numbers $(j_1, \dots, j_q)$ and $(\ell_1, \dots, \ell_q)$ with
$j_1 + \dots + j_q + \ell_1 + \dots + \ell_q = n$, of
$$
\sqrt{5}^{\,\ell_1 + \dots + \ell_q} \frac{n!}{j_1! \cdots j_q! \, \ell_1! \cdots \ell_q!}
\binom{m}{n} B_{\ell_1} \cdots B_{\ell_q} \frac{F_{j_1+1}}{j_1+1} \cdots \frac{F_{j_q+1}}{j_q+1}
x^{m-n}.
$$

The coefficient is the full multinomial coefficient: the paper's displayed definition omits the
factors $\ell_i!$, and with them omitted the identity fails, for example at $q = 2$,
$x = \sqrt{5}$, $m = 2$.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Theorem 15. -/
theorem_wanted add_mul_fibBeta_pow_eq_sum (q m : ℕ)
    (hq : 1 ≤ q) (x : ℝ) :
    (x + q * fibBeta) ^ m =
      ∑ n ∈ Finset.range (m + 1),
        ∑ jℓ ∈ (Finset.univ :
            Finset ((Fin q → Fin (n + 1)) ×
              (Fin q → Fin (n + 1)))).filter
            (fun jℓ => (∑ i, (jℓ.1 i).val) +
              (∑ i, (jℓ.2 i).val) = n),
          (Real.sqrt 5) ^ (∑ i, (jℓ.2 i).val) *
            ((n.factorial : ℝ) /
              ((∏ i, ((jℓ.1 i).val.factorial : ℝ)) *
                ∏ i, ((jℓ.2 i).val.factorial : ℝ))) *
            (Nat.choose m n : ℝ) *
            (∏ i, (bernoulli (jℓ.2 i).val : ℝ)) *
            (∏ i, ((Nat.fib ((jℓ.1 i).val + 1) : ℝ) /
              ((jℓ.1 i).val + 1 : ℕ))) *
            x ^ (m - n)

/-- **A multinomial sum of Bernoulli and Fibonacci numbers equal to one.** Let $F_n$ be the
Fibonacci numbers and let $B_k$ be the Bernoulli numbers, with $B_1 = -\tfrac{1}{2}$. For every
natural number $m$,
$$\sum_{n=0}^{m} \sum_{j_1 + j_2 + \ell_1 + \ell_2 = n} \sqrt{5}^{\,\ell_1 + \ell_2 + m - n}
\frac{n!}{j_1!\, j_2!\, \ell_1!\, \ell_2!} \binom{m}{n} B_{\ell_1} B_{\ell_2}
\frac{F_{j_1+1}}{j_1+1} \cdot \frac{F_{j_2+1}}{j_2+1} = 1,$$
where the inner sum runs over all quadruples $(j_1, j_2, \ell_1, \ell_2)$ of natural numbers with
sum $n$.

This is the case $q = 2$, $x = \sqrt{5}$ of Theorem 15, since $\sqrt{5} + 2\beta = 1$ for
$\beta = (1 - \sqrt{5})/2$. The paper's displayed multinomial coefficient omits the factors
$\ell_1!\, \ell_2!$; with that coefficient the sum at $m = 2$ is $8/3$, not $1$.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 17. -/
theorem_wanted sum_bernoulli_fib_two_eq_one (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1),
        ∑ jℓ ∈ (Finset.univ :
            Finset ((Fin 2 → Fin (n + 1)) ×
              (Fin 2 → Fin (n + 1)))).filter
            (fun jℓ => (∑ i, (jℓ.1 i).val) +
              (∑ i, (jℓ.2 i).val) = n),
          (Real.sqrt 5) ^ ((∑ i, (jℓ.2 i).val) + m - n) *
            ((n.factorial : ℝ) /
              ((∏ i, ((jℓ.1 i).val.factorial : ℝ)) *
                ∏ i, ((jℓ.2 i).val.factorial : ℝ))) *
            (Nat.choose m n : ℝ) *
            (∏ i, (bernoulli (jℓ.2 i).val : ℝ)) *
            (∏ i, ((Nat.fib ((jℓ.1 i).val + 1) : ℝ) /
              ((jℓ.1 i).val + 1 : ℕ))) = 1

/-- **Euler–Lucas multinomial expansion of $(x + q/2)^m$.** Let $E_k$ be the Euler (secant)
numbers, with exponential generating function $2/(e^t + e^{-t})$, and let $L_k$ be the Lucas
numbers ($L_0 = 2$, $L_1 = 1$, $L_{k+2} = L_{k+1} + L_k$). For all natural numbers $q \ge 1$ and
$m$ and every real number $x$,
$$2^q \left(x + \frac{q}{2}\right)^m = \sum_{n=0}^{m} \binom{m}{n} x^{m-n}
\sum_{j_1 + \dots + j_q + \ell_1 + \dots + \ell_q = n} \left(\frac{\sqrt{5}}{2}\right)^{\ell_1 +
\dots + \ell_q} \frac{n!}{j_1! \cdots j_q! \, \ell_1! \cdots \ell_q!} E_{\ell_1} \cdots
E_{\ell_q} L_{j_1} \cdots L_{j_q},$$
where the inner sum runs over all tuples $(j_1, \dots, j_q, \ell_1, \dots, \ell_q)$ of natural
numbers with sum $n$.

The coefficient is the full multinomial coefficient; the paper's displayed definition omits the
factors $\ell_i!$.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Theorem 18. -/
theorem_wanted two_pow_mul_add_half_pow (q m : ℕ)
    (hq : 1 ≤ q) (x : ℝ) :
    (2 : ℝ) ^ q * (x + (q : ℝ) / 2) ^ m =
      ∑ n ∈ Finset.range (m + 1),
        ∑ jℓ ∈ (Finset.univ :
            Finset ((Fin q → Fin (n + 1)) ×
              (Fin q → Fin (n + 1)))).filter
            (fun jℓ => (∑ i, (jℓ.1 i).val) +
              (∑ i, (jℓ.2 i).val) = n),
          ((Real.sqrt 5) / 2) ^ (∑ i, (jℓ.2 i).val) *
            ((n.factorial : ℝ) /
              ((∏ i, ((jℓ.1 i).val.factorial : ℝ)) *
                ∏ i, ((jℓ.2 i).val.factorial : ℝ))) *
            (Nat.choose m n : ℝ) *
            (∏ i, (eulerSecNumber (jℓ.2 i).val : ℝ)) *
            (∏ i, (lucasNumber (jℓ.1 i).val : ℝ)) *
            x ^ (m - n)

/-- **Multinomial Genocchi–Lucas expansion of $(x + q\beta)^m$.** Let
$\beta = (1 - \sqrt{5})/2$, let $G_k$ be the Genocchi numbers and $L_k$ the Lucas numbers, and for
every natural number $n$ let
$$
c_n = \sum_{k=0}^{n} \sqrt{5}^{\,k} \binom{n}{k} G_k \frac{L_{n-k+1}}{n-k+1} +
2 \sqrt{5}^{\,n+1} \frac{G_{n+1}}{n+1}
$$
be the Genocchi–Lucas coefficient. Then for every natural number $q \ge 1$, every natural number
$m$ and every real number $x$,
$$
(2\sqrt{5})^q (x + q\beta)^m = \sum_{n=0}^{m} \binom{m}{n} x^{m-n}
\sum_{j_1 + \dots + j_q = n} \frac{n!}{j_1! \cdots j_q!} c_{j_1} \cdots c_{j_q},
$$
where the inner sum runs over all $q$-tuples $(j_1, \dots, j_q)$ of natural numbers with
$j_1 + \dots + j_q = n$.

This is the $q$-fold convolution form of the corrected Theorem 11, the Genocchi–Lucas expansion
of $(x + \beta)^m$. As printed, with factors $L_{n-j_i+1}/(n-j_i+1)$, the paper's displayed
multinomial coefficient and no correction terms, the identity fails already at $q = 1$.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Theorem 20. -/
theorem_wanted two_sqrt5_pow_mul_add (q m : ℕ) (hq : 1 ≤ q)
    (x : ℝ) :
    (2 * Real.sqrt 5) ^ q * (x + q * fibBeta) ^ m =
      ∑ n ∈ Finset.range (m + 1), (Nat.choose m n : ℝ) *
        x ^ (m - n) *
        ∑ j ∈ (Finset.univ :
            Finset (Fin q → Fin (n + 1))).filter
            (fun j => ∑ i, (j i).val = n),
          ((n.factorial : ℝ) /
              ∏ i, ((j i).val.factorial : ℝ)) *
            ∏ i, genLucasCoeff (j i).val

/-- **Iterated forward differences of a power as an alternating binomial sum.** For a real
number $r$, let $\Delta_r$ be the forward difference operator with step $r$, sending a function
$f : \mathbb{R} \to \mathbb{R}$ to $y \mapsto f(y + r) - f(y)$, and let $\Delta_r^k$ be its
$k$-fold iterate (the identity when $k = 0$). For all real numbers $r$ and $x$ and all natural
numbers $k$ and $n$, applying $\Delta_r^k$ to the function $y \mapsto y^n$ and evaluating at $x$
gives $\sum_{j=0}^{k} (-1)^{k-j} \binom{k}{j} (x + rj)^n$.

The paper states this for nonzero complex $r$ and positive $k$; here $r$ is real and $k = 0$ is
allowed.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Lemma 21. -/
theorem_wanted iterate_forwardDiff_pow_eq_sum (r x : ℝ)
    (k n : ℕ) :
    ((fun f : ℝ → ℝ => fun y => f (y + r) - f y)^[k]
        (fun y => y ^ n)) x =
      ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ (k - j) *
        (Nat.choose k j : ℝ) * (x + r * j) ^ n

/-- **Genocchi numbers via Stirling numbers of the second kind.** For every natural number
$n \ge 1$, the Genocchi number $G_n$ satisfies, in $\mathbb{Q}$,
$$
\frac{G_n}{n} = \sum_{j=0}^{n-1} (-1)^j \frac{j!}{2^j} S(n-1, j),
$$
where $S(n-1, j)$ are the Stirling numbers of the second kind.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Theorem 22. -/
theorem_wanted genocchiNumber_div_eq_sum (n : ℕ) (hn : 1 ≤ n) :
    genocchiNumber n / (n : ℚ) =
      ∑ j ∈ Finset.range n, (-1 : ℚ) ^ j *
        (j.factorial : ℚ) / 2 ^ j *
        (Nat.stirlingSecond (n - 1) j : ℚ)

end MathlibExt.NumberTheory.FiniteSumsFibLucasWanted
