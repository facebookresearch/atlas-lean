/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Farey fractions with equal numerators

Statements from Rogelio Tomás García, "Farey
Fractions with Equal Numerators and the Rank of Unit
Fractions", *INTEGERS* 24 (2024), Article A63
(<https://math.colgate.edu/~integers/vol24.html>).

`fareyNumeratorCount n h` is the paper's `N_n(h)`:
the number of fractions of the Farey sequence `F_n`
with numerator `h`, i.e. denominators `h ≤ b ≤ n`
coprime to `h`. Lemma 1's endpoint conventions and
Theorem 1's formula were pinned by brute force over
small parameters (the count in `(1/k, 1/(k-1)]`
requires the strict lower endpoint as soon as
`n > k*h - 1`).

Not stated (see the source audit table): Theorem 2
and Corollaries 3-8 (their rank and counting
formulas could not be pinned from the flattened
extraction), Corollary 1 (false as extracted without
a floor), and Corollary 2 (expository text defining
the rank, not a statement).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Divisors

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FareyNumeratorWanted

/-- **Number of Farey fractions with a given numerator.** For natural numbers $n$ and $h$, $N_n(h)$
is the number of integers $b$ with $h \le b \le n$ and $\gcd(h, b) = 1$; for $h \ge 1$ this is
the number of fractions with numerator $h$ in the Farey sequence of order $n$. -/
def fareyNumeratorCount (n h : ℕ) : ℕ :=
  ((Finset.Icc h n).filter (fun b => Nat.Coprime h b)).card

/-- **Farey fractions with equal numerators between consecutive unit fractions.** Let $k$, $n$
and $h$ be natural numbers with $k > 1$, $h \ge 1$ and $n \ge kh - 1$, and let $\varphi$ be Euler's
totient function. The number of integers $b$ with $1 \le b \le n$, $\gcd(h, b) = 1$ and
$1/k < h/b \le 1/(k-1)$ is $\varphi(h)$. If moreover $h > 2$, then twice the number of integers
$b$ with $1 \le b \le n$, $\gcd(h, b) = 1$ and $1/k < h/b < 2/(2k-1)$ is $\varphi(h)$.

Equivalently, the Farey sequence of order $n$ has exactly $\varphi(h)$ fractions with numerator
$h$ in the interval $(1/k, 1/(k-1)]$, and for $h > 2$ exactly $\varphi(h)/2$ in the interval
$(1/k, 2/(2k-1))$.

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
Lemma 1. -/
theorem_wanted farey_between_count (k n h : ℕ)
    (hk : 1 < k) (hh : 1 ≤ h) (hn : k * h - 1 ≤ n) :
    ((Finset.Icc 1 n).filter (fun b => Nat.Coprime h b ∧
        (1 : ℚ) / k < (h : ℚ) / b ∧
          (h : ℚ) / b ≤ 1 / ((k : ℚ) - 1))).card =
        Nat.totient h ∧
      (2 < h →
        2 * ((Finset.Icc 1 n).filter (fun b =>
            Nat.Coprime h b ∧ (1 : ℚ) / k < (h : ℚ) / b ∧
              (h : ℚ) / b < 2 / (2 * (k : ℚ) - 1))).card =
          Nat.totient h)

/-- **Formula for the number of Farey fractions with a given numerator.** Let $h$ and $n$ be
natural numbers with $0 < h < n$, and let $N_n(h)$ be the number of integers $b$ with
$h \le b \le n$ and $\gcd(h, b) = 1$ (the number of fractions with numerator $h$ in the Farey
sequence of order $n$). Then
$$
N_n(h) = \frac{n \varphi(h)}{h} - \sum_{d \mid h} \mu(d) \frac{n \bmod d}{d} -
\varphi(h) + \delta_{1h},
$$
where $\varphi$ is Euler's totient function, $\mu$ is the Möbius function, the sum runs over the
positive divisors $d$ of $h$, $(n \bmod d)/d$ is the fractional part of $n/d$, and $\delta_{1h}$ is
$1$ if $h = 1$ and $0$ otherwise.

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
Theorem 1. -/
theorem_wanted fareyNumeratorCount_formula (h n : ℕ)
    (hh : 0 < h) (hhn : h < n) :
    (fareyNumeratorCount n h : ℚ) =
      (Nat.totient h : ℚ) * (n : ℚ) / h -
        ∑ d ∈ h.divisors,
          (ArithmeticFunction.moebius d : ℚ) *
            ((n % d : ℚ) / d) -
        (Nat.totient h : ℚ) + (if h = 1 then 1 else 0)

end MathlibExt.NumberTheory.FareyNumeratorWanted
