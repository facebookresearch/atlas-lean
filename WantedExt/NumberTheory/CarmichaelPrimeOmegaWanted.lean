/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.CarmichaelNumber

/-!
# Carmichael numbers with a prime number of prime factors

Statements from Thomas Wright, *Carmichael Numbers with a Prime Number of Prime Factors*,
INTEGERS 24 (2024), Article A97 (arXiv:2206.07254). Heath-Brown's conjecture (Conjecture 3 of the
paper: the least prime `≡ c (mod d)`, `gcd(c, d) = 1`, is `≪ d log² d`) enters Theorem 1 as a
hypothesis.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Infinitely many Carmichael numbers with a prime number of prime factors (conditional).**
Suppose there is a real constant $C$ such that for every natural number $d \ge 2$ and every
natural number $c$ coprime to $d$ there is a prime $p \equiv c \pmod{d}$ with
$p \le C d (\log d)^2$ (Heath-Brown's conjecture on the least prime in an arithmetic
progression). Then there are infinitely many Carmichael numbers $n$ whose number of prime
factors counted with multiplicity, $\Omega(n)$, is prime.

Source: Thomas Wright, *Carmichael Numbers with a Prime Number of Prime Factors*, INTEGERS 24
(2024), Article A97, Theorem 1 (`integers-2024-A97-thm-1`); the hypothesis is the paper's
Conjecture 3. -/
public theorem_wanted infinite_carmichael_prime_cardFactors_of_heathBrown
    (hHB : ∃ C : ℝ, ∀ d : ℕ, 2 ≤ d → ∀ c : ℕ, Nat.Coprime c d →
      ∃ p : ℕ, p.Prime ∧ p ≡ c [MOD d] ∧ (p : ℝ) ≤ C * d * Real.log d ^ 2) :
    {n : ℕ | n.IsCarmichael ∧ (ArithmeticFunction.cardFactors n).Prime}.Infinite

/-- **Alford–Granville–Pomerance count of zero-sum subsequences.** Let $G$ be an abelian group
and let $n$ be the least natural number $m$ such that every sequence of $m$ elements of $G$ has a
nonempty subsequence with product $1$ (the Davenport constant of $G$). Let $r$ and $t$ be natural
numbers with $n < t < r$. Then for every sequence $s_1, \dots, s_r$ of elements of $G$, the number
$M$ of sets $S \subseteq \{1, \dots, r\}$ with $t - n \le |S| \le t$ and $\prod_{i \in S} s_i = 1$
satisfies $\binom{r}{t} \le \binom{r}{n} M$.

Source: Thomas Wright, *Carmichael Numbers with a Prime Number of Prime Factors*, INTEGERS 24
(2024), Article A97, Proposition 1 (`integers-2024-A97-prop-1`), quoting Alford, Granville,
and Pomerance, Theorem 2.1. -/
public theorem_wanted choose_le_choose_mul_card_prod_eq_one {G : Type*} [CommGroup G]
    [DecidableEq G] (n : ℕ)
    (hn : IsLeast {m : ℕ | ∀ s : Fin m → G, ∃ S : Finset (Fin m), S.Nonempty ∧
      ∏ i ∈ S, s i = 1} n)
    (r t : ℕ) (hrt : t < r) (htn : n < t) (s : Fin r → G) :
    r.choose t ≤ r.choose n *
      (Finset.univ.filter fun S : Finset (Fin r) =>
        t - n ≤ S.card ∧ S.card ≤ t ∧ ∏ i ∈ S, s i = 1).card

/-- **Linnik's theorem with exponent 5.2 (Xylouris).** There is a real constant $C$ such that for
every natural number $d \ge 1$ and every natural number $c$ coprime to $d$, there is a prime
$p \equiv c \pmod{d}$ with $p \le C d^{5.2}$.

Source: Thomas Wright, *Carmichael Numbers with a Prime Number of Prime Factors*, INTEGERS 24
(2024), Article A97, Theorem 4 (`integers-2024-A97-thm-4`), quoting Xylouris. -/
public theorem_wanted exists_prime_modEq_le_rpow_five_point_two :
    ∃ C : ℝ, ∀ d : ℕ, 1 ≤ d → ∀ c : ℕ, Nat.Coprime c d →
      ∃ p : ℕ, p.Prime ∧ p ≡ c [MOD d] ∧ (p : ℝ) ≤ C * (d : ℝ) ^ (5.2 : ℝ)


/-- **Many primes $q$ with $q - 1$ smooth.** Let $1 < \theta < 2$. There are real constants
$\gamma > 0$ and $Y$ such that for every real $y > Y$, the number of primes $q$ with
$y^\theta / \log y \le q \le y^\theta$ such that every prime divisor of $q - 1$ is at most $y$
is at least $\gamma y^\theta / \log(y^\theta)$.

Source: Thomas Wright, *Carmichael Numbers with a Prime Number of Prime Factors*, INTEGERS 24
(2024), Article A97, Lemma 1 (`integers-2024-A97-lem-1`), quoting Lemma 5.1 of Matomäki and
Lemma 2.1 of Wright. -/
public theorem_wanted exists_card_smooth_shifted_primes_ge (θ : ℝ) (hθ : θ ∈ Set.Ioo 1 2) :
    ∃ γ Y : ℝ, 0 < γ ∧ ∀ y : ℝ, Y < y →
      γ * y ^ θ / Real.log (y ^ θ) ≤
        ({q : ℕ | q.Prime ∧ y ^ θ / Real.log y ≤ q ∧ (q : ℝ) ≤ y ^ θ ∧
          ∀ p : ℕ, p.Prime → p ∣ q - 1 → (p : ℝ) ≤ y}.ncard : ℝ)

/-- **Carmichael numbers with a prime number of prime factors in a range.** Assume Heath-Brown's
conjecture in the following form: there is a real constant $C$ such that for every natural
number $d \ge 2$ and every natural number $c$ coprime to $d$ there is a prime $p \equiv c
\pmod{d}$ with $p \le C d (\log d)^2$. Let $1 < \theta < 2$, and let $\gamma > 0$ be such that
for all sufficiently large real $y$, the number of primes $q$ with
$y^\theta / \log y \le q \le y^\theta$ such that every prime divisor of $q - 1$ is at most $y$
is at least $\gamma y^\theta / \log(y^\theta)$. Then there is a real $Y$ such that for every real
$y > Y$ there is a Carmichael number $n$ with $e^{(\gamma/4) y^\theta \log y} \le n \le
e^{e^{19 \theta y}}$ whose number of prime factors counted with multiplicity, $\Omega(n)$, is
prime.

The paper's proof uses its Lemma 2, which assumes Heath-Brown's conjecture (the paper's
Conjecture 3); here that assumption is an explicit hypothesis, as in Theorem 1.

Source: Thomas Wright, *Carmichael Numbers with a Prime Number of Prime Factors*, INTEGERS 24
(2024), Article A97, Theorem 3 (`integers-2024-A97-thm-3`). -/
public theorem_wanted exists_carmichael_prime_cardFactors_between_of_heathBrown
    (hHB : ∃ C : ℝ, ∀ d : ℕ, 2 ≤ d → ∀ c : ℕ, Nat.Coprime c d →
      ∃ p : ℕ, p.Prime ∧ p ≡ c [MOD d] ∧ (p : ℝ) ≤ C * d * Real.log d ^ 2)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo 1 2) (γ : ℝ) (hγ : 0 < γ)
    (hQ : ∃ Y : ℝ, ∀ y : ℝ, Y < y →
      γ * y ^ θ / Real.log (y ^ θ) ≤
        ({q : ℕ | q.Prime ∧ y ^ θ / Real.log y ≤ q ∧ (q : ℝ) ≤ y ^ θ ∧
          ∀ p : ℕ, p.Prime → p ∣ q - 1 → (p : ℝ) ≤ y}.ncard : ℝ)) :
    ∃ Y : ℝ, ∀ y : ℝ, Y < y → ∃ n : ℕ, n.IsCarmichael ∧
      (ArithmeticFunction.cardFactors n).Prime ∧
      Real.exp (γ / 4 * y ^ θ * Real.log y) ≤ n ∧
      (n : ℝ) ≤ Real.exp (Real.exp (19 * θ * y))

end

end MetaMathlibExt
