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
public import MathlibExt.Combinatorics.Additive.ZeroSumSubsequenceCount
public import MathlibExt.NumberTheory.CarmichaelPrimeOmegaRange

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

end

end MetaMathlibExt
