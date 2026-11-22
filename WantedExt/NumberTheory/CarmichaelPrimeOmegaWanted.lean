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

/-- Conditional on Heath-Brown's conjecture (least prime in a reduced residue class modulo `d`
is at most `C d log² d`), there are infinitely many Carmichael numbers `n` with `Ω(n)` prime.

Source: Thomas Wright, *Carmichael Numbers with a Prime Number of Prime Factors*, INTEGERS 24
(2024), Article A97, Theorem 1 (`integers-2024-A97-thm-1`); the hypothesis is the paper's
Conjecture 3. -/
public theorem_wanted infinite_carmichael_prime_cardFactors_of_heathBrown
    (hHB : ∃ C : ℝ, ∀ d : ℕ, 2 ≤ d → ∀ c : ℕ, Nat.Coprime c d →
      ∃ p : ℕ, p.Prime ∧ p ≡ c [MOD d] ∧ (p : ℝ) ≤ C * d * Real.log d ^ 2) :
    {n : ℕ | n.IsCarmichael ∧ (ArithmeticFunction.cardFactors n).Prime}.Infinite

/-- Alford, Granville, and Pomerance's subsequence count: if `n` is the least length forcing a
nonempty subsequence with product `1` in the abelian group `G` (the Davenport constant
`n(G)`) and `r > t > n`, then every sequence of `r` elements of `G` has at least
`C(r, t) / C(r, n)` distinct subsequences of length between `t - n` and `t` with product `1`.

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

/-- Xylouris's form of Linnik's theorem: for coprime `c` and `d` there is a prime `p ≡ c
(mod d)` with `p ≪ d^5.2`.

Source: Thomas Wright, *Carmichael Numbers with a Prime Number of Prime Factors*, INTEGERS 24
(2024), Article A97, Theorem 4 (`integers-2024-A97-thm-4`), quoting Xylouris. -/
public theorem_wanted exists_prime_modEq_le_rpow_five_point_two :
    ∃ C : ℝ, ∀ d : ℕ, 1 ≤ d → ∀ c : ℕ, Nat.Coprime c d →
      ∃ p : ℕ, p.Prime ∧ p ≡ c [MOD d] ∧ (p : ℝ) ≤ C * (d : ℝ) ^ (5.2 : ℝ)


/-- Lemma 1 (quoted): for `θ ∈ (1, 2)` and the set
`𝒬 = {q prime : y^θ / log y ≤ q ≤ y^θ, P(q - 1) ≤ y}` (`P(m)` the largest prime factor of `m`,
written as "every prime divisor of `q - 1` is at most `y`"), there are constants `γ = γ_θ > 0`
and `Y = Y_θ` with `|𝒬| ≥ γ y^θ / log(y^θ)` for `y > Y`. The construction of `L'`, `L` and the
exceptional set `𝒟_B(x)` that follows the lemma in the record is not part of the statement.

Source: Thomas Wright, *Carmichael Numbers with a Prime Number of Prime Factors*, INTEGERS 24
(2024), Article A97, Lemma 1 (`integers-2024-A97-lem-1`), quoting Lemma 5.1 of Matomäki and
Lemma 2.1 of Wright. -/
public theorem_wanted exists_card_smooth_shifted_primes_ge (θ : ℝ) (hθ : θ ∈ Set.Ioo 1 2) :
    ∃ γ Y : ℝ, 0 < γ ∧ ∀ y : ℝ, Y < y →
      γ * y ^ θ / Real.log (y ^ θ) ≤
        ({q : ℕ | q.Prime ∧ y ^ θ / Real.log y ≤ q ∧ (q : ℝ) ≤ y ^ θ ∧
          ∀ p : ℕ, p.Prime → p ∣ q - 1 → (p : ℝ) ≤ y}.ncard : ℝ)

/-- Theorem 3: for `θ ∈ (1, 2)` with Lemma 1 constant `γ = γ_θ` (any `γ > 0` for which the
Lemma 1 bound holds for all large `y`) and every sufficiently large `y`, there is a Carmichael
number `n` with `e^{(γ/4) y^θ log y} ≤ n ≤ e^{e^{19θy}}` and `Ω(n)` prime. The paper's proof
uses Lemma 2, which assumes Heath-Brown's conjecture (the paper's Conjecture 3); that
assumption is made explicit as the hypothesis `hHB`, as in Theorem 1.

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
