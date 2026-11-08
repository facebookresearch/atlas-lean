/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Primes in the `ℓ`-numerical semigroup of two generators

Statements from Yuchen Ding and Takao Komatsu, *On a Conjecture of Ramírez
Alfonsín and Skałba, III*, INTEGERS 25 (2025), Article A51 (arXiv `2311.03997`).

For coprime `1 < c < d`, the number of representations of `n` as `c x + d y` with
`x, y ∈ ℕ` is `{p : ℕ × ℕ | c * p.1 + d * p.2 = n}.ncard`. The `ℓ`-Frobenius number
is written through the paper's closed form (1), `g_ℓ(c, d) = (ℓ + 1) c d - c - d`,
and `π_{ℓ,c,d}` is the number of primes `n ≤ g_ℓ(c, d)` with more than `ℓ`
representations.
-/

open ArithmeticFunction

namespace MetaMathlibExt

@[expose] public section

/-- **Lemma 1.** If `c x + d y = c x' + d y'` with `x, y, x', y' ∈ ℕ` and `c, d`
coprime, then `c ∣ y - y'` and `d ∣ x - x'`.

The paper's standing assumption `1 < c < d` is not needed and is dropped.

Source: Yuchen Ding and Takao Komatsu, *On a Conjecture of Ramírez Alfonsín and
Skałba, III*, INTEGERS 25 (2025), Article A51, Lemma 1 (`integers-2025-A51-lem-1`). -/
public theorem_wanted twoGenerator_dvd_sub_of_eq {c d : ℕ} (hcd : c.Coprime d)
    {x y x' y' : ℕ} (h : c * x + d * y = c * x' + d * y') :
    (c : ℤ) ∣ (y : ℤ) - y' ∧ (d : ℤ) ∣ (x : ℤ) - x'

/-- **Lemma 2.** If `n = c x + d y` has exactly `ℓ` solutions `x, y ∈ ℕ`, then
`n = (ℓ - 1) c d + c x₀ + d y₀` for some `0 ≤ x₀ ≤ d - 1` and `0 ≤ y₀ ≤ c - 1`.

The identity is stated over `ℤ`, so `ℓ = 0` is included (then `ℓ - 1 = -1`). The
paper's standing assumption `1 < c < d` is weakened to `0 < c`, `0 < d`.

Source: Yuchen Ding and Takao Komatsu, *On a Conjecture of Ramírez Alfonsín and
Skałba, III*, INTEGERS 25 (2025), Article A51, Lemma 2 (`integers-2025-A51-lem-2`). -/
public theorem_wanted exists_eq_of_ncard_twoGeneratorReps {c d : ℕ} (hc : 0 < c) (hd : 0 < d)
    (hcd : c.Coprime d) (n ℓ : ℕ) (hℓ : {p : ℕ × ℕ | c * p.1 + d * p.2 = n}.ncard = ℓ) :
    ∃ x₀ < d, ∃ y₀ < c, (n : ℤ) = ((ℓ : ℤ) - 1) * c * d + c * x₀ + d * y₀

/-- **Lemma 3.** `π_{ℓ,c,d}`, the number of primes `n ≤ g_ℓ(c, d)` with more than
`ℓ` representations `n = c x + d y`, equals the number of primes `n` with
`ℓ c d < n ≤ g_ℓ(c, d)` of the form `n = ℓ c d + c x₀ + d y₀` with `0 ≤ x₀ ≤ d` and
`0 ≤ y₀ ≤ c`.

Source: Yuchen Ding and Takao Komatsu, *On a Conjecture of Ramírez Alfonsín and
Skałba, III*, INTEGERS 25 (2025), Article A51, Lemma 3 (`integers-2025-A51-lem-3`),
with `g_ℓ(c, d)` from equation (1). -/
public theorem_wanted card_primes_ellNumericalSemigroup_eq {c d : ℕ} (hc : 1 < c) (hcd : c < d)
    (hcop : c.Coprime d) (ℓ : ℕ) :
    ((Finset.range ((ℓ + 1) * c * d - c - d + 1)).filter fun n =>
        n.Prime ∧ ℓ < {p : ℕ × ℕ | c * p.1 + d * p.2 = n}.ncard).card =
      ((Finset.Ioc (ℓ * c * d) ((ℓ + 1) * c * d - c - d)).filter fun n =>
        n.Prime ∧ ∃ x₀ ≤ d, ∃ y₀ ≤ c, n = ℓ * c * d + c * x₀ + d * y₀).card

/-- **Proposition 1.** For each `ℓ`, the weighted count
`ψ_{ℓ,c,d} = ∑ Λ(n)` over `ℓ c d < n ≤ g_ℓ(c, d)` of the form
`n = ℓ c d + c x₀ + d y₀` (`0 ≤ x₀ ≤ d`, `0 ≤ y₀ ≤ c`) satisfies
`ψ_{ℓ,c,d} ∼ g₀(c, d) / 2` as `c → ∞`, uniformly over coprime `d > c`.

The asymptotic is stated with explicit `ε` and a threshold `C` for `c`.

Source: Yuchen Ding and Takao Komatsu, *On a Conjecture of Ramírez Alfonsín and
Skałba, III*, INTEGERS 25 (2025), Article A51, Proposition 1
(`integers-2025-A51-prop-1`), with `g_ℓ(c, d)` from equation (1). -/
public theorem_wanted vonMangoldt_sum_ellNumericalSemigroup_asymptotic (ℓ : ℕ) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C : ℕ, ∀ c d : ℕ, C ≤ c → c < d → c.Coprime d →
      |(∑ n ∈ (Finset.Ioc (ℓ * c * d) ((ℓ + 1) * c * d - c - d)).filter
          (fun n => ∃ x₀ ≤ d, ∃ y₀ ≤ c, n = ℓ * c * d + c * x₀ + d * y₀), Λ n) -
        ((c * d - c - d : ℕ) : ℝ) / 2| < ε * (((c * d - c - d : ℕ) : ℝ) / 2)

/-- **Theorem 1.** For each `ℓ`, `π_{ℓ,c,d} ∼ π(g_ℓ(c, d)) / (2ℓ + 2)` as `c → ∞`,
uniformly over coprime `d > c`, where `π_{ℓ,c,d}` is the number of primes
`n ≤ g_ℓ(c, d)` with more than `ℓ` representations `n = c x + d y`.

The asymptotic is stated with explicit `ε` and a threshold `C` for `c`.

Source: Yuchen Ding and Takao Komatsu, *On a Conjecture of Ramírez Alfonsín and
Skałba, III*, INTEGERS 25 (2025), Article A51, Theorem 1 (`integers-2025-A51-thm-1`),
with `g_ℓ(c, d)` from equation (1). -/
public theorem_wanted card_primes_ellNumericalSemigroup_asymptotic (ℓ : ℕ) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C : ℕ, ∀ c d : ℕ, C ≤ c → c < d → c.Coprime d →
      |(((Finset.range ((ℓ + 1) * c * d - c - d + 1)).filter fun n =>
            n.Prime ∧ ℓ < {p : ℕ × ℕ | c * p.1 + d * p.2 = n}.ncard).card : ℝ) -
          (Nat.primeCounting ((ℓ + 1) * c * d - c - d) : ℝ) / (2 * ℓ + 2)| <
        ε * ((Nat.primeCounting ((ℓ + 1) * c * d - c - d) : ℝ) / (2 * ℓ + 2))

end

end MetaMathlibExt
