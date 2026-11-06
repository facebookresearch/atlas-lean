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

/-- **Two representations by coprime generators.** Let $c$ and $d$ be coprime natural numbers.
If natural numbers $x, y, x', y'$ satisfy $cx + dy = cx' + dy'$, then $c$ divides $y - y'$ and
$d$ divides $x - x'$ in the integers.

The paper's standing assumption $1 < c < d$ is not needed and is dropped.

Source: Yuchen Ding and Takao Komatsu, *On a Conjecture of Ramírez Alfonsín and
Skałba, III*, INTEGERS 25 (2025), Article A51, Lemma 1 (`integers-2025-A51-lem-1`). -/
public theorem_wanted twoGenerator_dvd_sub_of_eq {c d : ℕ} (hcd : c.Coprime d)
    {x y x' y' : ℕ} (h : c * x + d * y = c * x' + d * y') :
    (c : ℤ) ∣ (y : ℤ) - y' ∧ (d : ℤ) ∣ (x : ℤ) - x'

/-- **Normal form of a number with exactly $\ell$ representations.** Let $c$ and $d$ be coprime
positive integers, and let $n$ and $\ell$ be natural numbers such that the equation
$n = cx + dy$ has exactly $\ell$ solutions $(x, y)$ in natural numbers. Then there are natural
numbers $x_0 < d$ and $y_0 < c$ with $n = (\ell - 1)cd + cx_0 + dy_0$ in the integers.

The identity is stated over the integers, so $\ell = 0$ is included (then $\ell - 1 = -1$). The
paper's standing assumption $1 < c < d$ is weakened to $0 < c$, $0 < d$.

Source: Yuchen Ding and Takao Komatsu, *On a Conjecture of Ramírez Alfonsín and
Skałba, III*, INTEGERS 25 (2025), Article A51, Lemma 2 (`integers-2025-A51-lem-2`). -/
public theorem_wanted exists_eq_of_ncard_twoGeneratorReps {c d : ℕ} (hc : 0 < c) (hd : 0 < d)
    (hcd : c.Coprime d) (n ℓ : ℕ) (hℓ : {p : ℕ × ℕ | c * p.1 + d * p.2 = n}.ncard = ℓ) :
    ∃ x₀ < d, ∃ y₀ < c, (n : ℤ) = ((ℓ : ℤ) - 1) * c * d + c * x₀ + d * y₀

/-- **Counting primes with more than $\ell$ representations.** Let $c$ and $d$ be coprime
natural numbers with $1 < c < d$, let $\ell$ be a natural number, and put
$g_\ell(c, d) = (\ell + 1)cd - c - d$. Write $\pi_{\ell,c,d}$ for the number of primes
$n \le g_\ell(c, d)$ such that the equation $n = cx + dy$ has more than $\ell$ solutions
$(x, y)$ in natural numbers. Then $\pi_{\ell,c,d}$ equals the number of primes $n$ with
$\ell cd < n \le g_\ell(c, d)$ of the form $n = \ell cd + cx_0 + dy_0$ for some natural numbers
$x_0 \le d$ and $y_0 \le c$.

Source: Yuchen Ding and Takao Komatsu, *On a Conjecture of Ramírez Alfonsín and
Skałba, III*, INTEGERS 25 (2025), Article A51, Lemma 3 (`integers-2025-A51-lem-3`),
with `g_ℓ(c, d)` from equation (1). -/
public theorem_wanted card_primes_ellNumericalSemigroup_eq {c d : ℕ} (hc : 1 < c) (hcd : c < d)
    (hcop : c.Coprime d) (ℓ : ℕ) :
    ((Finset.range ((ℓ + 1) * c * d - c - d + 1)).filter fun n =>
        n.Prime ∧ ℓ < {p : ℕ × ℕ | c * p.1 + d * p.2 = n}.ncard).card =
      ((Finset.Ioc (ℓ * c * d) ((ℓ + 1) * c * d - c - d)).filter fun n =>
        n.Prime ∧ ∃ x₀ ≤ d, ∃ y₀ ≤ c, n = ℓ * c * d + c * x₀ + d * y₀).card

/-- **Weighted count of primes in the $\ell$-numerical semigroup.** For every natural number
$\ell$ and every $\varepsilon > 0$ there is a natural number $C$ such that the following holds
for all coprime natural numbers $c$ and $d$ with $C \le c < d$. For a natural number $k$ put
$g_k(c, d) = (k + 1)cd - c - d$, so that $g_0(c, d) = cd - c - d$, and let $\psi_{\ell,c,d}$ be
the sum of the von Mangoldt function $\Lambda(n)$ over the natural numbers $n$ with
$\ell cd < n \le g_\ell(c, d)$ of the form $n = \ell cd + cx_0 + dy_0$ for some natural numbers
$x_0 \le d$ and $y_0 \le c$. Then
$$
\left|\psi_{\ell,c,d} - \frac{g_0(c, d)}{2}\right| < \varepsilon \, \frac{g_0(c, d)}{2}.
$$
That is, $\psi_{\ell,c,d} \sim g_0(c, d)/2$ as $c \to \infty$, uniformly over coprime $d > c$.

Source: Yuchen Ding and Takao Komatsu, *On a Conjecture of Ramírez Alfonsín and
Skałba, III*, INTEGERS 25 (2025), Article A51, Proposition 1
(`integers-2025-A51-prop-1`), with `g_ℓ(c, d)` from equation (1). -/
public theorem_wanted vonMangoldt_sum_ellNumericalSemigroup_asymptotic (ℓ : ℕ) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C : ℕ, ∀ c d : ℕ, C ≤ c → c < d → c.Coprime d →
      |(∑ n ∈ (Finset.Ioc (ℓ * c * d) ((ℓ + 1) * c * d - c - d)).filter
          (fun n => ∃ x₀ ≤ d, ∃ y₀ ≤ c, n = ℓ * c * d + c * x₀ + d * y₀), Λ n) -
        ((c * d - c - d : ℕ) : ℝ) / 2| < ε * (((c * d - c - d : ℕ) : ℝ) / 2)

/-- **Asymptotic count of primes with more than $\ell$ representations.** For every natural
number $\ell$ and every $\varepsilon > 0$ there is a natural number $C$ such that the following
holds for all coprime natural numbers $c$ and $d$ with $C \le c < d$. Put
$g_\ell(c, d) = (\ell + 1)cd - c - d$, and let $\pi_{\ell,c,d}$ be the number of primes
$n \le g_\ell(c, d)$ such that the equation $n = cx + dy$ has more than $\ell$ solutions
$(x, y)$ in natural numbers. Then, with $\pi$ the prime-counting function,
$$
\left|\pi_{\ell,c,d} - \frac{\pi(g_\ell(c, d))}{2\ell + 2}\right| <
\varepsilon \, \frac{\pi(g_\ell(c, d))}{2\ell + 2}.
$$
That is, $\pi_{\ell,c,d} \sim \pi(g_\ell(c, d))/(2\ell + 2)$ as $c \to \infty$, uniformly over
coprime $d > c$.

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
