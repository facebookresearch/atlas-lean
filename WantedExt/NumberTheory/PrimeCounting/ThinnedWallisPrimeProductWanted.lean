/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-! # Thinned Wallis-type prime products modulo `2^m`

Statement-only requests from Mike Winkler, *Thinned Wallis-Type Prime Products in Residue
Classes Modulo 2^m*, INTEGERS 26 (2026), Article A90. Following the source
(arXiv:2602.13371v4, abstract and Sections 1–4): for an odd prime `p`,
`A(p) = (p - χ₄(p))/(p + χ₄(p))` with `χ₄ = ZMod.χ₄`; for `q = 2^m`, `m ≥ 2`, and a set
`S` of reduced residues modulo `q`, `P_S(x) = ∏_{p ≤ x, p mod q ∈ S} A(p)` over primes;
`μ(S) = ∑_{a ∈ S} χ₄(a)`, where `χ₄(a)` is `χ₄` of the reduction of `a` modulo `4`. Since
every element of `S` is a unit and `2` is not a unit modulo `2^m`, the product only
involves odd primes.
-/

open Filter Topology

namespace MetaMathlibExt

@[expose] public section

/-- **Factor identity for Wallis-type prime products.** For every odd prime $p$,
$$\frac{p - \chi_4(p)}{p + \chi_4(p)} = \frac{(1 - \chi_4(p)/p)^2}{1 - 1/p^2},$$
where $\chi_4$ is the nontrivial Dirichlet character modulo $4$.

Source: Mike Winkler, *Thinned Wallis-Type Prime Products in Residue Classes Modulo 2^m*,
INTEGERS 26 (2026), Article A90, Lemma 1 (`integers-2026-A90-lem-1`). -/
public theorem_wanted wallis_prime_factor_eq
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4)) =
      (1 - (ZMod.χ₄ (p : ZMod 4) : ℝ) / p) ^ 2 / (1 - 1 / (p : ℝ) ^ 2)

/-- **Asymptotic for thinned Wallis-type prime products.** Let $m \ge 2$, let $q = 2^m$, and let
$S$ be a set of units of $\mathbb{Z}/q\mathbb{Z}$. Let $\varphi$ be Euler's totient function and
$\chi_4$ the nontrivial Dirichlet character modulo $4$, put $\mu(S) = \sum_{a \in S} \chi_4(a)$,
where $\chi_4(a)$ means $\chi_4$ of the reduction of $a$ modulo $4$, and for real $x$ let
$$P_S(x) = \prod_{p \le x,\ p \bmod q \in S} \frac{p - \chi_4(p)}{p + \chi_4(p)},$$
the product running over primes $p$. Then there is a real number $K > 0$ such that
$P_S(x) / \left(K (\log x)^{-2\mu(S)/\varphi(q)}\right) \to 1$ as $x \to \infty$.

Source: Mike Winkler, *Thinned Wallis-Type Prime Products in Residue Classes Modulo 2^m*,
INTEGERS 26 (2026), Article A90, Theorem 1 (`integers-2026-A90-thm-1`). -/
public theorem_wanted thinned_wallis_prime_product_asymptotic
    (m : ℕ) (hm : 2 ≤ m) (S : Finset (ZMod (2 ^ m))) (hS : ∀ a ∈ S, IsUnit a) :
    ∃ K : ℝ, 0 < K ∧
      Tendsto (fun x : ℝ =>
          (∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
              (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) ∈ S),
            ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4))) /
            (K * Real.log x ^
              (-2 * ((∑ a ∈ S, ZMod.χ₄ ((a.val : ℕ) : ZMod 4) : ℤ) : ℝ) /
                (Nat.totient (2 ^ m) : ℝ))))
        atTop (𝓝 1)

/-- **Convergence of thinned Wallis-type prime products.** Let $m \ge 2$, let $q = 2^m$, and let
$S$ be a set of units of $\mathbb{Z}/q\mathbb{Z}$. Let $\chi_4$ be the nontrivial Dirichlet
character modulo $4$, put $\mu(S) = \sum_{a \in S} \chi_4(a)$, where $\chi_4(a)$ means $\chi_4$ of
the reduction of $a$ modulo $4$, and for real $x$ let
$$P_S(x) = \prod_{p \le x,\ p \bmod q \in S} \frac{p - \chi_4(p)}{p + \chi_4(p)},$$
the product running over primes $p$. Then $P_S(x)$ converges as $x \to \infty$ to a positive real
limit if and only if $\mu(S) = 0$.

Source: Mike Winkler, *Thinned Wallis-Type Prime Products in Residue Classes Modulo 2^m*,
INTEGERS 26 (2026), Article A90, Corollary 1 (`integers-2026-A90-cor-1`). -/
public theorem_wanted thinned_wallis_prime_product_tendsto_pos_iff
    (m : ℕ) (hm : 2 ≤ m) (S : Finset (ZMod (2 ^ m))) (hS : ∀ a ∈ S, IsUnit a) :
    (∃ L : ℝ, 0 < L ∧
        Tendsto (fun x : ℝ =>
            ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
                (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) ∈ S),
              ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4)))
          atTop (𝓝 L)) ↔
      ∑ a ∈ S, ZMod.χ₄ ((a.val : ℕ) : ZMod 4) = 0

/-- **The constant in the thinned Wallis-type prime product asymptotic.** Let $m \ge 2$, let
$q = 2^m$, and let $S$ be a set of units of $\mathbb{Z}/q\mathbb{Z}$. Let $\varphi$ be Euler's
totient function and $\chi_4$ the nontrivial Dirichlet character modulo $4$, put
$\mu(S) = \sum_{a \in S} \chi_4(a)$, where $\chi_4(a)$ means $\chi_4$ of the reduction of $a$
modulo $4$, and for real $x$ let
$$P_S(x) = \prod_{p \le x,\ p \bmod q \in S} \frac{p - \chi_4(p)}{p + \chi_4(p)},$$
the product running over primes $p$. Suppose that $C(a)$ and $D(a)$, for $a \in S$, are real
numbers with
$$C(a) = \lim_{x \to \infty} (\log x)^{1/\varphi(q)} \prod_{p \le x,\ p \equiv a \ (q)} (1 - 1/p),$$
$$D(a) = \lim_{x \to \infty} \prod_{p \le x,\ p \equiv a \ (q)} (1 - 1/p^2),$$
the products running over primes $p$. Put
$K = \prod_{a \in S} \left(C(a)^2 / D(a)\right)^{\chi_4(a)}$. Then
$P_S(x) / \left(K (\log x)^{-2\mu(S)/\varphi(q)}\right) \to 1$ as $x \to \infty$, and if
$\mu(S) = 0$ then $P_S(x) \to K$ as $x \to \infty$.

Source: Mike Winkler, *Thinned Wallis-Type Prime Products in Residue Classes Modulo 2^m*,
INTEGERS 26 (2026), Article A90, Theorem 2 (`integers-2026-A90-thm-2`). -/
public theorem_wanted thinned_wallis_prime_product_constant
    (m : ℕ) (hm : 2 ≤ m) (S : Finset (ZMod (2 ^ m))) (hS : ∀ a ∈ S, IsUnit a)
    (C D : ZMod (2 ^ m) → ℝ)
    (hC : ∀ a ∈ S, Tendsto (fun x : ℝ =>
        Real.log x ^ (1 / (Nat.totient (2 ^ m) : ℝ)) *
          ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
              (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) = a), (1 - 1 / (p : ℝ)))
        atTop (𝓝 (C a)))
    (hD : ∀ a ∈ S, Tendsto (fun x : ℝ =>
        ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
            (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) = a), (1 - 1 / (p : ℝ) ^ 2))
        atTop (𝓝 (D a))) :
    Tendsto (fun x : ℝ =>
        (∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
            (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) ∈ S),
          ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4))) /
          ((∏ a ∈ S, (C a ^ 2 / D a) ^ ZMod.χ₄ ((a.val : ℕ) : ZMod 4)) *
            Real.log x ^
              (-2 * ((∑ a ∈ S, ZMod.χ₄ ((a.val : ℕ) : ZMod 4) : ℤ) : ℝ) /
                (Nat.totient (2 ^ m) : ℝ))))
      atTop (𝓝 1) ∧
    (∑ a ∈ S, ZMod.χ₄ ((a.val : ℕ) : ZMod 4) = 0 →
      Tendsto (fun x : ℝ =>
          ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
              (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) ∈ S),
            ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4)))
        atTop (𝓝 (∏ a ∈ S, (C a ^ 2 / D a) ^ ZMod.χ₄ ((a.val : ℕ) : ZMod 4))))

end

end MetaMathlibExt
