/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Order.Lattice.Nat
public import MathlibExt.Combinatorics.Additive.WeightedDavenportInterval
public import MathlibExt.Combinatorics.Additive.WeightedDavenportInitialInterval
public import MathlibExt.Combinatorics.Additive.WeightedDavenportPrimePow
public import MathlibExt.Combinatorics.Additive.WeightedDavenportZModProdSelf
public import Mathlib.NumberTheory.Padics.PadicVal.Defs

namespace MetaMathlibExt

@[expose] public section

/-- **Xia's theorem on arithmetic progressions of weights.** Let $n \ge 2$ and $a$ be natural
numbers, and let $A = \{(a + i) \bmod n : 0 \le i < \lceil n/2 \rceil\}$ be the set of remainders
modulo $n$ of the $\lceil n/2 \rceil$ consecutive integers
$a, a + 1, \dots, a + \lceil n/2 \rceil - 1$. If $0 \notin A$, then the $A$-weighted Davenport
constant of $\mathbb{Z}/n\mathbb{Z}$ is $D_A(\mathbb{Z}/n\mathbb{Z}) = 2$.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Theorem 1 (`integers-2026-A89-thm-1`). -/
public theorem_wanted weightedDavenport_zmod_arithmeticProgression (n a : ℕ) (hn : 2 ≤ n)
    (hzero : 0 ∉ (Finset.range (n ⌈/⌉ 2)).image (fun i => (a + i) % n)) :
    weightedDavenport ((Finset.range (n ⌈/⌉ 2)).image (fun i => (a + i) % n)) (ZMod n) =
      ((2 : ℕ) : ℕ∞)

/-- **Weighted Davenport constant of $\mathbb{Z}/n\mathbb{Z}$ for the weights prime to $p$.** Let
$n$ be a positive integer, $p$ a prime dividing $n$ and $k = v_p(n)$ the exponent of $p$ in $n$.
For the weight set $A = \{a \in \{1, \dots, n - 1\} : p \nmid a\}$, the $A$-weighted Davenport
constant of $\mathbb{Z}/n\mathbb{Z}$ is $D_A(\mathbb{Z}/n\mathbb{Z}) = k + 1$.

This is Xia's theorem. Without the hypothesis $p \mid n$ the formula fails: for $n = 10$ and
$p = 3$ one has $v_3(10) = 0$ but $D_A(\mathbb{Z}/10\mathbb{Z}) = 2$.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Theorem 2 (`integers-2026-A89-thm-2`). -/
public theorem_wanted weightedDavenport_zmod_not_dvd_prime (n p : ℕ) (hp : p.Prime)
    (hpn : p ∣ n) (hn : 0 < n) :
    weightedDavenport ((Finset.Icc 1 (n - 1)).filter (fun a => ¬ p ∣ a)) (ZMod n) =
      ((padicValNat p n + 1 : ℕ) : ℕ∞)

/-- **Olson's theorem for groups of rank at most two.** For positive integers $h$ and $k$ with
$h \mid k$, the Davenport constant $D(G) = D_{\{1\}}(G)$ of
$G = \mathbb{Z}/h\mathbb{Z} \oplus \mathbb{Z}/k\mathbb{Z}$ is $D(G) = h + k - 1$.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Theorem 3 (`integers-2026-A89-thm-3`). -/
public theorem_wanted weightedDavenport_one_zmod_prod_of_dvd (h k : ℕ) (hh : 1 ≤ h)
    (hdvd : h ∣ k) (hk : 1 ≤ k) :
    weightedDavenport {1} (ZMod h × ZMod k) = ((h + k - 1 : ℕ) : ℕ∞)

/-- **Olson's theorem for abelian $p$-groups.** Let $p$ be a prime, $r \ge 0$ and let
$e_1, \dots, e_r \ge 1$ be natural numbers. The Davenport constant $D(G) = D_{\{1\}}(G)$ of
$G = \mathbb{Z}/p^{e_1}\mathbb{Z} \oplus \dots \oplus \mathbb{Z}/p^{e_r}\mathbb{Z}$ is
$D(G) = 1 + \sum_{i=1}^{r} (p^{e_i} - 1)$. For $r = 0$ the group $G$ is trivial and this reads
$D(G) = 1$.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Theorem 4 (`integers-2026-A89-thm-4`). -/
public theorem_wanted weightedDavenport_one_pi_zmod_prime_pow (p r : ℕ) (hp : p.Prime)
    (e : Fin r → ℕ) (he : ∀ i, 1 ≤ e i) :
    weightedDavenport {1} ((i : Fin r) → ZMod (p ^ e i)) =
      ((1 + ∑ i, (p ^ e i - 1) : ℕ) : ℕ∞)

/-- **Weight sets with prescribed weighted Davenport constant on
$\mathbb{Z}/n\mathbb{Z} \times \mathbb{Z}/kn\mathbb{Z}$, divisible case.** Let $n \ge 2$ and
$k \ge 1$ be natural numbers, let $m \ge 2$ be a divisor of $n$, let
$\alpha = \lceil n/(m-1) \rceil - 1$, and suppose that $\alpha$ divides $n$. Then for every finite
set $A$ of natural numbers with $n/m \in A \subseteq \{1, \dots, \alpha\}$, the $A$-weighted
Davenport constant of $\mathbb{Z}/n\mathbb{Z} \times \mathbb{Z}/kn\mathbb{Z}$ is
$D_A(\mathbb{Z}/n\mathbb{Z} \times \mathbb{Z}/kn\mathbb{Z}) = m + \lceil kn/\alpha \rceil - 1$.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Theorem 6(i) (`integers-2026-A89-thm-6`). -/
public theorem_wanted weightedDavenport_zmod_prod_of_dvd (m n k : ℕ) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (hdvd : m ∣ n) (A : Finset ℕ) (hmem : n / m ∈ A)
    (hsub : A ⊆ Finset.Icc 1 (n ⌈/⌉ (m - 1) - 1)) (hα : n ⌈/⌉ (m - 1) - 1 ∣ n)
    (hk : 1 ≤ k) :
    weightedDavenport A (ZMod n × ZMod (k * n)) =
      ((m + (k * n) ⌈/⌉ (n ⌈/⌉ (m - 1) - 1) - 1 : ℕ) : ℕ∞)

/-- **Weight sets with prescribed weighted Davenport constant on
$\mathbb{Z}/n\mathbb{Z} \times \mathbb{Z}/kn\mathbb{Z}$, non-divisible case.** Let $n \ge 2$ and
$k \ge 1$ be natural numbers, let $m \ge 2$ be a divisor of $n$, let
$\alpha = \lceil n/(m-1) \rceil - 1$, and suppose that $\alpha$ does not divide $n$. Let $r$ be
the remainder of $n$ modulo $\alpha$, so that $1 \le r < \alpha$, and suppose that
$(k - 1)\alpha < kr$. Then for every finite set $A$ of natural numbers with
$n/m \in A \subseteq \{1, \dots, \alpha\}$, the $A$-weighted Davenport constant of
$\mathbb{Z}/n\mathbb{Z} \times \mathbb{Z}/kn\mathbb{Z}$ is
$D_A(\mathbb{Z}/n\mathbb{Z} \times \mathbb{Z}/kn\mathbb{Z}) = m + \lceil kn/\alpha \rceil - 1$.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Theorem 6(ii) (`integers-2026-A89-thm-6`). -/
public theorem_wanted weightedDavenport_zmod_prod_of_not_dvd (m n k : ℕ) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (hdvd : m ∣ n) (A : Finset ℕ) (hmem : n / m ∈ A)
    (hsub : A ⊆ Finset.Icc 1 (n ⌈/⌉ (m - 1) - 1)) (hr : 0 < n % (n ⌈/⌉ (m - 1) - 1))
    (hk : 1 ≤ k)
    (hkr : (k - 1) * (n ⌈/⌉ (m - 1) - 1) < k * (n % (n ⌈/⌉ (m - 1) - 1))) :
    weightedDavenport A (ZMod n × ZMod (k * n)) =
      ((m + (k * n) ⌈/⌉ (n ⌈/⌉ (m - 1) - 1) - 1 : ℕ) : ℕ∞)

/-- **Weighted Davenport constant of $(\mathbb{Z}/p^e\mathbb{Z})^r$.** Let $p$ be a prime and let
$a, e, r$ be natural numbers with $1 \le a \le e$ and $r \ge 1$. Let $A$ be a finite set of
natural numbers with $p^{e-a} \in A \subseteq \{1, \dots, \lceil p^e/(p^a - 1) \rceil - 1\}$.
Then the $A$-weighted Davenport constant of $(\mathbb{Z}/p^e\mathbb{Z})^r$ is
$D_A((\mathbb{Z}/p^e\mathbb{Z})^r) = 1 + r(p^a - 1)$.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Corollary 3 (`integers-2026-A89-cor-3`). -/
public theorem_wanted weightedDavenport_pi_zmod_prime_pow_const (p e a r : ℕ) (hp : p.Prime)
    (ha : 1 ≤ a) (hae : a ≤ e) (hr : 1 ≤ r) (A : Finset ℕ) (hmem : p ^ (e - a) ∈ A)
    (hsub : A ⊆ Finset.Icc 1 (p ^ e ⌈/⌉ (p ^ a - 1) - 1)) :
    weightedDavenport A ((_ : Fin r) → ZMod (p ^ e)) = ((1 + r * (p ^ a - 1) : ℕ) : ℕ∞)

end

end MetaMathlibExt
