/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.FieldTheory.Finite.GaloisField
public import MathlibExt.Combinatorics.Additive.BoseChowlaSubgroup
public import MathlibExt.Combinatorics.Additive.FiniteFieldDifferenceBases
public import MathlibExt.Combinatorics.Additive.GDifferenceBasisScaling
public import MathlibExt.Combinatorics.Additive.ZModDifferenceBasis

namespace MetaMathlibExt

open Filter Topology

@[expose] public section

/-- **Upper bound for the $g$-difference basis number.** For natural numbers $g$ and $n$, let
$\eta_g(n)$ be the least size of a finite set $A \subseteq \mathbb{Z}$ such that every
$x \in \{1, \dots, n\}$ is the difference $a - a'$ of at least $g$ ordered pairs
$(a, a') \in A \times A$. Then for all natural numbers $g$ and $n$,

$$\frac{\eta_g(n)}{\sqrt{n}} \le 2\left(1 + \frac{1}{\sqrt{n}}\right) g,$$

where for $n = 0$ both quotients are read with the convention that division by $0$ gives $0$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Corollary 1 (`integers-2025-A77-cor-1`). -/
public theorem_wanted diffBasisNumber_div_sqrt_le (g n : ℕ) :
    (diffBasisNumber g n : ℝ) / Real.sqrt n ≤ 2 * (1 + 1 / Real.sqrt n) * g

/-- **Kravitz's question: the normalized difference basis numbers converge.** For a finite set
$A$ of integers and an integer $x$, write $r_{A-A}(x)$ for the number of ordered pairs
$(a, a') \in A \times A$ with $a - a' = x$. For every integer $g \ge 1$, let $\eta_g(n)$ be the
least size of a finite set $A$ of integers with $r_{A-A}(x) \ge g$ for every integer
$x \in [1, n]$. Then there is a real number $c > 0$ with $\eta_g(n) / \sqrt{n} \to c$ as
$n \to \infty$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Theorem 1 (`integers-2025-A77-thm-1`). -/
public theorem_wanted tendsto_diffBasisNumber_div_sqrt (g : ℕ) (hg : 0 < g) :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun n : ℕ => (diffBasisNumber g n : ℝ) / Real.sqrt n) atTop (𝓝 c)

/-- **Singer product construction of difference bases.** Let $g, q, v \in \mathbb{N}$ and
$m = q^2 + q + 1$. Let $a_0, \dots, a_q$ be integers in $\{1, \dots, m\}$ such that every
$r \in \{1, \dots, m - 1\}$ is congruent modulo $m$ to $a_i - a_j$ for exactly one ordered pair
$(i, j)$ with $i \ne j$ (a Singer difference set modulo $m$). Let $B$ be a finite set of
integers such that every $x \in \{1, \dots, v\}$ equals $b - b'$ for at least $g$ ordered pairs
$(b, b') \in B \times B$. Then, with $F = \{a_i + mb : 0 \le i \le q,\ b \in B\}$, every
$s \in \{1, \dots, mv\}$ equals $f - f'$ for at least $g$ ordered pairs $(f, f') \in F \times F$.

All $q + 1$ Singer elements are used; the paper prints $1 \le i \le q$, for which the statement
fails.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 4 (`integers-2025-A77-lem-4`). -/
public theorem_wanted singer_product_diffBasis (g q v : ℕ) (a : Fin (q + 1) → ℤ)
    (ha : ∀ i, a i ∈ Finset.Icc (1 : ℤ) (q ^ 2 + q + 1))
    (hsinger : ∀ r ∈ Finset.Icc (1 : ℤ) (q ^ 2 + q),
      ∃! ij : Fin (q + 1) × Fin (q + 1),
        ij.1 ≠ ij.2 ∧ a ij.1 - a ij.2 ≡ r [ZMOD (q ^ 2 + q + 1 : ℤ)])
    (B : Finset ℤ) (hB : ∀ x ∈ Finset.Icc (1 : ℤ) v, g ≤ subRepCount B x) :
    ∀ s ∈ Finset.Icc (1 : ℤ) ((q ^ 2 + q + 1) * v),
      g ≤ subRepCount
        ((Finset.univ ×ˢ B).image fun ib : Fin (q + 1) × ℤ => a ib.1 + (q ^ 2 + q + 1) * ib.2) s

/-- **Square-root bound for difference bases of finite fields.** For every finite field $K$ with
$q$ elements, the least size $\eta_1(K)$ of a set $A \subseteq K$ such that every element of $K$
is a difference $a - a'$ of two elements of $A$ satisfies $\eta_1(K) \le 100 \sqrt{q}$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 7 (`integers-2025-A77-lem-7`). -/
public theorem_wanted groupDiffBasisNumber_le_hundred_sqrt {K : Type*} [Field K] [Finite K]
    [DecidableEq K] :
    (groupDiffBasisNumber 1 K : ℝ) ≤ 100 * Real.sqrt (Nat.card K)

open Classical in
/-- **Difference bases of $\mathbb{F}_{p^t} \times \mathbb{F}_{p^t}$.** Let $p$ be an odd prime.
For a finite abelian group $G$, a set $A \subseteq G$ and $x \in G$, write $r_{A-A}(x)$ for the
number of ordered pairs $(a, a') \in A \times A$ with $a - a' = x$, and let $\eta_1(G)$ be the
least size of a set $A \subseteq G$ with $r_{A-A}(x) \ge 1$ for every $x \in G$. Then
$\eta_1(\mathbb{F}_{p^t} \times \mathbb{F}_{p^t}) / p^t \to 1$ as $t \to \infty$, that is,
$\eta_1(\mathbb{F}_{p^t} \times \mathbb{F}_{p^t}) = (1 + o(1))\, p^t$, where $\mathbb{F}_{p^t}$
is the field with $p^t$ elements.

The restriction to odd $p$ is deliberate: for $p = 2$ the claim fails.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 8 (`integers-2025-A77-lem-8`). -/
public theorem_wanted tendsto_groupDiffBasisNumber_galoisField_prod (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) :
    Tendsto (fun t : ℕ =>
        (groupDiffBasisNumber 1 (GaloisField p t × GaloisField p t) : ℝ) / (p : ℝ) ^ t)
      atTop (𝓝 1)

/-- **Even and odd limits for difference bases of $\mathbb{F}_p^n$.** Let $p$ be an odd prime and
$g \ge 1$ an integer. For a finite abelian group $G$, a set $A \subseteq G$ and $x \in G$, write
$r_{A-A}(x)$ for the number of ordered pairs $(a, a') \in A \times A$ with $a - a' = x$, and let
$\eta_g(G)$ be the least size of a set $A \subseteq G$ with $r_{A-A}(x) \ge g$ for every $x \in G$.
Then there are real numbers $L_e > 0$ and $L_o > 0$ such that, as $k \to \infty$,
$\eta_g(\mathbb{F}_p^{2k}) / \sqrt{p^{2k}} \to L_e$ and
$\eta_g(\mathbb{F}_p^{2k+1}) / \sqrt{p^{2k+1}} \to L_o$, where $\mathbb{F}_p^n$ is the additive
group of $n$-tuples over the field $\mathbb{F}_p$ with $p$ elements.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Theorem 2 (`integers-2025-A77-thm-2`). -/
public theorem_wanted tendsto_groupDiffBasisNumber_even_odd (p g : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (hg : 0 < g) :
    (∃ Le : ℝ, 0 < Le ∧ Tendsto (fun k : ℕ =>
        (groupDiffBasisNumber g (Fin (2 * k) → ZMod p) : ℝ) / Real.sqrt ((p : ℝ) ^ (2 * k)))
      atTop (𝓝 Le)) ∧
    (∃ Lo : ℝ, 0 < Lo ∧ Tendsto (fun k : ℕ =>
        (groupDiffBasisNumber g (Fin (2 * k + 1) → ZMod p) : ℝ) /
          Real.sqrt ((p : ℝ) ^ (2 * k + 1)))
      atTop (𝓝 Lo))

/-- **Upper bound for sets with bounded difference multiplicities.** For natural numbers $g$ and
$n$, let $\alpha_g(n)$ be the largest size of a set $A \subseteq \{1, \dots, n\}$ such that every
nonzero integer $x$ is the difference $a - a'$ of at most $g$ ordered pairs
$(a, a') \in A \times A$. If $g \ge 1$, then for every real $\varepsilon > 0$ we have
$\alpha_g(n) \le (1 + \varepsilon)\sqrt{gn}$ for all sufficiently large $n$; that is,
$\alpha_g(n) \le (1 + o(1))\sqrt{gn}$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Proposition 1 (`integers-2025-A77-prop-1`). -/
public theorem_wanted boundedDiffSetNumber_le_one_add_mul_sqrt (g : ℕ) (hg : 0 < g) (ε : ℝ)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (boundedDiffSetNumber g n : ℝ) ≤ (1 + ε) * Real.sqrt (g * n)

/-- **Lower-bound construction for sets with bounded difference multiplicities.** For every
integer $g \ge 1$ there are finite sets $A_n \subseteq \{1, \dots, n\}$ of integers, one for each
$n \in \mathbb{N}$, such that for every $n$ each nonzero integer $x$ equals $a - a'$ for at most
$g$ ordered pairs $(a, a') \in A_n \times A_n$, and $|A_n| / \sqrt{gn} \to 1$ as $n \to \infty$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Proposition 2 (`integers-2025-A77-prop-2`). -/
public theorem_wanted exists_boundedDiffSet_card_div_sqrt_tendsto (g : ℕ) (hg : 0 < g) :
    ∃ A : ℕ → Finset ℤ,
      (∀ n, A n ⊆ Finset.Icc (1 : ℤ) n ∧ ∀ x : ℤ, x ≠ 0 → subRepCount (A n) x ≤ g) ∧
      Tendsto (fun n : ℕ => ((A n).card : ℝ) / Real.sqrt (g * n)) atTop (𝓝 1)

/-- **Asymptotics of the largest sets with bounded difference counts.** For a finite set $A$ of
integers and an integer $x$, write $r_{A-A}(x)$ for the number of ordered pairs
$(a, a') \in A \times A$ with $a - a' = x$. For every integer $g \ge 1$, let $\alpha_g(n)$ be the
largest size of a set $A$ of integers in the interval $[1, n]$ with $r_{A-A}(x) \le g$ for every
nonzero integer $x$. Then $\alpha_g(n) / \sqrt{gn} \to 1$ as $n \to \infty$, that is,
$\alpha_g(n) = (1 + o_g(1)) \sqrt{gn}$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Theorem 3 (`integers-2025-A77-thm-3`). -/
public theorem_wanted tendsto_boundedDiffSetNumber_div_sqrt (g : ℕ) (hg : 0 < g) :
    Tendsto (fun n : ℕ => (boundedDiffSetNumber g n : ℝ) / Real.sqrt (g * n)) atTop (𝓝 1)

end

end MetaMathlibExt
