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
public import MathlibExt.Combinatorics.GDifferenceBases
public import MathlibExt.Combinatorics.GDifferenceBasesGroupDiffBasisNumberLeHundredSqrt
public import MathlibExt.Combinatorics.GDifferenceBasesTendstoGroupDiffBasisNumberEvenOdd
public import MathlibExt.Combinatorics.GDifferenceBasesExistsBoundedDiffSetCardDivSqrtTendsto
public import MathlibExt.Combinatorics.GDifferenceBasesTendstoGroupDiffBasisNumberGaloisFieldProd

namespace MetaMathlibExt

open Filter Topology

@[expose] public section

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
