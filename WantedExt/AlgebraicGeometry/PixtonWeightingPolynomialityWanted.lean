/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PixtonWeightings

@[expose] public section

/-!
# Polynomial regularization of Pixton graph sums

The remaining request is polynomiality for sufficiently large positive
modulus. Its constant term is uniquely determined by the completed
eventual-polynomial uniqueness lemma. No weighting formula at modulus
zero is asserted.

Source: Janda--Pandharipande--Pixton--Zvonkine, Double ramification cycles
on the moduli spaces of curves, Appendix A, polynomiality of weighting
sums. https://arxiv.org/abs/1602.04705
-/

namespace WantedExt.AlgebraicGeometry.PixtonWeightingPolynomiality

open _root_.MathlibExt.AlgebraicGeometry.UniversalCurveStability
open _root_.MathlibExt.AlgebraicGeometry.PixtonWeightings
open scoped BigOperators

/-- **Polynomiality of Pixton's weighting sums.** Janda–Pandharipande–Pixton–Zvonkine,
Appendix A: let $G$ be a connected stable $n$-marked graph of genus $g$, let
$a_1, \dots, a_n \in \mathbb{Z}$ with $\sum_i a_i = 0$, and let $k_e \in \mathbb{N}$ for every edge
$e$. For $r > 0$, let $S(r)$ be the sum, over the mod-$r$ weightings $w$ of $G$ (values in
$\mathbb{Z}/r$ on the half-edges, opposite on the two halves $h_e, h'_e$ of each edge, such that at
every vertex the weights of its half-edges and the $a_i$ of its markings sum to $0$), of
$\prod_e (w(h_e)\, w(h'_e))^{k_e}$ computed with representatives in $\{0, \dots, r - 1\}$, divided
by $r^{b_1(G)}$ and by the number of automorphisms of $G$. Then there are a polynomial
$p \in \mathbb{Q}[x]$ and $N > 0$ with $S(r) = p(r)$ for all $r \ge N$. -/
public theorem_wanted pixton_polynomiality
    (g n : ℕ) (G : StableGraph g n) (a : Fin n → ℤ) (ha : ∑ i, a i = 0)
    (k : Fin G.edges → ℕ) :
    ∃ p : Polynomial ℚ, ∃ N : ℕ, 0 < N ∧
      ∀ (r : ℕ) (hr : 0 < r), N ≤ r →
        normalizedSum G a k r hr = p.eval (r : ℚ)

end WantedExt.AlgebraicGeometry.PixtonWeightingPolynomiality
