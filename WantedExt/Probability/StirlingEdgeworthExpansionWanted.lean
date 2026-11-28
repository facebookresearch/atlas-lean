/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Enumerative.Stirling

@[expose] public section

open Filter Finset Set
open scoped BigOperators Topology

namespace MetaMathlibExt

/-! # Stirling–Edgeworth expansion for Ewens sampling occupancy
-/

/--
**Local Edgeworth expansion for the Ewens distribution.** Let $r \ge 0$ be an integer and let
$L \subseteq (0, \infty)$ be compact. For $\theta > 0$ and integers $n \ge 2$ and $1 \le k \le n$,
let $s(n, k)$ be the unsigned Stirling number of the first kind (the number of permutations of
$n$ elements with exactly $k$ cycles), let
$p_n(k; \theta) = \theta^k s(n, k) / (\theta (\theta + 1) \cdots (\theta + n - 1))$ be the
probability that an Ewens permutation with parameter $\theta$ has exactly $k$ cycles, and let
$x_n(k; \theta) = (k - \theta \log n) / \sqrt{\theta \log n}$. Then there are functions
$H_0, H_1, \dots : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ such that for every
$\varepsilon > 0$ there is an $N \ge 2$ with the following property: for all $n \ge N$, all
$\theta \in L$ and all integers $1 \le k \le n$, writing $x = x_n(k; \theta)$,
$$(\log n)^{(r+1)/2} \left| p_n(k; \theta) - \frac{e^{-x^2/2}}{\sqrt{2 \pi \theta \log n}}
\sum_{j=0}^{r} \frac{H_j(x, \theta)}{(\theta \log n)^{j/2}} \right| < \varepsilon.$$

The functions $H_j$ are bound existentially and may depend on both $r$ and $L$; nothing requires
them to be polynomials.

Source: Zakhar Kabluchko, Alexander Marynych, and Henning Sulzbach, "Mode and
Edgeworth Expansion for the Ewens Distribution and the Stirling Numbers,"
Journal of Integer Sequences 19 (2016), Article 16.8.8, Theorem (label
`theo:stirling_edgeworth`), lines 207–226 (Ewens probability mass function at
lines 143–146),
https://cs.uwaterloo.ca/journals/JIS/VOL19/Kabluchko/kabl2.tex
-/
public theorem_wanted stirling_edgeworth_expansion
    (r : ℕ)
    (L : Set ℝ)
    (hL_compact : IsCompact L)
    (hL_positive : L ⊆ Set.Ioi 0) :
    ∃ H : ℕ → ℝ → ℝ → ℝ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∀ θ ∈ L, ∀ k ∈ Finset.Icc 1 n,
        Real.rpow (Real.log n) (((r : ℝ) + 1) / 2) *
            |θ ^ k * (Nat.stirlingFirst n k : ℝ) /
                (∏ i ∈ Finset.range n, (θ + (i : ℝ))) -
              Real.exp (-(((((k : ℝ) - θ * Real.log n) /
                  Real.sqrt (θ * Real.log n)) ^ 2) / 2)) /
                Real.sqrt (2 * Real.pi * θ * Real.log n) *
                ∑ j ∈ Finset.range (r + 1),
                  H j (((k : ℝ) - θ * Real.log n) /
                    Real.sqrt (θ * Real.log n)) θ /
                    Real.rpow (θ * Real.log n) ((j : ℝ) / 2)| < ε

end MetaMathlibExt
