/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Connected.Basic
public import MathlibExt.Combinatorics.ConstrainedTIntersections
public import MathlibExt.Combinatorics.ExoticKnifePancake
public import MathlibExt.Combinatorics.ThreeChain

/-!
# Cutting a pancake with an exotic knife

Statements from David O. H. Cutler, Jonas Karlsson and Neil J. A. Sloane, *Cutting a Pancake with
an Exotic Knife*, Journal of Integer Sequences 29 (2026), Article 26.4.5 (arXiv `2511.15864`,
TeX source read).

The plane is `ℝ × ℝ`. The number of regions formed by a closed set `K` of cuts is the number of
connected components of its complement, `planeRegionCount K`. Rays are written
`(fun s : ℝ => p + s • u) '' Set.Ici 0` and finite segments with Mathlib's `segment`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Maximum region count for long-legged A's.** For a tip $c \in \mathbb{R}^2$, nonzero vectors
$u_1, u_2 \in \mathbb{R}^2$ and reals $a, b > 0$, the long-legged A is the union of the rays
$\{c + s u_1 : s \ge 0\}$ and $\{c + s u_2 : s \ge 0\}$ and the crossbar segment
$[c + a u_1, c + b u_2]$. For every natural number $n$, the largest number of regions into which
the union of $n$ long-legged A's can divide the plane is $(9n^2 - 5n + 2)/2$.

Source: David O. H. Cutler, Jonas Karlsson and Neil J. A. Sloane, *Cutting a Pancake with an
Exotic Knife*, Journal of Integer Sequences 29 (2026), Article 26.4.5, Theorem 1
(`jis-2026-26.4.5-thm-1`), with the definition in the section *The long-legged A*. -/
public theorem_wanted isGreatest_planeRegionCount_longLeggedA (n : ℕ) :
    IsGreatest {N : ℕ | ∃ (c u₁ u₂ : Fin n → ℝ × ℝ) (a b : Fin n → ℝ),
      (∀ i, u₁ i ≠ 0 ∧ u₂ i ≠ 0 ∧ 0 < a i ∧ 0 < b i) ∧
        N = planeRegionCount (⋃ i, ((fun s : ℝ => c i + s • u₁ i) '' Set.Ici 0 ∪
          (fun s : ℝ => c i + s • u₂ i) '' Set.Ici 0 ∪
          segment ℝ (c i + a i • u₁ i) (c i + b i • u₂ i)))}
      ((9 * n ^ 2 - 5 * n + 2) / 2)

end

end MetaMathlibExt
