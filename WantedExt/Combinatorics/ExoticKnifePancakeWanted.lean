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

/-- **Number of regions cut out of the plane.** For a set $K \subseteq \mathbb{R}^2$ of cuts, the
number of regions into which $K$ divides the plane is the number of connected components of the
complement $\mathbb{R}^2 \setminus K$, or $0$ if there are infinitely many components.

Source: David O. H. Cutler, Jonas Karlsson and Neil J. A. Sloane, *Cutting a Pancake with an
Exotic Knife*, Journal of Integer Sequences 29 (2026), Article 26.4.5, Section 1. -/
public noncomputable def planeRegionCount (K : Set (ℝ × ℝ)) : ℕ :=
  Set.ncard {C : Set (ℝ × ℝ) | ∃ x ∈ Kᶜ, C = connectedComponentIn Kᶜ x}

/-- **No cuts, one region.** The empty set of cuts divides the plane into exactly one region.

Source: David O. H. Cutler, Jonas Karlsson and Neil J. A. Sloane, *Cutting a Pancake with an
Exotic Knife*, Journal of Integer Sequences 29 (2026), Article 26.4.5, Section 1 (`n = 0`). -/
public theorem planeRegionCount_empty : planeRegionCount ∅ = 1 := by
  have h : {C : Set (ℝ × ℝ) | ∃ x ∈ (∅ : Set (ℝ × ℝ))ᶜ, C = connectedComponentIn (∅ : Set (ℝ × ℝ))ᶜ x}
      = {Set.univ} := by
    ext C
    simp [Set.compl_empty, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ]
  rw [planeRegionCount, h, Set.ncard_singleton]

/-- **Maximum region count for three-armed V's.** A long-legged three-armed V is the union of
three rays $\{c + s u_j : s \ge 0\}$, $j = 1, 2, 3$, from a common tip $c \in \mathbb{R}^2$, with
nonzero direction vectors $u_1, u_2, u_3 \in \mathbb{R}^2$ in arbitrary directions. For every
natural number $n$, the largest number of regions into which the union of $n$ long-legged
three-armed V's can divide the plane is $(9n^2 - 5n + 2)/2$.

Source: David O. H. Cutler, Jonas Karlsson and Neil J. A. Sloane, *Cutting a Pancake with an
Exotic Knife*, Journal of Integer Sequences 29 (2026), Article 26.4.5, Theorem 1
(`jis-2026-26.4.5-thm-1`), with the definition in the section *The k-armed V*. -/
public theorem_wanted isGreatest_planeRegionCount_threeArmedV (n : ℕ) :
    IsGreatest {N : ℕ | ∃ (c : Fin n → ℝ × ℝ) (u : Fin n → Fin 3 → ℝ × ℝ),
      (∀ i j, u i j ≠ 0) ∧
        N = planeRegionCount (⋃ i, ⋃ j, (fun s : ℝ => c i + s • u i j) '' Set.Ici 0)}
      ((9 * n ^ 2 - 5 * n + 2) / 2)

/-- **Maximum region count for 3-chains.** For points $p, q \in \mathbb{R}^2$ and nonzero vectors
$u, v \in \mathbb{R}^2$, the 3-chain is the union of the ray $\{p + s u : s \ge 0\}$, the segment
$[p, q]$ and the ray $\{q + s v : s \ge 0\}$; the directions are arbitrary and the 3-chain may
intersect itself. For every natural number $n$, the largest number of regions into which the
union of $n$ 3-chains can divide the plane is $(9n^2 - 5n + 2)/2$.

Source: David O. H. Cutler, Jonas Karlsson and Neil J. A. Sloane, *Cutting a Pancake with an
Exotic Knife*, Journal of Integer Sequences 29 (2026), Article 26.4.5, Theorem 1
(`jis-2026-26.4.5-thm-1`), with the definition in the section *The k-chain*. -/
public theorem_wanted isGreatest_planeRegionCount_threeChain (n : ℕ) :
    IsGreatest {N : ℕ | ∃ (p q u v : Fin n → ℝ × ℝ), (∀ i, u i ≠ 0 ∧ v i ≠ 0) ∧
        N = planeRegionCount (⋃ i, ((fun s : ℝ => p i + s • u i) '' Set.Ici 0 ∪
          segment ℝ (p i) (q i) ∪ (fun s : ℝ => q i + s • v i) '' Set.Ici 0))}
      ((9 * n ^ 2 - 5 * n + 2) / 2)

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

/-- **Four-point intersections of constrained T's.** For a point $c \in \mathbb{R}^2$ and an angle
$\theta \in \mathbb{R}$, the constrained long-legged T $\bar T(c, \theta)$ is the union of the
crossbar, the line $\{c + s(-\sin\theta, \cos\theta) : s \in \mathbb{R}\}$, and the stem, the ray
$\{c + s(\cos\theta, \sin\theta) : s \ge 0\}$. For all $c_1, c_2 \in \mathbb{R}^2$ and
$\theta_1, \theta_2 \in \mathbb{R}$, if $\bar T(c_1, \theta_1) \cap \bar T(c_2, \theta_2)$ has
exactly four points, then $\cos(\theta_1 - \theta_2) < 0$, that is, the two stem directions make
an angle greater than $\pi/2$.

Source: David O. H. Cutler, Jonas Karlsson and Neil J. A. Sloane, *Cutting a Pancake with an
Exotic Knife*, Journal of Integer Sequences 29 (2026), Article 26.4.5, Lemma 2
(`jis-2026-26.4.5-lem-2`), with the definition in the subsection *The constrained long-legged T̄*. -/
public theorem_wanted cos_sub_neg_of_tbar_inter_ncard_four (c₁ c₂ : ℝ × ℝ) (θ₁ θ₂ : ℝ) :
    let T : ℝ × ℝ → ℝ → Set (ℝ × ℝ) := fun c θ =>
      Set.range (fun s : ℝ => c + s • (-Real.sin θ, Real.cos θ)) ∪
        (fun s : ℝ => c + s • (Real.cos θ, Real.sin θ)) '' Set.Ici 0
    (T c₁ θ₁ ∩ T c₂ θ₂).ncard = 4 → Real.cos (θ₁ - θ₂) < 0

/-- **Stem–circle intersections of two lollipops.** For a point $c = (a, b) \in \mathbb{R}^2$, a
radius $r > 0$ and an angle $\theta \in \mathbb{R}$, the lollipop with center $c$, radius $r$ and
stem direction $(\cos\theta, \sin\theta)$ consists of the circle
$\{(x, y) \in \mathbb{R}^2 : (x - a)^2 + (y - b)^2 = r^2\}$ and the stem
$\{c + s(\cos\theta, \sin\theta) : s \ge r\}$, the part of the ray from $c$ in that direction
outside the open disc. For all $c_1, c_2 \in \mathbb{R}^2$, $r_1, r_2 > 0$ and
$\theta_1, \theta_2 \in \mathbb{R}$, consider the lollipops with centers $c_i$, radii $r_i$ and
stem directions $(\cos\theta_i, \sin\theta_i)$. If the number of points where the stem of the
first meets the circle of the second plus the number of points where the stem of the second meets
the circle of the first is $3$ or $4$, then $\cos(\theta_1 - \theta_2) < 0$.

Source: David O. H. Cutler, Jonas Karlsson and Neil J. A. Sloane, *Cutting a Pancake with an
Exotic Knife*, Journal of Integer Sequences 29 (2026), Article 26.4.5, Lemma 3
(`jis-2026-26.4.5-lem-3`), with the definition in the subsection *The lollipop or qoppa*. -/
public theorem_wanted cos_sub_neg_of_lollipop_good_pair (c₁ c₂ : ℝ × ℝ) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (θ₁ θ₂ : ℝ) :
    let circ : ℝ × ℝ → ℝ → Set (ℝ × ℝ) := fun c r =>
      {x | (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 = r ^ 2}
    let stem : ℝ × ℝ → ℝ → ℝ → Set (ℝ × ℝ) := fun c r θ =>
      (fun s : ℝ => c + s • (Real.cos θ, Real.sin θ)) '' Set.Ici r
    (stem c₁ r₁ θ₁ ∩ circ c₂ r₂).ncard + (stem c₂ r₂ θ₂ ∩ circ c₁ r₁).ncard ∈
        ({3, 4} : Set ℕ) → Real.cos (θ₁ - θ₂) < 0

end

end MetaMathlibExt
