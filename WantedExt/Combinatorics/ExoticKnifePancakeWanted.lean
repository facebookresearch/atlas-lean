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

/-- The number of regions into which a set `K ⊆ ℝ²` of cuts divides the plane: the number of
connected components of `ℝ² \ K` (`0` if there are infinitely many).

Source: David O. H. Cutler, Jonas Karlsson and Neil J. A. Sloane, *Cutting a Pancake with an
Exotic Knife*, Journal of Integer Sequences 29 (2026), Article 26.4.5, Section 1. -/
public noncomputable def planeRegionCount (K : Set (ℝ × ℝ)) : ℕ :=
  Set.ncard {C : Set (ℝ × ℝ) | ∃ x ∈ Kᶜ, C = connectedComponentIn Kᶜ x}

/-- With no cuts the plane is a single region.

Source: David O. H. Cutler, Jonas Karlsson and Neil J. A. Sloane, *Cutting a Pancake with an
Exotic Knife*, Journal of Integer Sequences 29 (2026), Article 26.4.5, Section 1 (`n = 0`). -/
public theorem planeRegionCount_empty : planeRegionCount ∅ = 1 := by
  have h : {C : Set (ℝ × ℝ) | ∃ x ∈ (∅ : Set (ℝ × ℝ))ᶜ, C = connectedComponentIn (∅ : Set (ℝ × ℝ))ᶜ x}
      = {Set.univ} := by
    ext C
    simp [Set.compl_empty, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ]
  rw [planeRegionCount, h, Set.ncard_singleton]

/-- **Theorem 1** (3-armed V's). The maximum number of regions formed in the plane by `n`
long-legged 3-armed V's (a tip with three rays of arbitrary directions) is `(9n² - 5n + 2)/2`.

Source: David O. H. Cutler, Jonas Karlsson and Neil J. A. Sloane, *Cutting a Pancake with an
Exotic Knife*, Journal of Integer Sequences 29 (2026), Article 26.4.5, Theorem 1
(`jis-2026-26.4.5-thm-1`), with the definition in the section *The k-armed V*. -/
public theorem_wanted isGreatest_planeRegionCount_threeArmedV (n : ℕ) :
    IsGreatest {N : ℕ | ∃ (c : Fin n → ℝ × ℝ) (u : Fin n → Fin 3 → ℝ × ℝ),
      (∀ i j, u i j ≠ 0) ∧
        N = planeRegionCount (⋃ i, ⋃ j, (fun s : ℝ => c i + s • u i j) '' Set.Ici 0)}
      ((9 * n ^ 2 - 5 * n + 2) / 2)

/-- **Theorem 1** (3-chains). The maximum number of regions formed in the plane by `n` 3-chains
(a finite segment `[p, q]` with a ray attached at each end, arbitrary directions,
self-intersections allowed) is `(9n² - 5n + 2)/2`.

Source: David O. H. Cutler, Jonas Karlsson and Neil J. A. Sloane, *Cutting a Pancake with an
Exotic Knife*, Journal of Integer Sequences 29 (2026), Article 26.4.5, Theorem 1
(`jis-2026-26.4.5-thm-1`), with the definition in the section *The k-chain*. -/
public theorem_wanted isGreatest_planeRegionCount_threeChain (n : ℕ) :
    IsGreatest {N : ℕ | ∃ (p q u v : Fin n → ℝ × ℝ), (∀ i, u i ≠ 0 ∧ v i ≠ 0) ∧
        N = planeRegionCount (⋃ i, ((fun s : ℝ => p i + s • u i) '' Set.Ici 0 ∪
          segment ℝ (p i) (q i) ∪ (fun s : ℝ => q i + s • v i) '' Set.Ici 0))}
      ((9 * n ^ 2 - 5 * n + 2) / 2)

/-- **Theorem 1** (long-legged A's). The maximum number of regions formed in the plane by `n`
long-legged A's (a tip `c` with two rays `c + s u₁`, `c + s u₂` and a crossbar segment from
`c + a u₁` to `c + b u₂`, `a, b > 0`) is `(9n² - 5n + 2)/2`.

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

/-- **Lemma 2** (constrained T's). A constrained long-legged `T̄` with center `c` and stem
direction `(cos θ, sin θ)` is the line through `c` perpendicular to the stem (the crossbar)
together with the stem ray from `c`. If two `T̄`'s meet in exactly four points, then
`cos(θ₁ - θ₂) < 0`: their stem directions are more than `π/2` apart.

Source: David O. H. Cutler, Jonas Karlsson and Neil J. A. Sloane, *Cutting a Pancake with an
Exotic Knife*, Journal of Integer Sequences 29 (2026), Article 26.4.5, Lemma 2
(`jis-2026-26.4.5-lem-2`), with the definition in the subsection *The constrained long-legged T̄*. -/
public theorem_wanted cos_sub_neg_of_tbar_inter_ncard_four (c₁ c₂ : ℝ × ℝ) (θ₁ θ₂ : ℝ) :
    let T : ℝ × ℝ → ℝ → Set (ℝ × ℝ) := fun c θ =>
      Set.range (fun s : ℝ => c + s • (-Real.sin θ, Real.cos θ)) ∪
        (fun s : ℝ => c + s • (Real.cos θ, Real.sin θ)) '' Set.Ici 0
    (T c₁ θ₁ ∩ T c₂ θ₂).ncard = 4 → Real.cos (θ₁ - θ₂) < 0

/-- **Lemma 3** (lollipops). A lollipop with center `c`, radius `r > 0` and stem direction
`(cos θ, sin θ)` is the circle of radius `r` about `c` together with the part of the ray from `c`
in that direction outside the open disc. If two lollipops have three or four stem-circle
intersections in total (stem of each with circle of the other), then `cos(θ₁ - θ₂) < 0`.

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
