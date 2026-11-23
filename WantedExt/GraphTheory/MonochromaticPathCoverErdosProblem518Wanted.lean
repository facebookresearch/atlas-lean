/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Covering by monochromatic paths of one colour (Erdős Problem 518)

Erdős Problem 518 (Erdős and Gyárfás): in every 2-colouring of the edges of `K_n`, are there `√n`
monochromatic paths, all of the same colour, covering all vertices?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MathlibExt.GraphTheory.MonochromaticPathCoverErdosProblem518Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #518, https://www.erdosproblems.com/518 (status
PROVED). UnsolvedMath record UM-30006914 (`EP-518`), dataset ulamai/UnsolvedMath v1.8.0.

Stated for all large `n`, which is what is proved (for `n > 20^40`). A colouring is a graph `G` (red
edges) and its complement (blue). Paths need not be disjoint, single vertices are paths, and "`√n`
paths" means at most `√n`.
-/

/-- The vertices of `H` are covered by at most `m` paths of `H` (paths of length `0` allowed; the
paths need not be disjoint). -/
def HasPathCover {V : Type*} (H : SimpleGraph V) (m : ℝ) : Prop :=
  ∃ (k : ℕ) (u v : Fin k → V) (p : ∀ i, H.Walk (u i) (v i)),
    (k : ℝ) ≤ m ∧ (∀ i, (p i).IsPath) ∧ ∀ x : V, ∃ i, x ∈ (p i).support

/-- Erdős Problem 518 (Erdős-Gyárfás), for large `n`: for all large `n`, in every red/blue colouring
of the edges of `K_n` (red edges `G`, blue edges `Gᶜ`) the vertices are covered by at most `√n`
paths of one colour. -/
def sameColourPathCoverSqrt : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ G : SimpleGraph (Fin n),
    HasPathCover G (Real.sqrt n) ∨ HasPathCover Gᶜ (Real.sqrt n)

/--
Resolved true for large `n`: Pokrovskiy, Versteegen and Williams (Theorem 1.3) proved that for `n >
20^40` the vertices of every 2-edge-coloured `K_n` are covered by `√n` monochromatic paths of one
colour (not necessarily disjoint); `⌊√n⌋` paths can be necessary. Source: T. F. Bloom, Erdős
Problems, Problem #518, https://www.erdosproblems.com/518 (status PROVED); resolution: A.
Pokrovskiy, L. Versteegen and E. Williams, A proof of a conjecture of Erdős and Gyárfás on
monochromatic path covers, arXiv:2409.03623 (2024), Theorem 1.3: for all n > 20^40, every
2-edge-coloured K_n is covered by √n monochromatic paths of the same colour,
https://arxiv.org/abs/2409.03623.
-/
public theorem_wanted sameColourPathCoverSqrt_holds : sameColourPathCoverSqrt

end MathlibExt.GraphTheory.MonochromaticPathCoverErdosProblem518Wanted
