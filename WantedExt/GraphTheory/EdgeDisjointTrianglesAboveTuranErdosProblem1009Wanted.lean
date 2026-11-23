/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Edge-disjoint triangles above the Turán number (Erdős Problem 1009)

Erdős Problem 1009: is it true that for every `c > 0` there is `f(c)` such that every graph on `n`
vertices with at least `⌊n² / 4⌋ + k` edges, where `k < c n`, contains at least `k - f(c)`
edge-disjoint triangles?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MathlibExt.GraphTheory.EdgeDisjointTrianglesAboveTuranErdosProblem1009Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1009, https://www.erdosproblems.com/1009 (status
PROVED). UnsolvedMath record UM-30007123 (`EP-1009`), dataset ulamai/UnsolvedMath v1.8.0.

A family of edge-disjoint triangles is a finite set of `3`-cliques any two of which share at most
one vertex; `k - f(c)` is written `k ≤ |T| + f(c)` to avoid truncated subtraction. Compared with the
formal-conjectures statement `ErdosProblems/1009.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 1009: for every `c > 0` there is `f(c)` such that every graph on `n` vertices with
at least `⌊n² / 4⌋ + k` edges, where `k < c n`, has at least `k - f(c)` edge-disjoint triangles (a
family of `3`-cliques any two of which share at most one vertex). -/
def edgeDisjointTrianglesAboveTuran : Prop :=
  ∀ c : ℝ, 0 < c → ∃ f : ℕ, ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
    n ^ 2 / 4 + k ≤ G.edgeSet.ncard → (k : ℝ) < c * n →
      ∃ T : Finset (Finset (Fin n)), (∀ t ∈ T, G.IsNClique 3 t) ∧
        (T : Set (Finset (Fin n))).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ k ≤ T.card + f

/--
Resolved true: Győri proved the statement with `f(c) ≪ c²`, and `f(c) = 0` for `c < 2` (odd `n`) or
`c < 3/2` (even `n`); erdosproblems.com/1009 lists the problem as proved, with a formal proof in
plby/lean-proofs (`Erdos1009.lean`). Source: T. F. Bloom, Erdős Problems, Problem #1009,
https://www.erdosproblems.com/1009 (status PROVED); resolution: E. Győri, On the number of
edge-disjoint triangles in graphs of given size, in Combinatorics (Eger, 1987), Colloq. Math. Soc.
János Bolyai (1988), 267-276, affirmative answer with f(c) ≪ c² (erdosproblems.com/1009),
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1009.lean#L2347.
-/
public theorem_wanted edgeDisjointTrianglesAboveTuran_holds : edgeDisjointTrianglesAboveTuran

end MathlibExt.GraphTheory.EdgeDisjointTrianglesAboveTuranErdosProblem1009Wanted
