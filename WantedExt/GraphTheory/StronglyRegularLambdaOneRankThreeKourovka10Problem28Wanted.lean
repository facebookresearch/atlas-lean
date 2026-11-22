/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Strongly regular graphs with `λ = 1` and rank `3` (Kourovka Notebook Problem 10.28)

Kourovka Notebook, Archive of Solved Problems, Problem 10.28 (A. A. Makhnëv): is it true that finite
strongly regular graphs with `λ = 1` have rank `3`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

@[expose] public section

namespace MathlibExt.GraphTheory.StronglyRegularLambdaOneRankThreeKourovka10Problem28Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.28 (A. A.
Makhnëv). UnsolvedMath record UM-00700643 (`KOU-10.28`), dataset ulamai/UnsolvedMath v1.8.0.

Strongly regular is Mathlib's `SimpleGraph.IsSRGWith n k 1 μ` on a finite vertex type. Rank `3`
means that the automorphism group is transitive on vertices, on ordered pairs of adjacent vertices
and on ordered pairs of distinct non-adjacent vertices. With this reading the degenerate graphs that
`IsSRGWith` admits with `λ = 1` (complete graphs, empty graphs, disjoint unions of triangles) have
rank `3`, so they are not counterexamples.
-/

/-- `G` has rank `3`: its automorphism group is transitive on vertices, on ordered pairs of
adjacent vertices and on ordered pairs of distinct non-adjacent vertices. -/
def IsRankThree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v u' v' : V,
    ((u = v ∧ u' = v') ∨ (G.Adj u v ∧ G.Adj u' v') ∨
      (u ≠ v ∧ ¬ G.Adj u v ∧ u' ≠ v' ∧ ¬ G.Adj u' v')) →
      ∃ σ : G ≃g G, σ u = u' ∧ σ v = v'

/-- Kourovka 10.28 (A. A. Makhnëv): every finite strongly regular graph with `λ = 1` has
rank `3`. -/
def lambdaOneStronglyRegularIsRankThree : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (n k μ : ℕ),
    G.IsSRGWith n k 1 μ → IsRankThree G

/--
Resolved false: the Kourovka Archive answers 10.28 "No, not always", citing Cossidente and Penttila
(2005): some finite strongly regular graph with `λ = 1` does not have rank `3`. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.28 (A. A. Makhnëv);
resolution: A. Cossidente and T. Penttila, Hemisystems on the Hermitian surface, J. London Math.
Soc. (2) 72 (2005), 731-741, Kourovka Archive, Problem 10.28 ("No, not always").
-/
public theorem_wanted lambdaOneStronglyRegularIsRankThree_refuted :
    ¬ lambdaOneStronglyRegularIsRankThree

end MathlibExt.GraphTheory.StronglyRegularLambdaOneRankThreeKourovka10Problem28Wanted
