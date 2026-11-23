/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# End-devouring sets of rays with prescribed start vertices (Open Problem Garden 735)

Open Problem Garden, End-Devouring Rays (A. Georgakopoulos): let `G` be a graph, `ω` a countable end
of `G`, and `K` an infinite set of pairwise disjoint `ω`-rays. Then there is a set `K'` of pairwise
disjoint `ω`-rays that devours `ω` such that the set of starting vertices of rays in `K'` equals the
set of starting vertices of rays in `K`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Set.Countable
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.GraphTheory.EndDevouringRaysOpenGardenProblem735Wanted

/-!
Source: Open Problem Garden, End-Devouring Rays (node 735; A. Georgakopoulos),
http://www.openproblemgarden.org/op/end_devouring_rays. UnsolvedMath record UM-00003306 (`OPG-735`),
dataset ulamai/UnsolvedMath v1.8.0.

Graphs are arbitrary simple graphs (`V : Type` of any cardinality). A ray is an injective sequence
of vertices with consecutive vertices adjacent, starting at `r 0`; two rays are equivalent when no
finite vertex set separates them (tails in one component of `G - S` for every finite `S`,
Gollin-Heuer, Section 1), and the end `ω` is the class of a fixed ray `r₀`. As on the source page, a
set of rays devours `ω` if every `ω`-ray meets one of them, and `ω` is countable if some countable
set of rays devours it; as in Gollin-Heuer (Section 1), the devouring set is taken to consist of
`ω`-rays (they note that `ω` is countable exactly when it has no uncountable set of disjoint rays).
`K` is required to be infinite, as on the page; for `K = ∅` the claim fails, since the empty set
devours no end.
-/

/-- A ray of `G`: an injective sequence `r 0, r 1, …` of vertices with `r n` adjacent to
`r (n + 1)` for every `n`; its start vertex is `r 0`. -/
def IsRay {V : Type} (G : SimpleGraph V) (r : ℕ → V) : Prop :=
  Function.Injective r ∧ ∀ n, G.Adj (r n) (r (n + 1))

/-- The rays `r` and `s` cannot be separated by finitely many vertices: for every finite vertex
set `S`, tails of `r` and of `s` avoid `S` and lie in the same component of `G - S`. -/
def RaysEquiv {V : Type} (G : SimpleGraph V) (r s : ℕ → V) : Prop :=
  ∀ S : Finset V, ∃ m n, (∀ i, m ≤ i → r i ∉ S) ∧ (∀ j, n ≤ j → s j ∉ S) ∧
    Relation.ReflTransGen (fun x y => x ∉ S ∧ y ∉ S ∧ G.Adj x y) (r m) (s n)

/-- `s` is an `ω`-ray for the end `ω` of the ray `r₀`: a ray equivalent to `r₀`. -/
def IsEndRay {V : Type} (G : SimpleGraph V) (r₀ s : ℕ → V) : Prop :=
  IsRay G s ∧ RaysEquiv G r₀ s

/-- The set `R` of rays devours the end of `r₀`: every ray of that end meets some ray in `R`. -/
def Devours {V : Type} (G : SimpleGraph V) (r₀ : ℕ → V) (R : Set (ℕ → V)) : Prop :=
  ∀ s, IsEndRay G r₀ s → ∃ r ∈ R, ∃ i j, s i = r j

/-- The rays in `R` are pairwise (vertex-)disjoint. -/
def PairwiseDisjointRays {V : Type} (R : Set (ℕ → V)) : Prop :=
  R.Pairwise fun r s => Disjoint (Set.range r) (Set.range s)

/-- Georgakopoulos's problem: if `ω` (the end of the ray `r₀`) is countable, i.e. some countable set
of `ω`-rays devours it, then for every infinite set `R` of pairwise disjoint `ω`-rays there is a set
`R'` of pairwise disjoint `ω`-rays that devours `ω` and has the same set of start vertices. -/
def endDevouringRays : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) (r₀ : ℕ → V), IsRay G r₀ →
    (∃ R₀ : Set (ℕ → V), R₀.Countable ∧ (∀ r ∈ R₀, IsEndRay G r₀ r) ∧ Devours G r₀ R₀) →
    ∀ R : Set (ℕ → V), R.Infinite → (∀ r ∈ R, IsEndRay G r₀ r) → PairwiseDisjointRays R →
      ∃ R' : Set (ℕ → V), (∀ r ∈ R', IsEndRay G r₀ r) ∧ PairwiseDisjointRays R' ∧
        Devours G r₀ R' ∧ (fun r => r 0) '' R' = (fun r => r 0) '' R

/--
Resolved true: Gollin and Heuer proved (Theorem 1) that for every countable end `ω` and every set
`R` of disjoint `ω`-rays there is a set of disjoint `ω`-rays with the same start vertices that
devours `ω`, confirming Georgakopoulos's conjecture (the case of infinite `R`). Source: Open Problem
Garden, End-Devouring Rays (node 735; A. Georgakopoulos),
http://www.openproblemgarden.org/op/end_devouring_rays; resolution: J. P. Gollin and K. Heuer,
Infinite end-devouring sets of rays with prescribed start vertices, Discrete Math. 341 (2018),
2117-2120, doi:10.1016/j.disc.2018.04.012; arXiv:1704.06577, Theorem 1: let G be a graph, ω a
countable end of G and R any set of disjoint ω-rays; then there is a set R' of disjoint ω-rays that
devours ω and the start vertices of the rays in R and R' are the same; the abstract and introduction
say this confirms Georgakopoulos's conjecture [3, Problem 1],
https://doi.org/10.1016/j.disc.2018.04.012.
-/
public theorem_wanted endDevouringRays_holds : endDevouringRays

end MathlibExt.GraphTheory.EndDevouringRaysOpenGardenProblem735Wanted
