/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The double-cut-and-join distance formula

Genomes on the same `N` genes are given, as in
`WantedExt.Complexity.NPComplete.DCJMedianWanted`, by their adjacencies: gene `g` has the
extremities `2g` (tail) and `2g + 1` (head), and a genome is a simple graph on the extremities
`Fin (2N)` in which each extremity lies in at most one adjacency (an extremity in none is a
telomere). Chromosomes may be any mix of linear and circular ones. A double cut and join (DCJ)
cuts zero, one or two adjacencies and rejoins the freed extremities and telomeres (`IsDCJ`); one
that joins two telomeres cuts none. The DCJ distance `d_DCJ(A, B)` is the least number of DCJs
transforming `A` into `B` (`DCJWithin`).

The adjacency graph `AG(A, B)` has a vertex for each adjacency and each telomere of `A` and of
`B`, and an edge for each extremity, joining the vertex of `A` containing it to the vertex of
`B` containing it. Its connected components are cycles and paths; a path is odd if it has an
odd number of edges. They correspond to the connected components of the union graph `A ⊔ B` on
the extremities: a component of `AG(A, B)` is a cycle exactly when every extremity in it lies
in an adjacency of `A` and in an adjacency of `B`, and its number of edges is its number of
extremities.

**Theorem 1** (Bergeron–Mixtacki–Stoye 2006). `d_DCJ(A, B) = N - (C + I/2)`, where `C` is the
number of cycles and `I` the number of odd paths of `AG(A, B)`.

The formula is stated cleared of the denominator, as `2 d_DCJ = 2N - 2C - I`, together with the
attainment and the minimality of `d_DCJ`. The linear-time sorting algorithm (Algorithm 2) is not
stated.

Sources: A. Bergeron, J. Mixtacki and J. Stoye, "A unifying view of genome rearrangements",
WABI 2006, LNBI 4175, Springer, pp. 163-173, 2006, doi:10.1007/11851561_16, Theorem 1; DCJ
operation of S. Yancopoulos, O. Attie and R. Friedberg, Bioinformatics 21(16):3340-3346, 2005.
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Complexity.NPComplete.DCJMedianWanted
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.DCJDistanceWanted

open MetaMathlibExt.Complexity.NPComplete.DCJMedian

variable {N : ℕ}

/-- The component `K` of `A ⊔ B` corresponds to a cycle of the adjacency graph: every extremity
in `K` lies in an adjacency of `A` and in an adjacency of `B`. -/
def IsCycleComponent (A B : SimpleGraph (Fin (2 * N))) (K : (A ⊔ B).ConnectedComponent) :
    Prop :=
  ∀ v, (A ⊔ B).connectedComponentMk v = K → (∃ w, A.Adj v w) ∧ ∃ w, B.Adj v w

/-- The component `K` of `A ⊔ B` corresponds to an odd path of the adjacency graph: it is not a
cycle and has an odd number of extremities (the edges of its path). -/
def IsOddPathComponent (A B : SimpleGraph (Fin (2 * N))) (K : (A ⊔ B).ConnectedComponent) :
    Prop :=
  ¬ IsCycleComponent A B K ∧ Odd (Nat.card {v // (A ⊔ B).connectedComponentMk v = K})

/-- The number `C` of cycles of the adjacency graph. -/
noncomputable def numCycles (A B : SimpleGraph (Fin (2 * N))) : ℕ :=
  Nat.card {K : (A ⊔ B).ConnectedComponent // IsCycleComponent A B K}

/-- The number `I` of odd paths of the adjacency graph. -/
noncomputable def numOddPaths (A B : SimpleGraph (Fin (2 * N))) : ℕ :=
  Nat.card {K : (A ⊔ B).ConnectedComponent // IsOddPathComponent A B K}

/-- **The DCJ distance formula** (Bergeron–Mixtacki–Stoye 2006, Theorem 1). For genomes `A`
and `B` on the same `N` genes (simple graphs on the extremities `Fin (2N)` in which each
extremity lies in at most one adjacency), there is `d` with `2d = 2N - 2C - I`, where `C` and
`I` are the numbers of cycles and odd paths of the adjacency graph, such that at most `d` DCJs
transform `A` into `B` and no fewer than `d` DCJs do; that is,
`d_DCJ(A, B) = N - (C + I/2)`.

Source: A. Bergeron, J. Mixtacki and J. Stoye, WABI 2006, LNBI 4175, pp. 163-173, Theorem 1. -/
theorem_wanted dcj_distance (A B : SimpleGraph (Fin (2 * N))) (hA : IsGenome A)
    (hB : IsGenome B) :
    ∃ d : ℕ, 2 * (d : ℤ) = 2 * N - 2 * numCycles A B - numOddPaths A B ∧
      DCJWithin A B d ∧ ∀ k, DCJWithin A B k → d ≤ k

end WantedExt.Biology.ComputationalBiology.DCJDistanceWanted
