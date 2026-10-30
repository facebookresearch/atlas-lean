/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hamidoune's reverse-connectivity conjecture fails for `r ≥ 3` (AIM Caccetta–Häggkvist list, 6.21)

B. D. Sullivan, A Summary of Problems and Results related to the Caccetta–Häggkvist Conjecture (AIM
workshop report, arXiv:math/0605646), Conjecture 6.21 (Hamidoune, 1981): let `D` be a digraph with
`δ⁺_D ≥ r`, `δ⁻_D ≥ r` and `r ≥ 1`. Then there is an edge `(x, y)` such that `κ(y, x) ≥ r`, where
`κ(u, v)` is the maximum number of internally disjoint directed paths from `u` to `v`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MathlibExt.Combinatorics.HamidouneReverseConnectivityAIMCombinatoricsProblem191Wanted

/-!
Source: B. D. Sullivan, A Summary of Problems and Results related to the Caccetta-Haggkvist
Conjecture, AIM workshop report (2006), arXiv:math/0605646, Conjecture 6.21 and the note after it.
UnsolvedMath record UM-20001066 (`AIM-COMBINATORICS-0191`), dataset ulamai/UnsolvedMath v1.8.0.

This module states the refuted cases `r ≥ 3`; the open case `r = 2` is the OpenConjectures entry
`AIMCombinatoricsProblem191` (whose definitions WantedExt cannot import; `IsDirectedPath` copies the
entry `DirectedPathTwiceMinimumOutdegree`, and `internalVertices`, `HasInternallyDisjointPaths` copy
`AIMCombinatoricsProblem191`). Digraphs are finite, nonempty (the empty digraph would refute every
`r` vacuously), loopless and without parallel arcs: with parallel arcs counted in the degrees, an
`r`-fold directed cycle would refute every `r ≥ 2`, and Thomassen's digraphs are simple and
digon-free (his theorem is restated for simple digraphs in R. Steiner, arXiv:2604.13700, Theorem 2);
degrees count out- and in-neighbours. `κ(y, x) ≥ r` means `r` pairwise distinct directed paths
from `y` to `x`, no two sharing an internal vertex. The problem is posed for every `r`, so the
refuted part is stated existentially (some `r ≥ 3` for which the conjecture holds) and refuted.
-/

/-- A directed path: a duplicate-free vertex list whose consecutive vertices are joined by arcs. -/
def IsDirectedPath {V : Type} (D : Digraph V) (p : List V) : Prop :=
  p.Nodup ∧ p.IsChain D.Adj

/-- The internal vertices of a path given as a vertex list (all but the first and the last). -/
def internalVertices {V : Type} (p : List V) : List V :=
  p.tail.dropLast

/-- `κ(y, x) ≥ r`: there are `r` pairwise distinct directed paths from `y` to `x`, no two of which
share an internal vertex. -/
def HasInternallyDisjointPaths {V : Type} (D : Digraph V) (r : ℕ) (y x : V) : Prop :=
  ∃ P : Fin r → List V,
    (∀ i, IsDirectedPath D (P i) ∧ (P i).head? = some y ∧ (P i).getLast? = some x) ∧
      ∀ i j, i ≠ j → P i ≠ P j ∧ ∀ v ∈ internalVertices (P i), v ∉ internalVertices (P j)

/-- Hamidoune's conjecture holds for some `r ≥ 3`: every finite nonempty loopless digraph with
minimum out-degree and minimum in-degree at least `r` has an arc `(x, y)` with `κ(y, x) ≥ r`. -/
def hamidouneSomeRAtLeastThree : Prop :=
  ∃ r : ℕ, 3 ≤ r ∧ ∀ (V : Type) [Finite V] [Nonempty V] (D : Digraph V), (∀ v : V, ¬ D.Adj v v) →
    (∀ v : V, r ≤ {w | D.Adj v w}.ncard) → (∀ v : V, r ≤ {u | D.Adj u v}.ncard) →
      ∃ x y : V, D.Adj x y ∧ HasInternallyDisjointPaths D r y x

/--
Resolved false: for every `r ≥ 3` the conjecture fails. Thomassen constructed, for every positive
integer `r`, a digraph without digons with minimum out-degree and minimum in-degree at least `r` in
which no edge `(x, y)` has `κ(y, x) ≥ 3`; the report notes after Conjecture 6.21 that this is a
counterexample for all `r ≥ 3`. Source: B. D. Sullivan, A Summary of Problems and Results related to
the Caccetta-Haggkvist Conjecture, arXiv:math/0605646, Conjecture 6.21; resolution: C. Thomassen,
Even cycles in directed graphs, European J. Combin. 6 (1985) 85-89, as stated in the report's
Theorem 5.2 (part ii) and the note after Conjecture 6.21,
https://doi.org/10.1016/S0195-6698(85)80025-1.
-/
public theorem_wanted hamidouneSomeRAtLeastThree_refuted : ¬ hamidouneSomeRAtLeastThree

end MathlibExt.Combinatorics.HamidouneReverseConnectivityAIMCombinatoricsProblem191Wanted
