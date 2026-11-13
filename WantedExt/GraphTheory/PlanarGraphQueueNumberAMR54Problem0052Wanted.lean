/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Queue-number of planar graphs (Open Problems Project, Problem 52)

The Open Problems Project, Problem 52: does every planar graph have `O(1)` queue-number? A queue
layout is a linear order of the vertices and a partition of the edges into queues with no two nested
edges, `x y` being nested inside `v w` if `v < x < y < w`.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.Planarity

@[expose] public section

namespace MathlibExt.GraphTheory.PlanarGraphQueueNumberAMR54Problem0052Wanted

/-!
Source: E. D. Demaine, J. S. B. Mitchell and J. O'Rourke (eds.), The Open Problems Project, Problem
52, https://topp.openproblem.net/p52. UnsolvedMath record UM-05500052 (`AMR-054-0052`), dataset
ulamai/UnsolvedMath v1.8.0.

Planarity is MathlibExt's `SimpleGraph.IsPlanar`: an injective placement of the vertices in `ℝ²`
such that the straight segments of two distinct edges meet only in common ends; by Fáry's theorem
this is planarity for finite simple graphs. A `k`-queue layout is an injective `ord : V → ℕ` (a
linear order) and a map from edges to `Fin k` such that edges in the same queue are never nested, as
in the problem and in Dujmović et al., §1.
-/

/-- `G` has a `k`-queue layout: a linear order of the vertices (`ord` injective) and an assignment
of the edges to `k` queues such that no two edges in the same queue are nested, where `x y` is
nested inside `v w` if `v < x < y < w`. -/
def HasQueueLayout {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (ord : V → ℕ) (q : Sym2 V → Fin k), Function.Injective ord ∧
    ∀ v w x y, G.Adj v w → G.Adj x y → ord v < ord x → ord x < ord y → ord y < ord w →
      q s(v, w) ≠ q s(x, y)

/-- The Heath-Leighton-Rosenberg conjecture: planar graphs have bounded queue-number, that is, some
`Q` bounds the queue-number of every finite planar graph. -/
def planarGraphsHaveBoundedQueueNumber : Prop :=
  ∃ Q : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.IsPlanar → HasQueueLayout G Q

/--
Resolved true: Dujmović, Joret, Micek, Morin, Ueckerdt and Wood prove that planar graphs have
bounded queue-number (a universal constant bounds the queue-number of every planar graph), the
Heath-Leighton-Rosenberg conjecture. Source: E. D. Demaine, J. S. B. Mitchell and J. O'Rourke
(eds.), The Open Problems Project, Problem 52, https://topp.openproblem.net/p52; resolution: V.
Dujmović, G. Joret, P. Micek, P. Morin, T. Ueckerdt and D. R. Wood, Planar graphs have bounded
queue-number, FOCS 2019 and J. ACM (2020); arXiv:1904.04791, abstract and main theorem: planar
graphs have bounded queue-number, proving the conjecture of Heath, Leighton and Rosenberg (1992),
https://arxiv.org/abs/1904.04791.
-/
public theorem_wanted planarGraphsHaveBoundedQueueNumber_holds : planarGraphsHaveBoundedQueueNumber

end MathlibExt.GraphTheory.PlanarGraphQueueNumberAMR54Problem0052Wanted
