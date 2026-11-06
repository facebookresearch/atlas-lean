/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.FasterAPSP.Basic
public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.Extend

import CSLibExt.Algorithms.Lean.Graph.ShortestPath.MatrixPower
import CSLibExt.Algorithms.Lean.Graph.ShortestPath.SlowAPSP
import Mathlib.Algebra.Order.Group.Int

/-!
# Bounded min-plus paths and no-negative-cycle distances

This module instantiates the single shared arbitrary-power path theorem on the
actual FASTER-APSP return. Only the original input has a zero-diagonal premise.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Matrix

private theorem edgeBounded_distance_of_slowAPSP {n r : Nat}
    (W L0 : Vector (Vector (MinTropical (WithTop Int)) n) n)
    (hdiag : ∀ i : Fin n, MinTropical.untrop ((W.get i).get i) = 0)
    (hinit : ∀ i j : Fin n,
      MinTropical.untrop ((L0.get i).get j) = if i = j then 0 else ⊤)
    (hr : n - 1 ≤ r)
    (hNoCycle : FloydWarshall.NoNegativeCycle
      (Matrix.of fun x y => MinTropical.untrop ((W.get x).get y)))
    (i j : Fin n) (d : WithTop Int)
    (hbound : FloydWarshall.IsEdgeBoundedShortestPathWeight
      (Matrix.of fun x y => MinTropical.untrop ((W.get x).get y)) r i j d) :
    FloydWarshall.IsStageShortestPathWeight
      (Matrix.of fun x y => MinTropical.untrop ((W.get x).get y)) n i j d := by
  have hslowBound := slowAPSP_edgeBounded W L0 hdiag hinit i j
  have hslow := slowAPSP_distance_spec W L0 hdiag hinit hNoCycle i j
  have hle : d ≤ MinTropical.untrop (((slowAPSP W L0).ret.get i).get j) := by
    rcases hslowBound.2 with htop | ⟨p, hp, hlen, hweight⟩
    · rw [htop]
      exact le_top
    · rw [← hweight]
      exact hbound.1 p hp (hlen.trans hr)
  refine ⟨fun p hp hstage => hle.trans (hslow.1 p hp hstage), ?_⟩
  rcases hbound.2 with htop | ⟨p, hp, _, hweight⟩
  · exact Or.inl htop
  · exact Or.inr ⟨p, hp, fun v _ => v.isLt, hweight⟩

/-- **FASTER-APSP computes edge-bounded shortest-path weights.** Let $W$ be an $n \times n$
matrix with entries in $\mathbb{Z} \cup \{\infty\}$, read as edge weights of a directed graph on
the vertices $0, \dots, n - 1$ (weight $\infty$ meaning no edge), with $W_{ii} = 0$ for every
$i$, and let $k = \lceil \log_2 (n - 1) \rceil$ be the least natural number with
$n - 1 \le 2^k$. Run FASTER-APSP on $W$ over the min-plus semiring, whose addition is $\min$
and whose multiplication is $+$. Then for all vertices $i$ and $j$, the returned entry $d$ at
$(i, j)$ is at most the weight of every path from $i$ to $j$ with at most $2^k$ edges, all of
finite weight, and either $d = \infty$ or $d$ is the weight of such a path. Paths are
nonempty vertex sequences and may repeat vertices; no assumption on negative cycles is made. -/
public theorem fasterAPSP_edgeBounded {n : Nat}
    (W : Vector (Vector (MinTropical (WithTop Int)) n) n)
    (hdiag : ∀ i : Fin n, MinTropical.untrop ((W.get i).get i) = 0)
    (i j : Fin n) :
    FloydWarshall.IsEdgeBoundedShortestPathWeight
      (Matrix.of fun x y => MinTropical.untrop ((W.get x).get y))
      (2 ^ Nat.clog 2 (n - 1)) i j
      (MinTropical.untrop (((fasterAPSP W).ret.get i).get j)) := by
  have hbound := matrix_pow_edgeBounded
    (Matrix.of fun x y => (W.get x).get y) hdiag
    (2 ^ Nat.clog 2 (n - 1)) i j
  have hret := congrArg (fun M => MinTropical.untrop (M i j)) (fasterAPSP_ret W)
  change MinTropical.untrop (((fasterAPSP W).ret.get i).get j) =
    MinTropical.untrop
      ((Matrix.of (fun x y => (W.get x).get y) ^ (2 ^ Nat.clog 2 (n - 1))) i j) at hret
  rw [← hret] at hbound
  exact hbound

/-- **FASTER-APSP computes shortest-path weights.** Let $W$ be an $n \times n$ matrix with
entries in $\mathbb{Z} \cup \{\infty\}$, read as edge weights of a directed graph on the
vertices $0, \dots, n - 1$ (weight $\infty$ meaning no edge), such that $W_{ii} = 0$ for every
$i$ and $W$ has no negative cycle. Run FASTER-APSP on $W$ over the min-plus semiring, whose
addition is $\min$ and whose multiplication is $+$. Then for all vertices $i$ and $j$, the
returned entry $d$ at $(i, j)$ is the shortest-path weight from $i$ to $j$: $d$ is at most the
weight of every path from $i$ to $j$ all of whose edges have finite weight, and either
$d = \infty$ or $d$ is the weight of such a path. Paths are nonempty vertex sequences and may
repeat vertices. -/
public theorem fasterAPSP_distance_spec {n : Nat}
    (W : Vector (Vector (MinTropical (WithTop Int)) n) n)
    (hdiag : ∀ i : Fin n, MinTropical.untrop ((W.get i).get i) = 0)
    (hNoCycle : FloydWarshall.NoNegativeCycle
      (Matrix.of fun x y => MinTropical.untrop ((W.get x).get y)))
    (i j : Fin n) :
    FloydWarshall.IsStageShortestPathWeight
      (Matrix.of fun x y => MinTropical.untrop ((W.get x).get y)) n i j
      (MinTropical.untrop (((fasterAPSP W).ret.get i).get j)) := by
  let L0 : Vector (Vector (MinTropical (WithTop Int)) n) n :=
    Vector.ofFn fun x => Vector.ofFn fun y => MinTropical.trop (if x = y then 0 else ⊤)
  have hinit : ∀ x y : Fin n,
      MinTropical.untrop ((L0.get x).get y) = if x = y then 0 else ⊤ := by
    intro x y
    by_cases hxy : x = y
    · simp [L0, Vector.get_eq_getElem, hxy]
    · simp [L0, Vector.get_eq_getElem, hxy]
  exact edgeBounded_distance_of_slowAPSP W L0 hdiag hinit
    (Nat.le_pow_clog (by decide) (n - 1)) hNoCycle i j _
    (fasterAPSP_edgeBounded W hdiag i j)

end Cslib.Algorithms.Lean.Matrix
