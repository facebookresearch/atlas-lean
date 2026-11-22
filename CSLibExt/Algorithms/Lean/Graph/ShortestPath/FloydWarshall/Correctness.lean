/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall.Basic

import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall.Internal.Execution
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall.Internal.Simplify
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall.Internal.Stage

/-!
# Floyd-Warshall correctness

Stage-optimality, all-pairs shortest-distance correctness, reachability, and sound negative-cycle
detection for the executable recurrence.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloydWarshall

open Internal

/-- **Floyd–Warshall computes shortest-path distances.** Let $w$ assign a weight in
$\mathbb{Z} \cup \{\infty\}$ to each ordered pair of vertices in $\{0, \dots, n-1\}$, suppose that
$w$ has no negative cycle, and let $D$ be the distance matrix computed by Floyd–Warshall from $w$.
Then for all vertices $s$ and $t$, $D(s, t)$ is at most the weight of every weighted path from $s$
to $t$, and either $D(s, t) = \infty$ or $D(s, t)$ is the weight of some weighted path from $s$ to
$t$. Here a weighted path is a nonempty vertex sequence in which every consecutive pair has finite
weight, and its weight is the sum of these weights.

Formally this is the stage-$n$ characterization, which considers only paths whose intermediate
vertices are all below $n$; every path qualifies. -/
theorem floydWarshall_distance_spec {n : Nat}
    (weight : Fin n → Fin n → WithTop Int) (source target : Fin n)
    (hNoCycle : NoNegativeCycle weight) :
    IsStageShortestPathWeight weight n source target
      ((floydWarshall weight).ret source target) := by
  rw [floydWarshall_ret]
  exact stageValue_spec weight hNoCycle n (by omega) source target

/-- **Finite Floyd–Warshall distances are attained.** Let $w$ assign a weight in
$\mathbb{Z} \cup \{\infty\}$ to each ordered pair of vertices in $\{0, \dots, n-1\}$, and let $D$
be the distance matrix computed by Floyd–Warshall from $w$. If $D(s, t) = d$ for vertices $s$, $t$
and an integer $d$, then there is a weighted path from $s$ to $t$ (a nonempty vertex sequence from
$s$ to $t$ in which every consecutive pair has finite weight) whose weight, the sum of the weights
of its consecutive pairs, is $d$. -/
theorem floydWarshall_distance_realized {n : Nat}
    (weight : Fin n → Fin n → WithTop Int) (source target : Fin n) (distance : Int)
    (hDistance : (floydWarshall weight).ret source target = (distance : WithTop Int)) :
    ∃ path, IsWeightedPath weight source target path ∧
      pathWeight weight path = (distance : WithTop Int) := by
  rw [floydWarshall_ret] at hDistance
  obtain ⟨path, hpath, _, hweight⟩ :=
    stageValue_realized weight n (by omega) source target distance hDistance
  exact ⟨path, hpath, hweight⟩

/-- **No path is shorter than the Floyd–Warshall distance.** Let $w$ assign a weight in
$\mathbb{Z} \cup \{\infty\}$ to each ordered pair of vertices in $\{0, \dots, n-1\}$, suppose that
$w$ has no negative cycle, and let $D$ be the distance matrix computed by Floyd–Warshall from $w$.
Then for all vertices $s$ and $t$ and every weighted path $p$ from $s$ to $t$ (a nonempty vertex
sequence from $s$ to $t$ in which every consecutive pair has finite weight), $D(s, t)$ is at most
the weight of $p$, the sum of the weights of its consecutive pairs. -/
theorem floydWarshall_distance_minimal {n : Nat}
    (weight : Fin n → Fin n → WithTop Int) (source target : Fin n)
    (path : List (Fin n)) (hNoCycle : NoNegativeCycle weight)
    (hPath : IsWeightedPath weight source target path) :
    (floydWarshall weight).ret source target ≤ pathWeight weight path := by
  rw [floydWarshall_ret]
  apply stageValue_le_of_noNegativeCycle weight hNoCycle n (by omega) hPath
  intro vertex _
  exact vertex.isLt

/-- **Floyd–Warshall reports $\infty$ exactly for unreachable pairs.** Let $w$ assign a weight
in $\mathbb{Z} \cup \{\infty\}$ to each ordered pair of vertices in $\{0, \dots, n-1\}$, and let $D$
be the distance matrix computed by Floyd–Warshall from $w$. For all vertices $s$ and $t$,
$D(s, t) = \infty$ if and only if there is no weighted path from $s$ to $t$, that is, no nonempty
vertex sequence from $s$ to $t$ in which every consecutive pair has finite weight. -/
theorem floydWarshall_distance_eq_top_iff {n : Nat}
    (weight : Fin n → Fin n → WithTop Int) (source target : Fin n) :
    (floydWarshall weight).ret source target = ⊤ ↔
      ¬∃ path, IsWeightedPath weight source target path := by
  constructor
  · intro htop
    rintro ⟨path, hpath⟩
    obtain ⟨simple, hsimple, hnodup⟩ := hpath.exists_nodup
    have hbound : InternalVerticesBelow n simple := by
      intro vertex _
      exact vertex.isLt
    have hle := stageValue_le_nodup weight n (by omega) hsimple hnodup hbound
    rw [floydWarshall_ret] at htop
    rw [htop] at hle
    exact pathWeight_ne_top weight hsimple (top_unique hle)
  · intro hnoPath
    by_contra hnotTop
    obtain ⟨distance, hdistance⟩ := WithTop.ne_top_iff_exists.mp hnotTop
    obtain ⟨path, hpath, _⟩ := floydWarshall_distance_realized weight source target distance
      hdistance.symm
    exact hnoPath ⟨path, hpath⟩

/-- **A negative diagonal entry in Floyd–Warshall reveals a negative cycle.** Let $w$ assign a
weight in $\mathbb{Z} \cup \{\infty\}$ to each ordered pair of vertices in $\{0, \dots, n-1\}$, and
let $D$ be the distance matrix computed by Floyd–Warshall from $w$. If $D(v, v) < 0$ for some vertex
$v$, then $w$ has a negative cycle: a vertex sequence $v_0, v_1, \dots, v_m$ with $m \ge 1$ and
$v_m = v_0$, whose vertices $v_0, \dots, v_{m-1}$ are pairwise distinct, in which every consecutive
pair has finite weight, and whose total weight is negative. -/
theorem floydWarshall_hasNegativeDiagonal_sound {n : Nat}
    (weight : Fin n → Fin n → WithTop Int)
    (hNegative : hasNegativeDiagonal (floydWarshall weight).ret = true) :
    HasNegativeCycle weight := by
  obtain ⟨vertex, hdiagonal⟩ :=
    (hasNegativeDiagonal_eq_true_iff (floydWarshall weight).ret).mp hNegative
  have hnotTop : (floydWarshall weight).ret vertex vertex ≠ ⊤ := ne_top_of_lt hdiagonal
  obtain ⟨distance, hdistance⟩ := WithTop.ne_top_iff_exists.mp hnotTop
  obtain ⟨path, hpath, hpathWeight⟩ :=
    floydWarshall_distance_realized weight vertex vertex distance hdistance.symm
  have hpathNegative : pathWeight weight path < 0 := by
    rw [hpathWeight, hdistance]
    exact hdiagonal
  rcases negativeCycle_or_simplifies weight hpath with hcycle | ⟨simple, hsimple,
      hnodup, hweight, _⟩
  · exact hcycle
  · have hsimpleNegative : pathWeight weight simple < 0 := hweight.trans_lt hpathNegative
    have hclosed : simple.head hsimple.ne_nil = simple.getLast hsimple.ne_nil := by
      rw [hsimple.head_eq, hsimple.getLast_eq]
    obtain ⟨point, hpoint⟩ :=
      (List.Nodup.head_eq_getLast_iff hsimple.ne_nil hnodup).mp hclosed
    subst simple
    simp [pathWeight] at hsimpleNegative

/-- **Without negative cycles, Floyd–Warshall finds no negative diagonal entry.** Let $w$
assign a weight in $\mathbb{Z} \cup \{\infty\}$ to each ordered pair of vertices in
$\{0, \dots, n-1\}$, and let $D$ be the distance matrix computed by Floyd–Warshall from $w$. If $w$
has no negative cycle, then the negative-diagonal check on $D$ returns false, that is,
$D(v, v) \ge 0$ for every vertex $v$. -/
theorem floydWarshall_hasNegativeDiagonal_eq_false {n : Nat}
    (weight : Fin n → Fin n → WithTop Int) (hNoCycle : NoNegativeCycle weight) :
    hasNegativeDiagonal (floydWarshall weight).ret = false := by
  cases hflag : hasNegativeDiagonal (floydWarshall weight).ret with
  | false => rfl
  | true => exact False.elim (hNoCycle (floydWarshall_hasNegativeDiagonal_sound weight hflag))

end Cslib.Algorithms.Lean.FloydWarshall
