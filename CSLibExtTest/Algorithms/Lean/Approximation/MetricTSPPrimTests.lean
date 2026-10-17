/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Approximation.MetricTSPPrim
public meta import CSLibExt.Algorithms.Lean.Approximation.MetricTSPPrim
public meta import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Rat

/-!
# Metric TSP with Prim: tests

Executed fixtures with rational costs (the theorem is over `ℝ`; the same program runs over `ℚ`):
Manhattan distances between points in the plane. Each run checks that the tour visits every
vertex once and compares its cost with twice the optimal tour, found by brute force over all
tours from vertex `0`; it throws otherwise.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MetricTSP

private def manhattan {n : ℕ} (pts : Fin n → ℚ × ℚ) (i j : Fin n) : ℚ :=
  |(pts i).1 - (pts j).1| + |(pts i).2 - (pts j).2|

private def check (label : String) (n : ℕ) (pts : Fin n → ℚ × ℚ) (root : Fin n) : IO Unit := do
  let d := manhattan pts
  let tour := (primTSPTour d root).ret
  let isTour := tour.Nodup && tour.length == n
  let zero := (List.finRange n).filter (fun v => v.val = 0)
  let rest := (List.finRange n).filter (fun v => v.val ≠ 0)
  let opt := (rest.permutations.map fun p => tourCost d (zero ++ p)).foldl min
    (tourCost d (List.finRange n))
  let c := tourCost d tour
  unless isTour && c ≤ 2 * opt do
    throw (IO.userError s!"{label}: tour {tour.map (·.val)} costs {c}, optimum {opt}")
  IO.println s!"{label}: tour {tour.map (·.val)} costs {c} ≤ 2 · {opt}"

#eval check "hexagon" 6
  (fun i => #[(0, 0), (2, 0), (3, 2), (2, 4), (0, 4), (-1, 2)][i.val]!) 0
#eval check "cluster and outlier" 6
  (fun i => #[(0, 0), (1, 0), (0, 1), (1, 1), (10, 10), (5, 0)][i.val]!) 2
#eval check "seven scattered points" 7
  (fun i => (((i.val * 37 + 11) % 13 : ℕ), ((i.val * 53 + 7) % 11 : ℕ))) 3
#eval check "collinear" 5 (fun i => ((i.val : ℚ) ^ 2, 0)) 4

example {n : ℕ} {d : Fin n → Fin n → ℝ} (hd : IsMetricCost d) (root : Fin n) {H : List (Fin n)}
    (hH : IsTour (List.finRange n) H) :
    tourCost d (primTSPTour d root).ret ≤ 2 * tourCost d H :=
  primTSPTour_two_approx hd root hH

/-- The tour theorem needs no real weights: here with rational costs. -/
example (d : Fin 4 → Fin 4 → ℚ) : IsTour (List.finRange 4) (primTSPTour d 0).ret :=
  primTSPTour_isTour d 0

#print axioms primTSPTour_two_approx
#print axioms primTSPTour_isTour
#print axioms primTree_isMinimumSpanningTree
#print axioms isSpanning_buildForest
#print axioms weight_buildForest
#print axioms parentTree_primParents
#print axioms primTree_isTree
#print axioms sum_edgeFinset_eq

end Cslib.Algorithms.Lean.MetricTSP
