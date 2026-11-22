/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Geometry.AnySegmentsIntersect
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Rat
public meta import CSLibExt.Algorithms.Lean.Geometry.AnySegmentsIntersect
public meta import Mathlib.Algebra.Order.Field.Rat

/-!
# Tests for `ANY-SEGMENTS-INTERSECT`

Executed fixtures over `ℚ` compare the sweep with the brute-force test of all pairs and check
the cost bound `n² + 24 n` on: no segments, one segment, a proper crossing (also with the
endpoints given right to left), stacked disjoint segments, a left endpoint on another segment, a
shared left endpoint, a right endpoint meeting a left endpoint, a right endpoint inside another
segment, collinear overlapping and collinear disjoint segments, a crossing that becomes visible
only after a deletion exposes the two segments to each other, and covertical endpoints. Random
fixtures (fixed seed), with integer coordinates: 300 instances of 6 long segments, 300 of 25
short nearly level segments and 100 of 60 short segments, each agreeing with the brute force.
The sweep sorts with `List.mergeSort`, which `decide +kernel` does not reduce, so there are no
kernel-evaluated closed checks; closed checks instantiate the correctness and cost theorems over
`ℝ`.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Geometry

/-- The brute-force answer: some pair of distinct segments passes `SEGMENTS-INTERSECT`. -/
private meta def brute (segs : List ((ℚ × ℚ) × (ℚ × ℚ))) : Bool :=
  (List.range segs.length).any fun i => (List.range segs.length).any fun j =>
    i < j && (segmentsIntersect (segs.getD i default).1 (segs.getD i default).2
      (segs.getD j default).1 (segs.getD j default).2).ret

private meta def run (segs : List ((ℚ × ℚ) × (ℚ × ℚ))) : TimeM ℕ Bool :=
  anySegmentsIntersect (fun i : Fin segs.length => segs[i])

private meta def check (label : String) (segs : List ((ℚ × ℚ) × (ℚ × ℚ))) (expected : Bool) :
    IO Unit := do
  let r := run segs
  let n := segs.length
  unless r.ret == expected && r.ret == brute segs && r.time ≤ n * n + 24 * n do
    throw (IO.userError s!"{label}: got {r.ret} (brute force {brute segs}) with cost {r.time}")
  IO.println s!"{label}: {r.ret}, cost {r.time} (bound {n * n + 24 * n})"

#eval check "no segments" [] false
#eval check "one segment" [((0, 0), (1, 1))] false
#eval check "proper crossing" [((0, 0), (4, 4)), ((0, 4), (4, 0))] true
#eval check "proper crossing, endpoints right to left" [((4, 4), (0, 0)), ((4, 0), (0, 4))] true
#eval check "stacked, disjoint" [((0, 0), (4, 1)), ((1, 2), (5, 3)), ((0, 4), (3, 5))] false
#eval check "left endpoint on another segment" [((0, 0), (4, 0)), ((2, 0), (3, 5))] true
#eval check "shared left endpoint" [((0, 0), (4, 1)), ((0, 0), (4, -1))] true
#eval check "right endpoint meets a left endpoint" [((0, 0), (2, 2)), ((2, 2), (4, 0))] true
#eval check "right endpoint inside another segment" [((0, 0), (2, 1)), ((1, -1), (3, 3))] true
#eval check "collinear, overlapping" [((0, 0), (2, 2)), ((1, 1), (3, 3))] true
#eval check "collinear, disjoint" [((0, 0), (1, 1)), ((2, 2), (3, 3))] false
#eval check "crossing exposed by a deletion"
  [((0, 0), (10, 10)), ((1, 5), (2, 5)), ((0, 10), (10, 0))] true
#eval check "covertical endpoints, disjoint"
  [((0, 0), (2, 0)), ((2, 1), (4, 1)), ((2, -1), (4, -3))] false

/-- A deterministic linear congruential generator. -/
private meta def nextSeed (s : ℕ) : ℕ := (s * 1103515245 + 12345) % 2147483648

/-- `count` random instances of `n` segments with horizontal extent in `[1, len]` and vertical
change in `[-dy, dy]`. -/
private meta def randomCheck (label : String) (count n len dy : ℕ) (seed : ℕ) : IO Unit := do
  let mut s := seed
  let mut trues := 0
  let mut maxCost := 0
  for run' in [0:count] do
    let mut segs : List ((ℚ × ℚ) × (ℚ × ℚ)) := []
    for _ in [0:n] do
      s := nextSeed s
      let x₁ := s / 7 % 1000
      s := nextSeed s
      let y₁ := s / 7 % 1000
      s := nextSeed s
      let dx := 1 + s / 7 % len
      s := nextSeed s
      let y₂ : ℤ := y₁ + (s / 7 % (2 * dy + 1) : ℕ) - dy
      segs := segs ++ [(((x₁ : ℚ), (y₁ : ℚ)), (((x₁ + dx : ℕ) : ℚ), (y₂ : ℚ)))]
    let r := run segs
    unless r.ret == brute segs && r.time ≤ n * n + 24 * n do
      throw (IO.userError s!"{label}: instance {run'} disagrees with the brute force")
    if r.ret then trues := trues + 1
    maxCost := max maxCost r.time
  IO.println s!"{label}: {count} instances of {n} segments agree with the brute force \
    ({trues} intersecting); largest cost {maxCost}, bound {n * n + 24 * n}"

#eval randomCheck "long segments" 300 6 1000 1000 17
#eval randomCheck "short, nearly level segments" 300 25 60 15 29
#eval randomCheck "many short segments" 100 60 30 10 41

/-! Closed checks -/

/-- Over the reals, under CLRS's assumptions, the sweep's answer is exactly whether two distinct
segments meet. -/
example (S : Fin 5 → (ℝ × ℝ) × (ℝ × ℝ)) (hv : ∀ i, (S i).1.1 ≠ (S i).2.1)
    (h3 : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      segment ℝ (S i).1 (S i).2 ∩ segment ℝ (S j).1 (S j).2 ∩ segment ℝ (S k).1 (S k).2 = ∅) :
    (anySegmentsIntersect S).ret = true ↔
      ∃ i j, i ≠ j ∧ (segment ℝ (S i).1 (S i).2 ∩ segment ℝ (S j).1 (S j).2).Nonempty :=
  anySegmentsIntersect_ret_eq_true_iff S hv h3

example (S : Fin 5 → (ℝ × ℝ) × (ℝ × ℝ)) : (anySegmentsIntersect S).time ≤ 145 :=
  anySegmentsIntersect_time_le S

#print axioms anySegmentsIntersect_ret_eq_true_iff
#print axioms anySegmentsIntersect_time_le

end Cslib.Algorithms.Lean.Geometry
