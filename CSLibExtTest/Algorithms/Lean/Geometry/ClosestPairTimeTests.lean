/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Geometry.ClosestPairTime
public meta import CSLibExt.Algorithms.Lean.Geometry.ClosestPair
public meta import Mathlib.Algebra.Order.Field.Rat
public meta import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Field.Rat

/-!
# Closest-pair cost tests

The bound is proved over `ℝ`; the executed fixtures run the same algorithm over `ℚ` and compare
the number of distances with `7 n ⌈log₂ n⌉ + n` and with the brute force's `n (n - 1) / 2`, on
inputs that put many points in the strip: a vertical line of points (every point is in every
strip), a dense grid, and a pseudo-random set. Closed examples instantiate the theorems over `ℝ`.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Geometry

private meta def check (label : String) (ps : List (ℚ × ℚ)) : IO Unit := do
  let n := ps.length
  let r := closestPair ps
  let bound := 7 * n * Nat.clog 2 n + n
  unless r.time ≤ bound && r.ret == (bruteMin ps).ret do
    throw (IO.userError s!"{label}: {r.time} distances, bound {bound}")
  IO.println s!"{label}: {r.time} distances ≤ {bound} (brute force {n * (n - 1) / 2}), {r.ret}"

#eval check "64 points on a vertical line" ((List.range 64).map fun i => (0, (i : ℚ)))
#eval check "8 x 8 grid" ((List.range 64).map fun i => (((i / 8 : ℕ) : ℚ), ((i % 8 : ℕ) : ℚ)))
#eval check "128 scattered points"
  ((List.range 128).map fun i => (((i * 37 + 11) % 211 : ℕ), ((i * 53 + 7) % 199 : ℕ)))

example (ps : List (ℝ × ℝ)) :
    (closestPair ps).time ≤ 7 * ps.length * Nat.clog 2 ps.length + ps.length :=
  closestPair_time_le ps

example (δ xmid : ℝ) (Y : List Tagged) (hs : Y.Pairwise fun a b => a.1.2 ≤ b.1.2)
    (hp : Y.Pairwise (SameSideFar δ)) (hst : ∀ a ∈ Y, InStrip δ xmid a) :
    (stripScan δ (Y.map Prod.fst)).time ≤ 7 * Y.length :=
  stripScan_time_le δ xmid Y hs hp hst

#print axioms closestPair_time_le
#print axioms closestRec_time_le
#print axioms stripScan_time_le
#print axioms length_le_seven

end Cslib.Algorithms.Lean.Geometry
