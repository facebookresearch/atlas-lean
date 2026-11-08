/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Online.SkiRental
public meta import CSLibExt.Algorithms.Lean.Online.SkiRental
public import Mathlib.Algebra.Order.Field.Rat
public meta import Mathlib.Algebra.Order.Field.Rat

/-!
# Ski rental tests

Executed fixtures: for every buying price `B ≤ 20`, the worst ratio `cost / opt` of each
strategy over seasons of up to `4 B` days is computed exactly; the break-even strategy's worst
ratio is `(2 B - 1) / B`, and no strategy (buying on any day up to `4 B`, or never) does better,
matching `cost_breakEven_le` and `exists_cost_ge`. Each run throws on a mismatch. Closed checks
instantiate the theorems.
-/

namespace Cslib.Algorithms.Lean.Online.SkiRental

/-- The worst ratio `cost / opt` of a strategy over seasons of `1, …, D` days. -/
private meta def worst (B D : ℕ) (s : Strategy) : ℚ :=
  (List.range' 1 D).foldl (fun m d => max m ((cost B s d : ℚ) / (opt B d : ℚ))) 0

private meta def checkB (B : ℕ) : IO Unit := do
  let D := 4 * B
  let target : ℚ := (2 * (B : ℚ) - 1) / (B : ℚ)
  unless worst B D (breakEven B) == target do
    throw (IO.userError s!"B = {B}: break-even worst ratio {worst B D (breakEven B)}")
  let strategies : List Strategy := none :: (List.range' 1 D).map some
  let best := strategies.foldl (fun m s => min m (worst B D s)) (worst B D none)
  unless best == target do
    throw (IO.userError s!"B = {B}: best deterministic worst ratio {best}, expected {target}")

#eval do
  for B in List.range' 1 20 do checkB B
  IO.println "B = 1..20: break-even's worst ratio is (2B - 1)/B and no deterministic strategy \
    does better"

#eval IO.println s!"B = 10: break-even worst ratio {worst 10 40 (breakEven 10)}, renting forever \
  {worst 10 40 none}, buying on day 1 {worst 10 40 (some 1)}"

/-! Closed checks -/

example (d : ℕ) : cost 10 (breakEven 10) d ≤ 2 * opt 10 d :=
  cost_breakEven_le_two_mul (by decide : 1 ≤ 10) d

example (s : Strategy) : ∃ d, 19 * opt 10 d ≤ 10 * cost 10 s d :=
  exists_cost_ge (by decide : 1 ≤ 10) s

#print axioms cost_breakEven_le
#print axioms cost_breakEven_le_two_mul
#print axioms exists_cost_ge
#print axioms opt_le_cost

end Cslib.Algorithms.Lean.Online.SkiRental
