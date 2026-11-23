/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.HMM.ProfileHMM
public meta import CSLibExt.Bioinformatics.HMM.ProfileHMM
public import Mathlib.Algebra.Order.Field.Rat
public meta import Mathlib.Algebra.Order.Field.Rat

/-!
# Profile HMM tests

`toy` is a Plan 7 profile HMM with `L = 2` columns over `Bool` (`IsPlan7`, nonnegative weights,
each transition row out of nodes `0` and `1` sums to one): column 1 prefers `true`, column 2
prefers `false`. Executed fixtures: for every binary sequence of length at most 4, `forward` equals
the brute-force sum of `pathProb` over `alignmentsOf x (columns 2)` and `viterbi` equals the
brute-force maximum. Closed checks: Laplace pseudocount estimates and the junk value of the
estimate without pseudocounts on an empty column; the Viterbi value of `[true, false]` is the weight
`0.9 · 0.9 · 0.8 · 0.8` of the path `M 1, M 2`, and the theorems instantiate.
-/

namespace Cslib.Bioinformatics.HMM

open Cslib.Algorithms.Lean ProfileHMM

/-- The toy profile's transitions out of node `0` (the begin state, type `M`) and node `1`; all
others are `0`. -/
def toyTrans : ℕ → ProfileState → ProfileState → ℚ
  | 0, .M, .M => 9 / 10
  | 0, .M, .D => 1 / 10
  | 1, .M, .M => 8 / 10
  | 1, .M, .I => 1 / 10
  | 1, .M, .D => 1 / 10
  | 1, .I, .M => 6 / 10
  | 1, .I, .I => 4 / 10
  | 1, .D, .M => 7 / 10
  | 1, .D, .D => 3 / 10
  | _, _, _ => 0

/-- A Plan 7 profile HMM with two columns over `Bool`. -/
def toy : ProfileHMM 2 Bool ℚ where
  trans := toyTrans
  stop _ := 1
  emitM k a := if k = 1 then (if a then 9 / 10 else 1 / 10) else (if a then 2 / 10 else 8 / 10)
  emitI _ _ := 1 / 2

/-- **Non-vacuity**: the toy profile satisfies Plan 7's restrictions. -/
theorem toy_isPlan7 : toy.IsPlan7 where
  no_DI k := by rcases k with _ | _ | k <;> rfl
  no_ID k := by rcases k with _ | _ | k <;> rfl
  no_I₀ s := by cases s <;> rfl
  no_I_last s := by cases s <;> rfl

/-- The toy profile has nonnegative weights. -/
theorem toy_nonneg : toy.Nonneg where
  trans k s t := by
    rcases k with _ | _ | k <;> cases s <;> cases t <;> norm_num [toy, toyTrans]
  emitM k a := by simp only [toy]; split_ifs <;> norm_num
  emitI _ _ := by norm_num [toy]

/-- The transition rows out of the begin node and node `1` sum to one. -/
example : (toyTrans 0 .M .M + toyTrans 0 .M .I + toyTrans 0 .M .D = 1) ∧
    (toyTrans 1 .M .M + toyTrans 1 .M .I + toyTrans 1 .M .D = 1) ∧
    (toyTrans 1 .I .M + toyTrans 1 .I .I + toyTrans 1 .I .D = 1) ∧
    (toyTrans 1 .D .M + toyTrans 1 .D .I + toyTrans 1 .D .D = 1) := by
  norm_num [toyTrans]

/-- All binary sequences of length at most `n`. -/
private def boolSeqs : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => [] :: ((boolSeqs n).flatMap fun s => [false :: s, true :: s]) |>.dedup

#eval do
  for x in boolSeqs 4 do
    let As : List (List (Option Bool × Option ℕ)) := alignmentsOf x (columns 2)
    let brute := (As.map toy.pathProb).sum
    unless toy.forward x == brute do throw (IO.userError s!"forward {x}")
    let bmax := (As.map toy.pathProb).foldl max 0
    unless toy.viterbi x == bmax do throw (IO.userError s!"viterbi {x}")
  IO.println "all sequences up to length 4: forward and Viterbi = brute force over paths"

/-- The best path for `[true, false]` is `M 1, M 2`: weight `0.9 · 0.9 · 0.8 · 0.8 · 1`. -/
example : toy.viterbi [true, false] = 81 / 100 * (64 / 100) := by decide +kernel

example : toy.pathProb [(some true, some 1), (some false, some 2)] = toy.viterbi [true, false] :=
  by decide +kernel

example (x : List Bool) {A : List (Option Bool × Option ℕ)}
    (hA : A ∈ alignmentsOf x (columns 2)) :
    toy.pathProb A ≤ toy.viterbi x :=
  pathProb_le_viterbi toy_nonneg hA

example (x : List Bool) : toy.forward x = ((alignmentsOf x (columns 2)).map toy.pathProb).sum :=
  toy.forward_eq_sum x

/-! ## Pseudocount emission estimates -/

/-- Laplace's rule on the column `[true, true, true]`: `true` gets `4/5`, `false` gets `1/5`. -/
example : pseudocountEmission [true, true, true] (fun _ => (1 : ℚ)) true = 4 / 5 ∧
    pseudocountEmission [true, true, true] (fun _ => (1 : ℚ)) false = 1 / 5 := by
  decide +kernel

example (col : List Bool) : ∑ a, pseudocountEmission col (fun _ => (1 : ℚ)) a = 1 :=
  sum_pseudocountEmission col fun _ => one_pos

/-- Boundary: with zero pseudocounts on an empty column, the estimate is the junk value
`0 / 0 = 0` for every residue, so the sum is `0`, not `1` (the positivity hypothesis is needed). -/
example : ∑ a, pseudocountEmission ([] : List Bool) (fun _ => (0 : ℚ)) a = 0 := by
  decide +kernel

end Cslib.Bioinformatics.HMM
