/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.WeightedMajority
public meta import CSLibExt.MachineLearning.WeightedMajority
public import Mathlib.Basic.Real.Basic

/-!
# Weighted majority tests

Executed fixtures: 200 pseudo-random runs of 40 rounds with 8 experts of varying reliability
(expert 0 perfect in half of the runs) check `4 ^ M ≤ n 3 ^ M 2 ^ m` (penalty `1/2`) and
`(3/4) ^ m 2 ^ M ≤ n (7/4) ^ M` (penalty `3/4`) against every expert; with a perfect expert
among 8 the penalty-`1/2` algorithm never makes more than `log_{4/3} 8 < 7.3` mistakes, and the
worst observed count is printed. Each run throws on a violation. Closed checks instantiate the
theorems, including the general bound over `ℝ`.
-/

namespace Cslib.MachineLearning.WeightedMajority

#eval do
  let n := 8
  let mut s := 23
  let mut worst := 0
  for run in [0:200] do
    let mut rs : List (Round n) := []
    for _ in [0:40] do
      s := (s * 1103515245 + 12345) % 2147483648
      let y := s / 3 % 2 == 0
      let mut bits : List Bool := []
      for i in [0:n] do
        s := (s * 1103515245 + 12345) % 2147483648
        -- expert i is wrong with probability about i / 10; in even runs expert 0 is perfect
        let wrong := (s / 5 % 10) < i || (i == 0 && run % 2 == 1 && s / 7 % 10 == 0)
        bits := bits ++ [if wrong then !y else y]
      rs := rs ++ [((fun (j : Fin n) => bits.getD j.val false), y)]
    let M := mistakes (1 / 2 : ℚ) rs (fun _ => 1)
    let M' := mistakes (3 / 4 : ℚ) rs (fun _ => 1)
    for i in List.finRange n do
      unless 4 ^ M ≤ n * 3 ^ M * 2 ^ expertMistakes i rs do
        throw (IO.userError s!"bound fails in run {run} for expert {i}")
      unless (3 / 4 : ℚ) ^ expertMistakes i rs * 2 ^ M' ≤ n * (7 / 4) ^ M' do
        throw (IO.userError s!"penalty-3/4 bound fails in run {run} for expert {i}")
    if run % 2 == 0 then
      unless 4 ^ M ≤ n * 3 ^ M do throw (IO.userError s!"perfect-expert bound fails in run {run}")
      worst := max worst M
  IO.println s!"200 runs, 8 experts, 40 rounds: 4^M ≤ n 3^M 2^m (penalty 1/2) and \
    (3/4)^m 2^M ≤ n (7/4)^M (penalty 3/4) for every expert; with a perfect expert at most \
    {worst} mistakes (bound: log_(4/3) 8 < 7.3)"

/-! Closed checks -/

example (rs : List (Round 8)) (i : Fin 8) :
    4 ^ mistakes (1 / 2 : ℚ) rs (fun _ => 1) ≤
      8 * 3 ^ mistakes (1 / 2 : ℚ) rs (fun _ => 1) * 2 ^ expertMistakes i rs :=
  mistake_bound_nat rs i

/-- The general bound over the reals, with Hazan's penalty `1 - ε` at `ε = 1/4`. -/
example (rs : List (Round 8)) (i : Fin 8) :
    (3 / 4 : ℝ) ^ expertMistakes i rs * (2 : ℝ) ^ mistakes (3 / 4 : ℝ) rs (fun _ => 1) ≤
      8 * (1 + 3 / 4 : ℝ) ^ mistakes (3 / 4 : ℝ) rs (fun _ => 1) := by
  have := mistake_bound_general (K := ℝ) (β := 3 / 4) (by norm_num) (by norm_num) rs i
  simpa using this

#print axioms mistake_bound
#print axioms mistake_bound_nat
#print axioms mistake_bound_general
#print axioms total_update_of_mistake

end Cslib.MachineLearning.WeightedMajority
