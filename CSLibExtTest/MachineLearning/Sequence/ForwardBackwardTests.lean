/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.ForwardBackward
public meta import CSLibExt.MachineLearning.Sequence.ForwardBackward
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Matrix.Mul
public meta import Mathlib.Algebra.Order.Field.Rat

/-!
# Forward-backward tests

Executed fixtures: on 60 pseudo-random HMMs over `ℚ` (1 to 3 states, binary observations, random
positive weights, horizons `t + k` up to 5), for every time `t` and state `s` the tabulated
`forward t s * backward k t s` equals the brute-force sum over all paths through `s` at time `t`
(`stateMarg`, evaluated directly). The tabulated smoothing weights (`smoothedTab`) sum to one
and equal that sum divided by the brute-force likelihood. Each run throws on a disagreement.
Closed checks instantiate the theorems, including over noncommutative `2 × 2` matrix weights.
-/

namespace Cslib.MachineLearning.Sequence.HiddenMarkov

#eval do
  let mut s := 31
  for _ in [0:60] do
    s := (s * 1103515245 + 12345) % 2147483648
    let n := s / 7 % 3 + 1
    s := (s * 1103515245 + 12345) % 2147483648
    let T := s / 7 % 5
    let mut ws : Array ℚ := #[]
    for _ in [0:n + n * n + 2 * n + T + 1] do
      s := (s * 1103515245 + 12345) % 2147483648
      ws := ws.push ((s / 11 % 4 + 1 : ℕ) : ℚ)
    let hm : HMM (Fin n) Bool ℚ :=
      ⟨fun i => ws.getD i.val 0, fun i j => ws.getD (n + n * i.val + j.val) 0,
        fun i o => ws.getD (n + n * n + 2 * i.val + (if o then 1 else 0)) 0⟩
    let xs : ℕ → Bool := fun i => (ws.getD (n + n * n + 2 * n + i) 0) > 2
    for t in [0:T + 1] do
      let k := T - t
      let L := likelihood hm xs (t + k)
      let post := smoothedTab xs hm t k
      let total := (List.finRange n).foldl (fun acc i => acc + post[i]) 0
      unless total == 1 do throw (IO.userError s!"smoothing weights sum to {total}")
      for i in List.finRange n do
        let fb := (forwardTab xs hm t)[i] * (backwardTab xs hm k t)[i]
        let brute := stateMarg hm xs t k i
        unless fb == brute do throw (IO.userError s!"forward-backward {fb} ≠ brute {brute}")
        unless post[i] == brute / L do throw (IO.userError "smoothing weight mismatch")
  IO.println "60 random HMMs: forward·backward = brute-force state marginals; smoothing sums to 1"

/-! Closed checks -/

example (hm : HMM (Fin 3) Bool ℚ) (xs : ℕ → Bool) (s : Fin 3) :
    stateMarg hm xs 2 3 s = forward hm xs 2 s * backward hm xs 3 2 s :=
  stateMarg_eq hm xs 2 3 s

-- noncommutative weights: 2 × 2 matrices
example (hm : HMM (Fin 2) Bool (Matrix (Fin 2) (Fin 2) ℚ)) (xs : ℕ → Bool) (s : Fin 2) :
    stateMarg hm xs 1 2 s = forward hm xs 1 s * backward hm xs 2 1 s :=
  stateMarg_eq hm xs 1 2 s

example (hm : HMM (Fin 3) Bool ℚ) (hn : hm.Nonneg) (xs : ℕ → Bool) (s : Fin 3) :
    0 ≤ smoothed xs hm 2 3 s :=
  smoothed_nonneg xs hm hn 2 3 s

example (hm : HMM (Fin 3) Bool ℚ) (xs : ℕ → Bool) (hL : likelihood hm xs (2 + 3) ≠ 0) :
    ∑ s, smoothed xs hm 2 3 s = 1 :=
  sum_smoothed xs hm 2 3 hL

#print axioms stateMarg_eq
#print axioms sum_smoothed
#print axioms smoothedTab_get

end Cslib.MachineLearning.Sequence.HiddenMarkov
