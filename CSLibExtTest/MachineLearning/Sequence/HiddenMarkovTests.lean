/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.HiddenMarkov
public meta import CSLibExt.MachineLearning.Sequence.HiddenMarkov
public import Mathlib.Algebra.Order.Field.Rat
public meta import Mathlib.Algebra.Order.Field.Rat

/-!
# Hidden Markov model tests

Executed fixtures: on 60 pseudo-random HMMs over `ℚ` (1 to 3 states, binary observations,
sequences of length 1 to 6, random nonnegative weights), `likelihoodTab` equals the brute-force
sum over all state paths (`likelihood`, evaluated directly). The Viterbi path's weight equals the
brute-force maximum over all paths and the largest tabulated Viterbi variable. Each run throws
on a disagreement. Closed checks instantiate the theorems.
-/

namespace Cslib.MachineLearning.Sequence.HiddenMarkov

#eval do
  let mut s := 23
  for _ in [0:60] do
    s := (s * 1103515245 + 12345) % 2147483648
    let n := s / 7 % 3 + 1
    s := (s * 1103515245 + 12345) % 2147483648
    let t := s / 7 % 6
    let mut ws : Array ℚ := #[]
    for _ in [0:n + n * n + 2 * n + t + 1] do
      s := (s * 1103515245 + 12345) % 2147483648
      ws := ws.push ((s / 11 % 5 : ℕ) : ℚ)
    let hm : HMM (Fin n) Bool ℚ :=
      ⟨fun i => ws.getD i.val 0, fun i j => ws.getD (n + n * i.val + j.val) 0,
        fun i o => ws.getD (n + n * n + 2 * i.val + (if o then 1 else 0)) 0⟩
    let xs : ℕ → Bool := fun i => (ws.getD (n + n * n + 2 * n + i) 0) > 2
    have : NeZero n := ⟨by omega⟩
    let brute := likelihood hm xs t
    unless likelihoodTab xs hm t == brute do
      throw (IO.userError s!"likelihood {likelihoodTab xs hm t} ≠ brute force {brute}")
    let best := (Finset.univ : Finset (Fin (t + 1) → Fin n)).sup' Finset.univ_nonempty
      (pathProb hm xs t)
    let vp := pathProb hm xs t (viterbiPath xs hm t)
    let vmax := (Finset.univ : Finset (Fin n)).sup' Finset.univ_nonempty
      fun i => (viterbiTab xs hm t)[i]
    unless vp == best && vmax == best do
      throw (IO.userError s!"Viterbi {vp} / {vmax} ≠ max {best}")
  IO.println "60 random HMMs: forward = brute-force likelihood; Viterbi path = brute-force max"

/-! Closed checks -/

example (hm : HMM (Fin 3) Bool ℚ) (xs : ℕ → Bool) :
    likelihoodTab xs hm 4 = ∑ z : Fin 5 → Fin 3, pathProb hm xs 4 z :=
  likelihoodTab_eq xs hm 4

example (hm : HMM (Fin 3) Bool ℚ) (hn : hm.Nonneg) (xs : ℕ → Bool) (z : Fin 5 → Fin 3) :
    pathProb hm xs 4 z ≤ pathProb hm xs 4 (viterbiPath xs hm 4) :=
  pathProb_le_viterbiPath xs hm hn 4 z

#print axioms likelihood_eq_sum_forward
#print axioms pathProb_le_viterbiPath
#print axioms sup'_viterbi_eq

end Cslib.MachineLearning.Sequence.HiddenMarkov
