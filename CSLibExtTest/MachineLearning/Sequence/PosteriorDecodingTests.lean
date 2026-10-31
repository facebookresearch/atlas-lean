/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.PosteriorDecoding
public meta import CSLibExt.MachineLearning.Sequence.PosteriorDecoding
public import Mathlib.Algebra.Order.Field.Rat
public meta import Mathlib.Algebra.Order.Field.Rat

/-!
# Posterior decoding tests

The counterexample `cex`: three states, one observation symbol (all emission weights `1`),
initial weights `(1/2, 1/4, 1/4)`, state `0` moves to `1` or `2` with weight `1/2` each, states
`1` and `2` move to `0`. Over two time steps the posteriors are `(1/2, 1/4, 1/4)` at time `0` and
`(1/2, 1/4, 1/4)` at time `1`, so posterior decoding returns the path `0, 0`, whose weight is
`0` (no `0 → 0` transition), while the Viterbi path has weight `1/4`: **posterior decoding and
Viterbi differ**, and the posterior path need not be a possible path. Posterior decoding still has
the larger expected number of correctly decoded states (`1` against `3/4`).
-/

namespace Cslib.MachineLearning.Sequence.HiddenMarkov

/-- The counterexample HMM. -/
def cex : HMM (Fin 3) Unit ℚ where
  init := ![1 / 2, 1 / 4, 1 / 4]
  trans := ![![0, 1 / 2, 1 / 2], ![1, 0, 0], ![1, 0, 0]]
  emit _ _ := 1

/-- The (only) observation sequence. -/
def obs : ℕ → Unit := fun _ => ()

/-- The posterior path is `0, 0`. -/
example : posteriorPath obs cex 1 = ![0, 0] := by decide +kernel

/-- The posterior path has weight `0`. -/
example : pathProb cex obs 1 (posteriorPath obs cex 1) = 0 := by decide +kernel

/-- The Viterbi path (first maximizer) is `1, 0`. -/
example : viterbiPath obs cex 1 = ![1, 0] := by decide +kernel

/-- The Viterbi path has weight `1/4`. -/
example : pathProb cex obs 1 (viterbiPath obs cex 1) = 1 / 4 := by decide +kernel

/-- **Posterior decoding differs from Viterbi.** -/
example : posteriorPath obs cex 1 ≠ viterbiPath obs cex 1 := by decide +kernel

/-- The posteriors at each time sum to one (`sum_smoothed`, likelihood `1`). -/
example (t : Fin 2) : ∑ s, smoothed obs cex t (1 - t) s = 1 := by
  refine sum_smoothed obs cex t (1 - t) ?_
  rw [show (t : ℕ) + (1 - t) = 1 by omega, likelihood_eq_sum_forward]
  decide +kernel

/-- Expected numbers of correctly decoded states: `1` for the posterior path, `3/4` for the
Viterbi path. -/
example : expectedCorrect obs cex 1 (posteriorPath obs cex 1) = 1 ∧
    expectedCorrect obs cex 1 (viterbiPath obs cex 1) = 3 / 4 := by
  rw [show posteriorPath obs cex 1 = ![0, 0] by decide +kernel,
    show viterbiPath obs cex 1 = ![1, 0] by decide +kernel]
  simp only [expectedCorrect_eq_sum_smoothed, smoothed,
    Nat.add_sub_cancel' (Nat.le_of_lt_succ (Fin.is_lt _)), likelihood_eq_sum_forward]
  decide +kernel

/-- `expectedCorrect_le_posteriorPath` instantiated. -/
example (z : Fin 2 → Fin 3) :
    expectedCorrect obs cex 1 z ≤ expectedCorrect obs cex 1 (posteriorPath obs cex 1) :=
  expectedCorrect_le_posteriorPath obs cex 1 z

/-- Boundary: with likelihood `0` (an impossible observation), all posteriors are `0`, so
`expectedCorrect` is `0` (the `x / 0 = 0` convention), not an expectation. -/
example : expectedCorrect obs
    { init := fun _ => 0, trans := fun _ _ => 0, emit := fun _ _ => 1 : HMM (Fin 2) Unit ℚ } 1
    ![0, 1] = 0 := by
  simp only [expectedCorrect_eq_sum_smoothed, smoothed,
    Nat.add_sub_cancel' (Nat.le_of_lt_succ (Fin.is_lt _)), likelihood_eq_sum_forward]
  decide +kernel

/-! ## Executed fixtures -/

-- On pseudo-random HMMs, `expectedCorrect` (brute force over paths) equals the sum of the
-- posteriors, and the posterior path maximizes it over all paths.
#eval do
  let mut s := 41
  for _ in [0:20] do
    s := (s * 1103515245 + 12345) % 2147483648
    let ws : Array ℚ := (List.range 30).toArray.map fun i =>
      (((s / (i + 7)) % 5 : ℕ) : ℚ)
    let g : HMM (Fin 2) Bool ℚ :=
      { init := fun a => ws[a.val]!, trans := fun a b => ws[2 + 2 * a.val + b.val]!,
        emit := fun a o => ws[6 + 2 * a.val + (if o then 1 else 0)]! + 1 }
    let x : ℕ → Bool := fun t => (s / (t + 3)) % 2 == 0
    let T := 2
    let paths : List (Fin (T + 1) → Fin 2) :=
      (List.finRange 8).map fun (k : Fin 8) (t : Fin (T + 1)) => ⟨(k.val / 2 ^ t.val) % 2, by omega⟩
    let best := expectedCorrect x g T (posteriorPath x g T)
    for z in paths do
      let e := expectedCorrect x g T z
      let r := ∑ t : Fin (T + 1), smoothed x g t (T - t) (z t)
      unless e == r do throw (IO.userError s!"identity fails: {e} vs {r}")
      unless e ≤ best do throw (IO.userError s!"posterior path not optimal: {best} < {e}")
  IO.println "20 random HMMs: expectedCorrect = sum of posteriors; posterior path is optimal"

end Cslib.MachineLearning.Sequence.HiddenMarkov
