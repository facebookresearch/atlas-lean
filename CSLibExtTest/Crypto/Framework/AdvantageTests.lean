/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Advantage

/-!
# Tests for the advantage vocabulary

* Point masses and the fair coin have the expected success probabilities and advantages.
* A perfect guesser in `bitGame` has guessing advantage `1/2` and distinguishing advantage `1`.
* The hybrid lemmas on a sequence of point masses that switches from `0` to `1` at index `3`:
  the end-to-end advantage `1` is split as `1/5` per uniformly chosen step.
* The difference lemma on a uniform `Fin 4`: two outcomes differing only on `ω = 1` have advantage
  `1/4`, bounded by `Pr[ω = 1] = 1/4`.
* Statistical distance equals advantage on `Bool`.
-/

@[expose] public section

namespace Cslib.Crypto.FrameworkTests.Advantage

open Cslib.Crypto.Framework
open scoped Cslib.Probability.PMF

example : winProb (PMF.pure true) = 1 := by simp

example : advantage (PMF.pure true) (PMF.pure false) = 1 := by simp [advantage]

example : guessAdvantage fairCoin = 0 := by simp [guessAdvantage]

example : guessAdvantage (PMF.pure true) = 1 / 2 := by norm_num [guessAdvantage]

/-- A perfect guesser: the experiment for bit `b` outputs `b`. -/
example : guessAdvantage (bitGame fun b => PMF.pure b) = 1 / 2 := by
  rw [guessAdvantage_bitGame]
  norm_num [advantage]

/-- A blind guesser: the experiment outputs `true` whatever the bit. -/
example : guessAdvantage (bitGame fun _ => PMF.pure true) = 0 := by
  rw [guessAdvantage_bitGame]
  simp

/-- Hybrids switching from `0` to `1` at index `3`. -/
noncomputable def H (i : ℕ) : PMF Bool := PMF.pure (decide (3 ≤ i))

example : advantage (H 0) (H 5) = 1 := by norm_num [H, advantage]

example : advantage (H 0) (H 5) ≤ ∑ i ∈ Finset.range 5, advantage (H i) (H (i + 1)) :=
  advantage_le_sum H 5

/-- Picking the hybrid index uniformly among `5` gives exactly `1/5` of the advantage. -/
example : advantage ((Cslib.Probability.PMF.uniformOfFintype (Fin 5)).bind fun i => H i)
    ((Cslib.Probability.PMF.uniformOfFintype (Fin 5)).bind fun i => H (i + 1)) = 1 / 5 := by
  rw [advantage_hybrid_uniform]
  norm_num [H, advantage]

/-- Two outcomes on a uniform `Fin 4` that differ only when `ω = 1`. -/
example : advantage
    ((Cslib.Probability.PMF.uniformOfFintype (Fin 4)).map fun ω => decide (ω = 0 ∨ ω = 1))
    ((Cslib.Probability.PMF.uniformOfFintype (Fin 4)).map fun ω => decide (ω = 0)) ≤ 1 / 4 := by
  refine (advantage_le_winProb_of_eq_of_not_bad _ _ _ (fun ω => decide (ω = 1)) ?_).trans ?_
  · decide
  · rw [winProb_map_uniform]
    have : (Finset.univ.filter fun ω : Fin 4 => decide (ω = 1) = true).card = 1 := by decide
    rw [this]
    norm_num

/-- The bound of the difference lemma is attained in that example. -/
example : advantage
    ((Cslib.Probability.PMF.uniformOfFintype (Fin 4)).map fun ω => decide (ω = 0 ∨ ω = 1))
    ((Cslib.Probability.PMF.uniformOfFintype (Fin 4)).map fun ω => decide (ω = 0)) = 1 / 4 := by
  rw [advantage, winProb_map_uniform, winProb_map_uniform]
  have h1 : (Finset.univ.filter fun ω : Fin 4 => decide (ω = 0 ∨ ω = 1) = true).card = 2 := by
    decide
  have h2 : (Finset.univ.filter fun ω : Fin 4 => decide (ω = 0) = true).card = 1 := by decide
  rw [h1, h2]
  norm_num

example : dist (PMF.pure true) (PMF.pure false) = 1 := by
  rw [← advantage_eq_dist]
  simp [advantage]

end Cslib.Crypto.FrameworkTests.Advantage
