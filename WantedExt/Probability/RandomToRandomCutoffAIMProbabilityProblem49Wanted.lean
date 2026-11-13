/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Cutoff for the random-to-random shuffle (AimPL Markov chain mixing times, Conjecture 5.1)

AimPL, Markov chain mixing times, Conjecture 5.1 (E. Nestoridi): the random-to-random card shuffle
on `S_n` has cutoff at `(3n/4) log n`. The list records Subag's lower bound `(3/4 - ε) n log n` and
upper bounds `2 n log n` and `(3/2) n log n`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Order.Filter.AtTopBot.Basic
public import WantedExt.Probability.SymmetricGroupRandomWalkShared

@[expose] public section

namespace MathlibExt.Probability.RandomToRandomCutoffAIMProbabilityProblem49Wanted

/-!
Source: AimPL: Markov chain mixing times, Conjecture 5.1 (E. Nestoridi),
http://aimpl.org/markovmixing/5/. UnsolvedMath record UM-20002607 (`AIM-PROBABILITY-0049`), dataset
ulamai/UnsolvedMath v1.8.0.

One step picks a uniform position `i` and an independent uniform position `j` and moves the card at
`i` to position `j` (`n²` equally likely moves). A deck is a permutation `d` of positions (`d p` is
the card at `p`); the move is `d ↦ d * s` with `s = (cycleRange i)⁻¹ * cycleRange j` (move the card
at `i` to the top, then the top card to `j`), checked against list remove-and-insert for `n ≤ 6`.
The distance is measured from the identity deck, which by translation invariance equals the
worst-case distance. Cutoff at `t_n = (3/4) n log n` is the multiplicative form: distance `→ 0` at
`⌈(1 + η) t_n⌉` and `→ 1` at `⌊(1 - η) t_n⌋`.
-/

open Filter Topology MathlibExt.Probability.SymmetricGroupRandomWalkShared

/-- The step law of the random-to-random shuffle of `n` cards: the card at a uniform position `i`
is removed and reinserted at an independent uniform position `j`. On decks `d : Fin n → cards`
(`d p` is the card at position `p`) this is `d ↦ d ∘ s` with `s = (cycleRange i)⁻¹ * cycleRange j`
(move the card at `i` to the top, then the top card to `j`). -/
noncomputable def randomToRandomStep (n : ℕ) : Equiv.Perm (Fin n) → ℝ :=
  pairStepLaw fun ij => (Fin.cycleRange ij.1)⁻¹ * Fin.cycleRange ij.2

/-- AimPL Markov chain mixing times, Conjecture 5.1, as a claim: the random-to-random shuffle has
total variation cutoff at `t_n = (3/4) n log n`, i.e. for every `η ∈ (0, 1)` the distance to
uniformity tends to `0` at time `⌈(1 + η) t_n⌉` and to `1` at time `⌊(1 - η) t_n⌋`. -/
def randomToRandomCutoff : Prop :=
  ∀ η : ℝ, 0 < η → η < 1 →
    Tendsto (fun n : ℕ => walkDistToUniform (randomToRandomStep n)
      ⌈(1 + η) * (3 / 4 * n * Real.log n)⌉₊) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => walkDistToUniform (randomToRandomStep n)
      ⌊(1 - η) * (3 / 4 * n * Real.log n)⌋₊) atTop (𝓝 1)

/--
Resolved true: Bernstein and Nestoridi proved, with Subag's lower bound, that the random-to-random
shuffle has total variation cutoff at `(3/4) n log n - (1/4) n log log n` with window of order `n`,
hence cutoff at `(3/4) n log n`. Source: AimPL: Markov chain mixing times, Conjecture 5.1 (E.
Nestoridi), http://aimpl.org/markovmixing/5/; resolution: M. Bernstein and E. Nestoridi, Cutoff for
random to random card shuffle, Ann. Probab. 47 (2019), no. 5, 3303-3320, arXiv:1703.06210, abstract
and Theorem 1 (upper bound e^{-c} at time (3/4) n log n - (1/4) n log log n + c n): combined with
Subag's lower bound (E. Subag, Electron. J. Probab. 18 (2013), 1-20) the random to random shuffle
has total variation cutoff at (3/4) n log n - (1/4) n log log n with window of order n, answering
Diaconis's conjecture of cutoff at (3/4) n log n, https://doi.org/10.1214/19-AOP1340.
-/
public theorem_wanted randomToRandomCutoff_holds : randomToRandomCutoff

end MathlibExt.Probability.RandomToRandomCutoffAIMProbabilityProblem49Wanted
