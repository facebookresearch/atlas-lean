/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.ForwardBackward
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring

/-!
# Hidden Markov models: posterior decoding

Posterior decoding (Durbin, Eddy, Krogh and Mitchison, *Biological Sequence Analysis*, 1998,
section 3.2; Rabiner 1989, section III-B) picks, at each time `t ≤ T`, a state of largest
posterior probability `P(z t = s | x 0, …, x T)`. The posteriors are the forward-backward
smoothing weights `smoothed x g t (T - t) s` of `Sequence/ForwardBackward.lean`, which sum to
one at each time when the likelihood is nonzero (`sum_smoothed`) and are nonnegative for
nonnegative weights (`smoothed_nonneg`).

Unlike the Viterbi path, which maximizes the probability of the whole path, the posterior path
maximizes the expected number of correctly decoded states: for a state path `w` drawn from the
posterior `pathProb w / likelihood`, the expected number of times `t ≤ T` with `w t = z t` is
`∑ t, smoothed x g t (T - t) (z t)` (`expectedCorrect_eq_sum_smoothed`), and the posterior path
maximizes this sum (`expectedCorrect_le_posteriorPath`). The two decodings differ in general:
the test file has an HMM whose posterior path is not a Viterbi path and has weight zero.

## Main results

* `posteriorPath`: posterior decoding on `Fin n` states; `smoothed_le_posteriorPath`: it
  picks a state of largest posterior at each time.
* `smoothed_eq_sum_pathProb`: the posterior as a sum over paths.
* `expectedCorrect_eq_sum_smoothed`: the posterior expected number of correctly decoded states
  of a path `z` is the sum over time of the posteriors of `z t`.
* `expectedCorrect_le_posteriorPath`: **posterior decoding maximizes the expected number of
  correctly decoded states**.

## References

* R. Durbin, S. R. Eddy, A. Krogh and G. Mitchison, *Biological Sequence Analysis*, Cambridge
  University Press, 1998, section 3.2.
* L. R. Rabiner, *A tutorial on hidden Markov models and selected applications in speech
  recognition*, Proc. IEEE 77 (1989), 257–286.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Sequence.HiddenMarkov

variable {O K : Type*} [Semifield K] [LinearOrder K] {n : ℕ}
  (x : ℕ → O) (g : HMM (Fin n) O K)

/-- **Posterior decoding**: at each time `t ≤ T`, a state of largest posterior
`smoothed x g t (T - t)` (the first one, via `argmaxFin`). -/
def posteriorPath [NeZero n] (T : ℕ) : Fin (T + 1) → Fin n :=
  fun t => argmaxFin fun s => smoothed x g t (T - t) s

/-- The posterior path picks a state of largest posterior at each time. -/
theorem smoothed_le_posteriorPath [NeZero n] (T : ℕ) (t : Fin (T + 1)) (s : Fin n) :
    smoothed x g t (T - t) s ≤ smoothed x g t (T - t) (posteriorPath x g T t) :=
  le_argmaxFin _ s

omit [LinearOrder K] in
/-- The posterior of state `s` at time `t ≤ T`, as a sum over the paths of length `T + 1`: the
total weight of the paths through `s` at time `t` over the likelihood. -/
theorem smoothed_eq_sum_pathProb (T : ℕ) (t : Fin (T + 1)) (s : Fin n) :
    smoothed x g t (T - t) s =
      (∑ w : Fin (T + 1) → Fin n, if w t = s then pathProb g x T w else 0) /
        likelihood g x T := by
  rw [smoothed_eq]
  obtain ⟨t, ht⟩ := t
  have hk : t + (T - t) = T := by omega
  generalize T - t = k at hk ⊢
  subst hk
  rfl

/-- The posterior expected number of correctly decoded states of a path `z`: the sum over all
state paths `w` of `pathProb w / likelihood` times the number of times `t ≤ T` with
`w t = z t`. When the weights are probabilities and the likelihood is positive, this is the
expectation under the posterior law of the path; for likelihood `0` it is `0` (`x / 0 = 0`), as
is every posterior `smoothed`. -/
def expectedCorrect (T : ℕ) (z : Fin (T + 1) → Fin n) : K :=
  ∑ w : Fin (T + 1) → Fin n,
    pathProb g x T w / likelihood g x T * ((Finset.univ.filter fun t => w t = z t).card : K)

/-- **The expected number of correct states is a sum of posteriors**: for every path `z`, the
posterior expected number of times `t ≤ T` with `w t = z t` is the sum over `t` of the posterior
of `z t` at time `t`. -/
theorem expectedCorrect_eq_sum_smoothed (T : ℕ) (z : Fin (T + 1) → Fin n) :
    expectedCorrect x g T z = ∑ t : Fin (T + 1), smoothed x g t (T - t) (z t) := by
  simp only [smoothed_eq_sum_pathProb, expectedCorrect, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun w _ => ?_
  split_ifs <;> ring

/-- **Posterior decoding maximizes the expected number of correctly decoded states.** -/
theorem expectedCorrect_le_posteriorPath [NeZero n] (T : ℕ) (z : Fin (T + 1) → Fin n) :
    expectedCorrect x g T z ≤ expectedCorrect x g T (posteriorPath x g T) := by
  rw [expectedCorrect_eq_sum_smoothed, expectedCorrect_eq_sum_smoothed]
  exact Finset.sum_le_sum fun t _ => smoothed_le_posteriorPath x g T t (z t)

end Cslib.MachineLearning.Sequence.HiddenMarkov
