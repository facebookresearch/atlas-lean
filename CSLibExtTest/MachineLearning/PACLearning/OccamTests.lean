/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.Occam

/-!
# Occam bound tests

Non-vacuity checks on the instance space `Bool` with the point mass at `(true, true)`: the
hypothesis `not` has error `1`, so it agrees with `m + 1` examples with probability `0`; the
bridge from `trueError` to CSLib's `error`; the realizable-family membership of a labelled
distribution; and CSLib's `IsPACLearnable` for the one-element class `{id}`.
-/

namespace Cslib.MachineLearning.PACLearning

open MeasureTheory
open scoped ENNReal

example : error (Measure.dirac ((true, true) : Bool × Bool)) not = 1 := by
  simp [error]

-- `not` disagrees with every example drawn from the point mass, so it survives no nonempty sample
example (m : ℕ) :
    Measure.pi (fun _ : Fin (m + 1) => Measure.dirac ((true, true) : Bool × Bool))
      {S : LabeledSample Bool Bool (m + 1) | ∀ i, not (S i).1 = (S i).2} = 0 := by
  rw [pi_consistent_eq _ _ MeasurableSet.of_discrete (m + 1)]
  simp [error]

-- the bridge: `trueError` against `id` under a point mass is CSLib's error of the pushforward
example (h : Bool → Bool) :
    trueError (Measure.dirac true) id h = error ((Measure.dirac true).map fun x => (x, id x)) h :=
  trueError_eq_error_map _ measurable_id h MeasurableSet.of_discrete

-- labelling any distribution by `id` is realizable for `{id}`
example (μ : Measure Bool) :
    μ.map (fun x => (x, id x)) ∈ realizableFamily ({id} : Set (Bool → Bool)) :=
  map_graph_mem_realizableFamily μ measurable_id rfl MeasurableSet.of_discrete (by simp [trueError])

-- Corollary 3.2 instance: the one-element class `{id}` is PAC learnable
example : IsPACLearnable ((({id} : Finset (Bool → Bool))) : ConceptClass Bool Bool)
    (realizableFamily ((({id} : Finset (Bool → Bool))) : ConceptClass Bool Bool)) :=
  isPACLearnable_of_finite _ (Finset.singleton_nonempty _) fun _ _ => MeasurableSet.of_discrete

end Cslib.MachineLearning.PACLearning
