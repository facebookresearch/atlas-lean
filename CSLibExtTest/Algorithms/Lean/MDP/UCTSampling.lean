/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.MDP.UCTSampling
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-! # UCT with an atomless reward law -/

namespace Cslib.Algorithms.Lean.MarkovDecision.UCT.Tests

open MeasureTheory
open scoped unitInterval

private def uniformReward : Sampler Unit Unit I where
  actions _ := {()}
  nonempty _ := Finset.singleton_nonempty _
  sample _ _ u := ((), u.val)
  measurable_sample := measurable_const.prodMk (measurable_subtype_coe.comp measurable_snd.snd)
  measurable_available _ := by simp

-- One self-transition yields the innovation itself as the episode return; the pushforward of
-- the actual one-step episode law is Lebesgue measure restricted to [0,1].
example : Measure.map Prod.fst
    (uniformReward.rolloutLaw 1 1 volume 1 () : Measure (ℝ × Table Unit Unit)) =
    volume.restrict (Set.Icc (0 : ℝ) 1) := by
  have hm := uniformReward.rollout_measurable (c := 1) (γ := 1) QueryMeasurable.empty_table 1 0
    (measurable_const (a := ())) (measurable_id (α := Fin 1 → I))
  have hme : Measurable (uniformReward.rollout 1 1 empty 1 0 ()) := hm.1.prodMk hm.2.measurable
  rw [Sampler.rolloutLaw, ProbabilityMeasure.coe_mk, Measure.map_map measurable_fst hme]
  convert (unitInterval.measurePreserving_coe.comp
    (measurePreserving_eval (fun _ : Fin 1 => (volume : Measure I)) 0)).map_eq using 2
  funext w
  simp [Sampler.rollout, uniformReward, Function.eval]

-- Read the learned root-action mean after one episode, rather than the simulator oracle.
-- Its entire distribution is uniform, not just its expectation or support.
example : Measure.map (fun T : Table Unit Unit => (T 0 () ()).mean)
    (uniformReward.runLaw 1 1 volume 1 1 () : Measure (Table Unit Unit)) =
    volume.restrict (Set.Icc (0 : ℝ) 1) := by
  have ht := uniformReward.run_queryMeasurable (c := 1) (γ := 1) 1 1 () measurable_id
  have hm : Measurable (fun T : Table Unit Unit => (T 0 () ()).mean) := by
    obtain ⟨hc, hr⟩ := Stats.measurable_iff.mp ((measurable_pi_apply ()).comp
      ((measurable_pi_apply ()).comp (measurable_pi_apply 0)) :
      Measurable (fun T : Table Unit Unit => T 0 () ()))
    apply hr.div
    fun_prop
  have hme : Measurable (uniformReward.run 1 1 1 () 1) := ht.measurable
  rw [Sampler.runLaw, ProbabilityMeasure.coe_mk, Measure.map_map hm hme]
  have hrow := measurePreserving_eval (fun _ : Fin 1 => Measure.pi
    (fun _ : Fin 1 => (volume : Measure I))) 0
  have hstep := measurePreserving_eval (fun _ : Fin 1 => (volume : Measure I)) 0
  convert (unitInterval.measurePreserving_coe.comp (hstep.comp hrow)).map_eq using 2
  funext w
  simp [Function.comp_def, Sampler.run, Sampler.rollout, uniformReward, Stats.mean,
    record, Stats.observe, empty, Function.eval, Fin.last]

-- The first innovation sets the successor as well as the reward. A different second draw at
-- that successor gives a different suffix. Across episodes, both child locations are retained.
private noncomputable def branching : Sampler Bool Unit Bool where
  actions _ := {()}
  nonempty _ := Finset.singleton_nonempty _
  sample s _ b := (b, if s then 1 / 2 else if b then 1 / 4 else 0)
  measurable_sample := Measurable.of_discrete
  measurable_available _ := by simp

example : let w : Fin 2 → Fin 2 → Bool := fun j i => decide (j ≠ i)
    let T := branching.run 1 1 2 false 2 w
    (T 0 false (), T 1 false (), T 1 true ()) = (⟨2, 1⟩, ⟨1, 1 / 4⟩, ⟨1, 1 / 2⟩) := by
  norm_num [Sampler.run, Sampler.rollout, branching, record, Stats.observe, empty, Fin.last]

end Cslib.Algorithms.Lean.MarkovDecision.UCT.Tests
