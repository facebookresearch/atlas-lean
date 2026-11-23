/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.Ergodic.BernoulliShift
public import Mathlib.Probability.UniformOn

import Mathlib.Tactic

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Dynamics.Ergodic.Mixing MathlibExt.Dynamics.Ergodic.BernoulliShift

namespace MathlibExtTest.Dynamics.Ergodic.BernoulliShift

-- The shift reads the sequence from the next position.
example : shift^[3] (fun n : ℕ => n) 2 = 5 := by
  rw [shift_iterate_apply]

-- The fair coin-tossing shift is mixing and ergodic.
example : IsMixing shift
    (Measure.infinitePi fun _ : ℕ => uniformOn (Set.univ : Set Bool)) :=
  isMixing_shift _

example : Ergodic shift
    (Measure.infinitePi fun _ : ℕ => uniformOn (Set.univ : Set (Fin 3))) :=
  ergodic_shift _

-- Mixing gives asymptotic independence of the first coordinate and the `n`-th one.
example (p : Measure Bool) [IsProbabilityMeasure p] :
    Filter.Tendsto
      (fun n : ℕ => (Measure.infinitePi fun _ : ℕ => p)
        ({x | x 0 = true} ∩ shift^[n] ⁻¹' {x | x 0 = true}))
      Filter.atTop
      (nhds ((Measure.infinitePi fun _ : ℕ => p) {x | x 0 = true} *
        (Measure.infinitePi fun _ : ℕ => p) {x | x 0 = true})) :=
  (isMixing_shift p).tendsto_measure_inter_preimage
    (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const)
    (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const)

end MathlibExtTest.Dynamics.Ergodic.BernoulliShift
