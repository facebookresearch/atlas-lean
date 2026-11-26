/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.Ergodic.MaximalBirkhoff

/-!
# Tests for `MathlibExt.Dynamics.Ergodic.MaximalBirkhoff`

* `maxBirkhoff` at `n = 0` is `0`.
* `maximal_ergodic_inequality` and `hopf_maximal_inequality` for the identity on the one-point
  space with the Dirac measure and `f = 1`.
-/

@[expose] public section

open MeasureTheory StatMech.Birkhoff

namespace MathlibExtTest.StatMech.Dynamics.Ergodic.MaximalBirkhoff

example (T : Unit → Unit) (f : Unit → ℝ) (x : Unit) : maxBirkhoff T f 0 x = 0 := by
  simp [maxBirkhoff]

example : 0 ≤ ∫ x in {x | 0 < maxBirkhoff id (fun _ : Unit => (1 : ℝ)) 3 x},
    (fun _ : Unit => (1 : ℝ)) x ∂(Measure.dirac ()) :=
  maximal_ergodic_inequality (MeasurePreserving.id _) (integrable_const _) 3

example : (1 / 2 : ℝ) *
    ((Measure.dirac ()) (maximalLevelSet id (fun _ : Unit => (1 : ℝ)) (1 / 2) 3)).toReal
    ≤ ∫ x in maximalLevelSet id (fun _ : Unit => (1 : ℝ)) (1 / 2) 3, (fun _ => (1 : ℝ)) x
      ∂(Measure.dirac ()) :=
  hopf_maximal_inequality (MeasurePreserving.id _) (integrable_const _) _ 3

end MathlibExtTest.StatMech.Dynamics.Ergodic.MaximalBirkhoff
