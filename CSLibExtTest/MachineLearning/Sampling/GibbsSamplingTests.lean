/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sampling.GibbsSampling

@[expose] public section

/-!
# Tests for Gibbs sampling
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Function Cslib.MachineLearning.Sampling
open scoped ENNReal NNReal

namespace CSLibExtTest.MachineLearning.Sampling.GibbsSampling

/-- The uniform law on pairs of bits. -/
noncomputable def uniform : PMF (Fin 2 → Bool) :=
  PMF.ofFintype (fun _ ↦ ((1 / 4 : ℝ≥0) : ℝ≥0∞)) (by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      nsmul_eq_mul, ← ENNReal.coe_natCast, ← ENNReal.coe_mul, ← ENNReal.coe_one, ENNReal.coe_inj,
      ← NNReal.coe_inj]
    push_cast
    norm_num)

theorem uniform_pos (x : Fin 2 → Bool) : uniform x ≠ 0 := by
  simp [uniform]

/-- Under the uniform law, resampling a coordinate picks each bit with probability `1 / 2`. -/
example (x : Fin 2 → Bool) (b : Bool) :
    gibbsStep uniform uniform_pos 0 x (update x 0 b) = ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
  rw [gibbsStep_apply]
  simp only [update_self, ↓reduceIte, uniform, PMF.ofFintype_apply, condNorm, Fintype.sum_bool]
  rw [← ENNReal.coe_add, ← ENNReal.coe_div (by norm_num), ENNReal.coe_inj, ← NNReal.coe_inj]
  push_cast
  norm_num

/-- A coordinate update never changes the other coordinate. -/
example (x : Fin 2 → Bool) : gibbsStep uniform uniform_pos 0 x (update x 1 (!x 1)) = 0 := by
  rw [gibbsStep_apply, ite_eq_right_iff]
  intro h
  have := congrFun h 1
  simp at this

/-- The sweep `[0, 1]` updates coordinate `0` first: from `x` it first draws from the coordinate-`0`
update and then runs the coordinate-`1` update. -/
example (x : Fin 2 → Bool) :
    gibbsSweep uniform uniform_pos [0, 1] x =
      (pmfKernel (gibbsStep uniform uniform_pos 0) x).bind
        (pmfKernel (gibbsStep uniform uniform_pos 1)) := by
  rw [gibbsSweep_cons_apply]
  congr 1
  exact congrArg DFunLike.coe (Kernel.id_comp _)

/-- A full sweep over both coordinates leaves the uniform law stationary. -/
example : (gibbsSweep uniform uniform_pos [0, 1]).Invariant uniform.toMeasure :=
  invariant_gibbsSweep uniform uniform_pos [0, 1]

end CSLibExtTest.MachineLearning.Sampling.GibbsSampling
