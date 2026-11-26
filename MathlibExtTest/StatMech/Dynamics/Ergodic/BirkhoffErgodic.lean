/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.Ergodic.BirkhoffErgodic

/-!
# Tests for `MathlibExt.Dynamics.Ergodic.BirkhoffErgodic`

* `birkhoffAverage_eq_inv_mul_sum` for a constant function, and with it the explicit averages in
  `MathlibExt.Dynamics.Ergodic.BirkhoffWanted.birkhoff_pointwise_ergodic`, for the identity on
  the one-point space with the Dirac measure and `f = 1`.
* The `Function.const` form of `birkhoffLimit_ae_eq_integral_of_ergodic` in the same setting.
-/

@[expose] public section

open MeasureTheory Filter Topology StatMech.BirkhoffAE

namespace MathlibExtTest.StatMech.Dynamics.Ergodic.BirkhoffErgodic

/-- The identity on the one-point space is ergodic for the Dirac measure. -/
lemma ergodic_id_unit : Ergodic (id : Unit → Unit) (Measure.dirac ()) :=
  ⟨MeasurePreserving.id _, ⟨fun _ _ _ => Filter.EventuallyConst.of_subsingleton_left⟩⟩

example (n : ℕ) (x : Unit) :
    birkhoffAverage ℝ (id : Unit → Unit) (fun _ => (2 : ℝ)) n x
      = (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (fun _ : Unit => (2 : ℝ)) (id^[k] x) :=
  birkhoffAverage_eq_inv_mul_sum _ _ n x

example : ∀ᵐ x ∂(Measure.dirac ()), Tendsto
    (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (fun _ : Unit => (1 : ℝ)) (id^[k] x)) atTop
    (𝓝 (∫ _, (1 : ℝ) ∂(Measure.dirac ()))) := by
  filter_upwards [MathlibExt.Dynamics.Ergodic.BirkhoffWanted.birkhoff_pointwise_ergodic
    ergodic_id_unit (integrable_const (1 : ℝ))] with x hx
  simpa only [birkhoffAverage_eq_inv_mul_sum] using hx

example : birkhoffLimit (id : Unit → Unit) (fun _ => (1 : ℝ)) =ᵐ[Measure.dirac ()]
    Function.const Unit (∫ _, (1 : ℝ) ∂(Measure.dirac ())) := by
  filter_upwards [birkhoffLimit_ae_eq_integral_of_ergodic ergodic_id_unit
    (integrable_const _)] with x hx
  simpa [Function.const] using hx

end MathlibExtTest.StatMech.Dynamics.Ergodic.BirkhoffErgodic
