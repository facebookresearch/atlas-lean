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

* `tendsto_birkhoffSum_div_integral_ae` and `birkhoffLimit_ae_eq_const` for the identity on the
  one-point space with the Dirac measure and `f = 1`.
-/

@[expose] public section

open MeasureTheory Filter Topology StatMech.BirkhoffAE

namespace MathlibExtTest.StatMech.Dynamics.Ergodic.BirkhoffErgodic

/-- The identity on the one-point space is ergodic for the Dirac measure. -/
lemma ergodic_id_unit : Ergodic (id : Unit → Unit) (Measure.dirac ()) :=
  ⟨MeasurePreserving.id _, ⟨fun _ _ _ => Filter.EventuallyConst.of_subsingleton_left⟩⟩

example : ∀ᵐ x ∂(Measure.dirac ()), Tendsto
    (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (fun _ : Unit => (1 : ℝ)) (id^[k] x)) atTop
    (𝓝 (∫ _, (1 : ℝ) ∂(Measure.dirac ()))) :=
  Ergodic.tendsto_birkhoffSum_div_integral_ae ergodic_id_unit (integrable_const _)

example : birkhoffLimit (id : Unit → Unit) (fun _ => (1 : ℝ)) =ᵐ[Measure.dirac ()]
    Function.const Unit (∫ _, (1 : ℝ) ∂(Measure.dirac ())) :=
  Ergodic.birkhoffLimit_ae_eq_const ergodic_id_unit (integrable_const _)

end MathlibExtTest.StatMech.Dynamics.Ergodic.BirkhoffErgodic
