/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Radon–Nikodym derivatives at atoms and of probability mass functions

The Radon–Nikodym derivative `μ.rnDeriv ν` is determined only up to `ν`-null sets, but at an
atom of `ν`, a point `x` with `0 < ν {x} < ∞`, its value is forced: `μ {x} / ν {x}`. This needs
only a Lebesgue decomposition of `μ` with respect to `ν`, but neither absolute continuity nor
a countable space; measurable singletons are needed only for the PMF corollaries below.

For probability mass functions `p` and `q` on a space with measurable singletons, this gives
the derivative of `p.toMeasure` with respect to `q.toMeasure` at every point that `q` charges,
the mass ratio `p x / q x`. Absolute continuity `p.toMeasure ≪ q.toMeasure` is support
inclusion `p.support ⊆ q.support`.

## Main results

* `MeasureTheory.Measure.rnDeriv_eq_measure_singleton_div`: the derivative at an atom.
* `PMF.toMeasure_absolutelyContinuous_iff`: absolute continuity of PMF measures is support
  inclusion.
* `PMF.rnDeriv_toMeasure_apply`: the derivative of PMF measures at a point that `q` charges.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

/-- **Radon–Nikodym derivative at an atom.** If `μ` has a
Lebesgue decomposition with respect to `ν`, then at every point `x` with `ν {x} ≠ 0` and
`ν {x} ≠ ∞` the derivative is `μ.rnDeriv ν x = μ {x} / ν {x}`. The singular part of `μ`
vanishes at `x` because it is carried by a `ν`-null set, so `μ` is not assumed absolutely
continuous with respect to `ν`. The finiteness hypothesis `ν {x} ≠ ∞` cannot be dropped:
for `μ = ν = ∞ • Measure.dirac x`, `μ.rnDeriv ν x` is nonzero, while
`μ {x} / ν {x} = ∞ / ∞ = 0`. -/
theorem rnDeriv_eq_measure_singleton_div {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] {x : α}
    (h0 : ν {x} ≠ 0) (htop : ν {x} ≠ ∞) :
    μ.rnDeriv ν x = μ {x} / ν {x} := by
  have hs : μ.singularPart ν {x} = 0 := by
    have h := mutuallySingular_singularPart μ ν
    have hx : x ∈ h.nullSet := by
      by_contra hx
      exact h0 (measure_mono_null (Set.singleton_subset_iff.mpr hx) h.measure_compl_nullSet)
    exact measure_mono_null (Set.singleton_subset_iff.mpr hx) h.measure_nullSet
  have hμ : μ {x} = μ.rnDeriv ν x * ν {x} := by
    conv_lhs => rw [haveLebesgueDecomposition_add μ ν]
    rw [_root_.add_apply, hs, zero_add]
    apply le_antisymm
    · set g := μ.rnDeriv ν with hg
      set T := toMeasurable ν {x} with hT
      set t := (g ⁻¹' Set.Iic (g x)) ∩ T with ht
      have hxT : x ∈ T := Set.singleton_subset_iff.mp (subset_toMeasurable ν {x})
      have hxt : x ∈ t :=
        ⟨Set.mem_preimage.mpr (Set.mem_Iic.mpr le_rfl), hxT⟩
      have ht_sub : {x} ⊆ t := Set.singleton_subset_iff.mpr hxt
      have ht_meas : MeasurableSet t :=
        ((measurable_rnDeriv μ ν) measurableSet_Iic).inter (measurableSet_toMeasurable ν {x})
      have hνt : ν t ≤ ν {x} :=
        (measure_mono Set.inter_subset_right).trans (measure_toMeasurable {x}).le
      calc ν.withDensity g {x} ≤ ν.withDensity g t := measure_mono ht_sub
        _ = ∫⁻ y in t, g y ∂ν := withDensity_apply _ ht_meas
        _ ≤ ∫⁻ _ in t, g x ∂ν :=
            lintegral_mono_ae ((ae_restrict_mem ht_meas).mono fun y hy => hy.1)
        _ = g x * ν t := setLIntegral_const t (g x)
        _ ≤ g x * ν {x} := by gcongr
    · calc μ.rnDeriv ν x * ν {x} = ∫⁻ y in {x}, μ.rnDeriv ν y ∂ν :=
            (lintegral_singleton' (measurable_rnDeriv μ ν) x).symm
        _ ≤ ν.withDensity (μ.rnDeriv ν) {x} := withDensity_apply_le _ _
  rw [hμ, ENNReal.mul_div_cancel_right h0 htop]

end MeasureTheory.Measure

namespace PMF

/-- **Absolute continuity of PMF measures.** On a space with measurable singletons,
`p.toMeasure` is absolutely continuous with respect to `q.toMeasure` exactly when every point
charged by `p` is charged by `q`. -/
theorem toMeasure_absolutelyContinuous_iff {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {p q : PMF α} :
    p.toMeasure ≪ q.toMeasure ↔ p.support ⊆ q.support := by
  refine ⟨fun h x hx => ?_, fun h => Measure.AbsolutelyContinuous.mk fun s hs hq => ?_⟩
  · rw [mem_support_iff] at hx ⊢
    intro hq
    have h1 := h (show q.toMeasure {x} = 0 by
      rw [q.toMeasure_apply_singleton x (measurableSet_singleton x), hq])
    rw [p.toMeasure_apply_singleton x (measurableSet_singleton x)] at h1
    exact hx h1
  · rw [toMeasure_apply_eq_zero_iff _ hs] at hq ⊢
    exact hq.mono_left h

/-- **Radon–Nikodym derivative of PMF measures.** On a space with measurable singletons, at
every point `x` with `q x ≠ 0` the derivative of `p.toMeasure` with respect to `q.toMeasure`
is the mass ratio `p x / q x`. -/
theorem rnDeriv_toMeasure_apply {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (p q : PMF α) {x : α} (hx : q x ≠ 0) :
    p.toMeasure.rnDeriv q.toMeasure x = p x / q x := by
  have hq := q.toMeasure_apply_singleton x (measurableSet_singleton x)
  rw [Measure.rnDeriv_eq_measure_singleton_div p.toMeasure q.toMeasure (hq ▸ hx)
      (hq ▸ q.apply_ne_top x), p.toMeasure_apply_singleton x (measurableSet_singleton x), hq]

end PMF
