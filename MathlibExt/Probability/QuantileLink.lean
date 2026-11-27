/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Quantile

/-!
# Equipercentile linking

For probability measures with continuous, strictly monotone cdfs, the
equipercentile link `x ↦ cdfQuantile ν (cdf μ x)` pushes `μ` forward to
`ν` and is a two-sided inverse of the reverse link. The work is the
intermediate lemma: pushing a measure forward by its own cdf gives
Lebesgue measure restricted to `[0, 1]`.
-/

open MeasureTheory Set

@[expose] public section

namespace QuantileLink

open ProbabilityTheory

/-- NEW OBLIGATION (intermediate cdf-pushforward lemma).

For a probability measure whose cdf is continuous and strictly
monotone, pushing the measure forward by its own cdf gives Lebesgue
measure restricted to `[0, 1]`.  There is no Atlas lemma with this
conclusion, so this -- not transport itself -- is the leaf's real
proof work.  It must be proved from cdf facts; it may not be assumed
by any downstream statement in this file.

Expected route (all names verified against Mathlib at the pinned
revision): apply `MeasureTheory.Measure.ext_of_Iic` -- it suffices to
agree on every `Set.Iic t` -- with `MeasureTheory.Measure.map_apply`
(measurability of `fun x => cdf μ x` is `(cdf μ).mono.measurable`).
For `t ∈ Ioo 0 1`, `{x | cdf μ x ≤ t} = Set.Iic (cdfQuantile μ t)` by
`StrictMono.le_iff_le hmono` and
`cdf_cdfQuantile_eq_of_continuous`, so by
`ProbabilityTheory.ofReal_cdf` the pushforward's mass on `Set.Iic t`
is `ENNReal.ofReal t`, as is Lebesgue's.  For `t < 0` the preimage is
empty by `ProbabilityTheory.cdf_nonneg`; for `t ≥ 1` it is everything
by `ProbabilityTheory.cdf_le_one`; for `t = 0` it is empty by
`cdf_mem_Ioo_of_strictMono` below (no mass escapes `[0, 1]`). -/
theorem cdf_pushforward_eq_volume_restrict_Icc (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hcont : Continuous (cdf μ))
    (hmono : StrictMono (cdf μ)) :
    Measure.map (fun x => cdf μ x) μ = (volume : Measure ℝ).restrict (Icc 0 1) := by
  have hmeas : Measurable (fun x => cdf μ x) := (monotone_cdf μ).measurable
  apply Measure.ext_of_Iic _ _
  intro t
  rw [Measure.map_apply hmeas measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic]
  by_cases ht0 : t < 0
  · have hpre : (fun x => cdf μ x) ⁻¹' Iic t = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro x hx
      simp only [mem_preimage, mem_Iic] at hx
      have h0 := cdf_nonneg μ x
      linarith
    have hinter : Iic t ∩ Icc (0 : ℝ) 1 = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro x hx
      simp only [mem_inter_iff, mem_Iic, mem_Icc] at hx
      obtain ⟨h1, h2, -⟩ := hx
      linarith
    rw [hpre, hinter, measure_empty, measure_empty]
  · by_cases ht1 : t < 1
    · by_cases ht0' : t = 0
      · subst ht0'
        have hpre : (fun x => cdf μ x) ⁻¹' Iic (0 : ℝ) = ∅ := by
          rw [eq_empty_iff_forall_notMem]
          intro x hx
          simp only [mem_preimage, mem_Iic] at hx
          have hpos : (0 : ℝ) < cdf μ x :=
            (cdf_nonneg μ (x - 1)).trans_lt (hmono (sub_one_lt x))
          linarith
        have hinter : Iic (0 : ℝ) ∩ Icc (0 : ℝ) 1 = {(0 : ℝ)} := by
          ext x
          simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_singleton_iff]
          constructor
          · intro h
            exact le_antisymm h.1 h.2.1
          · rintro rfl
            norm_num
        rw [hpre, hinter, measure_empty, Real.volume_singleton]
      · have hu : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne' (le_of_not_gt ht0) ht0', ht1⟩
        have hset : (fun x => cdf μ x) ⁻¹' Iic t = Iic (cdfQuantile μ t) := by
          ext x
          simp only [mem_preimage, mem_Iic]
          have hq : cdf μ (cdfQuantile μ t) = t :=
            cdf_cdfQuantile_eq_of_continuous μ hcont hu
          calc cdf μ x ≤ t ↔ cdf μ x ≤ cdf μ (cdfQuantile μ t) := by rw [hq]
            _ ↔ x ≤ cdfQuantile μ t := hmono.le_iff_le
        have hinter : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 t := by
          ext x
          simp only [mem_inter_iff, mem_Iic, mem_Icc]
          constructor
          · intro h
            exact ⟨h.2.1, h.1⟩
          · intro h
            exact ⟨h.2, h.1, h.2.trans hu.2.le⟩
        rw [hset, ← ofReal_cdf μ (cdfQuantile μ t),
          cdf_cdfQuantile_eq_of_continuous μ hcont hu, hinter, Real.volume_Icc,
          sub_zero]
    · have ht1' : (1 : ℝ) ≤ t := le_of_not_gt ht1
      have hpre : (fun x => cdf μ x) ⁻¹' Iic t = univ := by
        ext x
        simp only [mem_preimage, mem_Iic, mem_univ]
        exact iff_of_true ((cdf_le_one μ x).trans ht1') trivial
      have hinter : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 1 := by
        ext x
        simp only [mem_inter_iff, mem_Iic, mem_Icc]
        constructor
        · intro h
          exact h.2
        · intro h
          exact ⟨h.2.trans ht1', h⟩
      rw [hpre, hinter, measure_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]

/-- NEW OBLIGATION (helper for the roundtrips and for the endpoint
cases of `cdf_pushforward_eq_volume_restrict_Icc`).

Under a strictly monotone cdf of a probability measure, every cdf
value lies strictly between `0` and `1`: if `cdf μ x = 0`, any
`y < x` would have `cdf μ y < 0`; if `cdf μ x = 1`, any
`y > x` would
have `cdf μ y > 1`.  Continuity is not needed here. -/
theorem cdf_mem_Ioo_of_strictMono (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hmono : StrictMono (cdf μ)) (x : ℝ) :
    cdf μ x ∈ Ioo (0 : ℝ) 1 := by
  exact ⟨(cdf_nonneg μ (x - 1)).trans_lt (hmono (sub_one_lt x)),
    (hmono (lt_add_one x)).trans_le (cdf_le_one μ (x + 1))⟩

/-- equipercentile linking over the actual
Atlas objects.

Let `μ, ν` be probability measures on `ℝ` with continuous, strictly
monotone cdfs, and let `e = fun x => cdfQuantile ν (cdf μ x)` be the
equipercentile link.  Then:

1. (transport) `e` pushes `μ` forward to `ν`;
2. (roundtrips) `cdfQuantile μ ∘ cdf ν` is a two-sided inverse of `e`.

Proof route for (1) -- a composition, not an assumption:
`Measure.map e μ
  = Measure.map (cdfQuantile ν) (Measure.map (fun x => cdf μ x) μ)`
by `Measure.map_map (measurable_cdfQuantile ν) (cdf μ).mono.measurable`,
`= Measure.map (cdfQuantile ν) ((volume : Measure ℝ).restrict (Icc 0 1))`
by `cdf_pushforward_eq_volume_restrict_Icc μ hμcont hμmono`,
`= ν` by `map_cdfQuantile_restrict_Icc ν`.

Proof route for (2): for the first roundtrip, `cdf μ x ∈ Ioo 0 1` by
`cdf_mem_Ioo_of_strictMono μ hμmono`, so
`cdf_cdfQuantile_eq_of_continuous ν hνcont` gives
`cdf ν (cdfQuantile ν (cdf μ x)) = cdf μ x`, and
`cdfQuantile_cdf_of_strictMono μ hμmono` finishes.  The second
roundtrip is symmetric, using `cdf_mem_Ioo_of_strictMono ν hνmono`,
`cdf_cdfQuantile_eq_of_continuous μ hμcont`, and
`cdfQuantile_cdf_of_strictMono ν hνmono`. -/
theorem equipercentileLink_spec (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμcont : Continuous (cdf μ)) (hμmono : StrictMono (cdf μ))
    (hνcont : Continuous (cdf ν)) (hνmono : StrictMono (cdf ν)) :
    Measure.map (fun x => cdfQuantile ν (cdf μ x)) μ = ν ∧
    (∀ x : ℝ,
      (cdfQuantile μ ∘ fun y => cdf ν y)
        ((fun x => cdfQuantile ν (cdf μ x)) x) = x) ∧
    (∀ y : ℝ,
      (fun x => cdfQuantile ν (cdf μ x))
        ((cdfQuantile μ ∘ fun z => cdf ν z) y) = y) := by
  have hmeas : Measurable (fun x => cdf μ x) := (monotone_cdf μ).measurable
  refine ⟨?_, ?_, ?_⟩
  · have hcomp : (fun x => cdfQuantile ν (cdf μ x))
        = cdfQuantile ν ∘ (fun x => cdf μ x) := rfl
    rw [hcomp, ← Measure.map_map (measurable_cdfQuantile ν) hmeas,
      cdf_pushforward_eq_volume_restrict_Icc μ hμcont hμmono,
      map_cdfQuantile_restrict_Icc ν]
  · intro x
    show cdfQuantile μ (cdf ν (cdfQuantile ν (cdf μ x))) = x
    have h1 : cdf μ x ∈ Ioo (0 : ℝ) 1 := cdf_mem_Ioo_of_strictMono μ hμmono x
    rw [cdf_cdfQuantile_eq_of_continuous ν hνcont h1,
      cdfQuantile_cdf_of_strictMono μ hμmono x]
  · intro y
    show cdfQuantile ν (cdf μ (cdfQuantile μ (cdf ν y))) = y
    have h1 : cdf ν y ∈ Ioo (0 : ℝ) 1 := cdf_mem_Ioo_of_strictMono ν hνmono y
    rw [cdf_cdfQuantile_eq_of_continuous μ hμcont h1,
      cdfQuantile_cdf_of_strictMono ν hνmono y]

end QuantileLink
