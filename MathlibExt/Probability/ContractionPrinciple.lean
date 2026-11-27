/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LargeDeviationPrinciple
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-!
# The contraction principle

If a sequence of measures `μₙ` on `X` satisfies a large deviation principle with a *good* rate
function `I`, and `F : X → Y` is continuous into a Hausdorff space, then the image measures
`F_* μₙ` satisfy a large deviation principle on `Y` with the good rate function

`J(y) = inf { I(x) : F(x) = y }`.

The proof is Varadhan's: preimages of closed (open) sets under `F` are closed (open), and the
infimum of `I` over `F⁻¹(C)` is the infimum of `J` over `C`. Goodness of `I` is what makes `J` a
rate function at all: the finite sub-level sets of `J` are the images `F({I ≤ a})` of the compact
sub-level sets of `I` (the infimum defining `J` is attained), hence compact and closed.

## Source

S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010,
Section 2, Theorem 2.7 (https://math.nyu.edu/~varadhan/LDP/1-2.pdf), stated there for Polish
spaces; the argument only uses continuity of `F`, goodness of `I` and the Hausdorff property of
`Y`. See also A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed.,
Section 4.2.

## Main results

* `pushforwardRate F I`: the rate function `y ↦ inf_{F x = y} I x`.
* `coe_biInf_ennreal`: the coercion `ℝ≥0∞ → EReal` commutes with bounded infima.
* `iInf_preimage_eq_iInf_pushforwardRate`: `inf_{F⁻¹ C} I = inf_C J`.
* `exists_eq_pushforwardRate`: for a good rate function the infimum defining `J y` is attained.
* `isGoodRateFunction_pushforwardRate`: `J` is a good rate function.
* `satisfiesLDP_map`: the contraction principle.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace MathlibExt.Probability.ContractionPrinciple

open MathlibExt.Probability.LargeDeviationPrinciple

variable {X Y : Type*}

/-- **Push-forward rate function.** For `F : X → Y` and `I : X → [0, ∞]`, the function
`J(y) = inf { I(x) : F(x) = y }`, which is `∞` off the range of `F`. It is the rate function of
the contraction principle (Varadhan, *Large Deviations*, NYU lecture notes, 2010, Section 2,
Theorem 2.7). -/
noncomputable def pushforwardRate (F : X → Y) (I : X → ℝ≥0∞) : Y → ℝ≥0∞ :=
  fun y => ⨅ x ∈ F ⁻¹' {y}, I x

/-- **The coercion from extended nonnegative reals to extended reals commutes with bounded
infima.** For any set `s` (empty or not) and `f : ι → [0, ∞]`, the infimum of `f` over `s`
computed in `[0, ∞]` and then coerced agrees with the infimum of the coerced values computed in
`EReal`; both are `∞` when `s` is empty. -/
theorem coe_biInf_ennreal {ι : Type*} (s : Set ι) (f : ι → ℝ≥0∞) :
    (((⨅ i ∈ s, f i : ℝ≥0∞)) : EReal) = ⨅ i ∈ s, (f i : EReal) := by
  apply le_antisymm
  · exact le_iInf₂ fun i hi => EReal.coe_ennreal_le_coe_ennreal_iff.mpr (iInf₂_le i hi)
  · set m : EReal := ⨅ i ∈ s, (f i : EReal) with hm
    have hm0 : 0 ≤ m := le_iInf₂ fun i _ => EReal.coe_ennreal_nonneg _
    rw [← EReal.coe_toENNReal hm0]
    refine EReal.coe_ennreal_le_coe_ennreal_iff.mpr (le_iInf₂ fun i hi => ?_)
    have h1 : m ≤ (f i : EReal) := iInf₂_le i hi
    rw [← EReal.coe_toENNReal hm0] at h1
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mp h1

/-- **Infimum over a preimage.** The infimum of `I` over `F⁻¹(C)` equals the infimum over `C` of
the push-forward rate function `J(y) = inf_{F x = y} I x`, both computed in `EReal`. This is the
identity behind both bounds of the contraction principle. -/
theorem iInf_preimage_eq_iInf_pushforwardRate (F : X → Y) (I : X → ℝ≥0∞) (C : Set Y) :
    (⨅ x ∈ F ⁻¹' C, (I x : EReal)) = ⨅ y ∈ C, (pushforwardRate F I y : EReal) := by
  simp_rw [pushforwardRate, coe_biInf_ennreal]
  apply le_antisymm
  · refine le_iInf₂ fun y hy => le_iInf₂ fun x hx => ?_
    have hx' : F x ∈ C := by
      rw [mem_preimage, mem_singleton_iff] at hx
      rw [hx]; exact hy
    exact iInf₂_le x hx'
  · refine le_iInf₂ fun x hx => ?_
    exact (iInf₂_le (F x) hx).trans (iInf₂_le x (by simp))

variable [TopologicalSpace X] [TopologicalSpace Y]

/-- **The contraction infimum is attained.** If `I` is a good rate function, `F` is continuous
and `Y` is Hausdorff, then for every `y` with `J(y) < ∞` there is `x` with `F x = y` and
`I x = J y`, where `J = pushforwardRate F I`. The minimiser exists because the fibre
`F⁻¹{y}` is closed and meets a compact sub-level set of the lower semicontinuous `I`. -/
theorem exists_eq_pushforwardRate [T2Space Y] {F : X → Y} (hF : Continuous F)
    {I : X → ℝ≥0∞} (hI : IsGoodRateFunction I) {y : Y} (hy : pushforwardRate F I y ≠ ⊤) :
    ∃ x, F x = y ∧ I x = pushforwardRate F I y := by
  set r : ℝ := (pushforwardRate F I y).toReal + 1 with hr
  have hlt : pushforwardRate F I y < ENNReal.ofReal r := by
    rw [hr, ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_toReal hy]
    exact ENNReal.lt_add_right hy (by simp)
  set K : Set X := F ⁻¹' {y} ∩ {x | I x ≤ ENNReal.ofReal r} with hK
  have hKc : IsCompact K :=
    (hI.isCompact_levelSet r).inter_left (isClosed_singleton.preimage hF)
  have hKne : K.Nonempty := by
    obtain ⟨x, hx, hxlt⟩ : ∃ x ∈ F ⁻¹' {y}, I x < ENNReal.ofReal r := by
      simpa [pushforwardRate, iInf_lt_iff] using hlt
    exact ⟨x, hx, hxlt.le⟩
  obtain ⟨x₀, hx₀K, hmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn hKne hKc (hI.lowerSemicontinuous.lowerSemicontinuousOn K)
  refine ⟨x₀, hx₀K.1, le_antisymm ?_ (iInf₂_le x₀ hx₀K.1)⟩
  refine le_iInf₂ fun x hx => ?_
  by_cases hxK : I x ≤ ENNReal.ofReal r
  · exact (isMinOn_iff.mp hmin) x ⟨hx, hxK⟩
  · exact hx₀K.2.trans (not_le.mp hxK).le

/-- **Sub-level sets of the push-forward rate.** For a good rate function `I`, continuous `F`
and Hausdorff `Y`, the sub-level set `{J ≤ a}` of `J = pushforwardRate F I` at a finite level
`a` is the image `F({I ≤ a})`. (At `a = ∞` the left side is all of `Y` while the right side
is the range of `F`.) -/
theorem setOf_pushforwardRate_le [T2Space Y] {F : X → Y} (hF : Continuous F)
    {I : X → ℝ≥0∞} (hI : IsGoodRateFunction I) {a : ℝ≥0∞} (ha : a ≠ ⊤) :
    {y | pushforwardRate F I y ≤ a} = F '' {x | I x ≤ a} := by
  ext y
  constructor
  · intro hy
    have htop : pushforwardRate F I y ≠ ⊤ := ne_top_of_le_ne_top ha hy
    obtain ⟨x, hxy, hIx⟩ := exists_eq_pushforwardRate hF hI htop
    exact ⟨x, by simpa [hIx] using hy, hxy⟩
  · rintro ⟨x, hx, rfl⟩
    have hle : pushforwardRate F I (F x) ≤ I x :=
      iInf₂_le (f := fun x' (_ : x' ∈ F ⁻¹' {F x}) => I x') x rfl
    exact hle.trans hx

/-- **The push-forward of a good rate function is a good rate function.** If `I` is a good rate
function on `X`, `F : X → Y` is continuous and `Y` is Hausdorff, then
`J(y) = inf_{F x = y} I x` is lower semicontinuous with compact finite sub-level sets
(Varadhan, *Large Deviations*, NYU lecture notes, 2010, Section 2, Theorem 2.7). -/
theorem isGoodRateFunction_pushforwardRate [T2Space Y] {F : X → Y} (hF : Continuous F)
    {I : X → ℝ≥0∞} (hI : IsGoodRateFunction I) :
    IsGoodRateFunction (pushforwardRate F I) := by
  refine ⟨⟨?_⟩, fun a => ?_⟩
  · rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro a
    by_cases ha : a = ⊤
    · subst ha
      simp only [Iic_top, preimage_univ, isClosed_univ]
    · have : pushforwardRate F I ⁻¹' Iic a = {y | pushforwardRate F I y ≤ a} := rfl
      rw [this, setOf_pushforwardRate_le hF hI ha, ← ENNReal.ofReal_toReal ha]
      exact ((hI.isCompact_levelSet a.toReal).image hF).isClosed
  · rw [setOf_pushforwardRate_le hF hI ENNReal.ofReal_ne_top]
    exact (hI.isCompact_levelSet a).image hF

/-- **Contraction principle.** Let `μₙ` be measures on `X` satisfying the large deviation
principle with a good rate function `I`, and let `F : X → Y` be continuous, where `Y` is a
Hausdorff Borel space. Then the image measures `F_* μₙ` satisfy the large deviation principle on
`Y` with the good rate function `J(y) = inf { I(x) : F(x) = y }`.

Source: S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010,
Section 2, Theorem 2.7 (stated for Polish `X` and `Y`). -/
theorem satisfiesLDP_map [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace Y] [T2Space Y] {μ : ℕ → Measure X} {I : X → ℝ≥0∞} (hμ : SatisfiesLDP μ I)
    (hI : IsGoodRateFunction I) {F : X → Y} (hF : Continuous F) :
    SatisfiesLDP (fun n => (μ n).map F) (pushforwardRate F I) := by
  refine ⟨(isGoodRateFunction_pushforwardRate hF hI).toIsRateFunction, fun U hU => ?_,
    fun C hC => ?_⟩
  · have h := hμ.lower_bound (F ⁻¹' U) (hU.preimage hF)
    rw [iInf_preimage_eq_iInf_pushforwardRate] at h
    simpa only [Measure.map_apply hF.measurable hU.measurableSet] using h
  · have h := hμ.upper_bound (F ⁻¹' C) (hC.preimage hF)
    rw [iInf_preimage_eq_iInf_pushforwardRate] at h
    simpa only [Measure.map_apply hF.measurable hC.measurableSet] using h

end MathlibExt.Probability.ContractionPrinciple
