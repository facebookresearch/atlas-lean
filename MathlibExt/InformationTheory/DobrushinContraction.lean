/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.MeasurePinsker
public import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.MeasureTheory.Measure.Sub

/-!
# Dobrushin's contraction coefficient for total variation

For a Markov kernel `κ` from `X` to `Y`, Dobrushin's coefficient is
`η_TV(κ) = sup_{x, x'} TV(κ x, κ x')`, with `TV(μ, ν) = sup_B |μ(B) - ν(B)|`. This file proves
the strong data-processing inequality for total variation,

`TV(κ ∘ μ, κ ∘ ν) ≤ η_TV(κ) · TV(μ, ν)` for all probability measures `μ`, `ν` on `X`,

and that `η_TV(κ)` is the least such constant when singletons of `X` are measurable: the
inequality for the point masses `δ_x` and `δ_{x'}` bounds each `TV(κ x, κ x')`, hence their
supremum. The supremum need not be attained by a pair of point masses: for the kernel on `ℕ`
whose rows are `Bernoulli(n / (n + 1))` it is `1`, while every pair of rows is at total variation
below `1`. Since `η_TV(κ) ≤ 1`, the ordinary data-processing inequality for total variation
follows. No countability or standard-Borel hypothesis is used: the proof splits `μ` and `ν` into
their common part (mass `1 - TV`) and two remainders of mass `TV`, and compares the remainders
through an averaged pair of inputs.

## Main results

* `dobrushinCoeff κ`: `sup_{x, x'} TV(κ x, κ x')`.
* `totalVariationDist_comp_le`: `TV(κ ∘ₘ μ, κ ∘ₘ ν) ≤ dobrushinCoeff κ * TV(μ, ν)`.
* `totalVariationDist_comp_le_self`: `TV(κ ∘ₘ μ, κ ∘ₘ ν) ≤ TV(μ, ν)`.
* `dobrushinCoeff_le_of_forall`: `dobrushinCoeff κ` is at most every constant `c ≥ 0` with
  `TV(κ ∘ₘ μ, κ ∘ₘ ν) ≤ c · TV(μ, ν)` for all `μ`, `ν`.

## References

* Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University
  Press, 2025, Theorem 33.4 (Dobrushin: `η_TV = sup_{x ≠ x'} TV(P_{Y|X=x}, P_{Y|X=x'})`).
* R. L. Dobrushin, Central limit theorem for nonstationary Markov chains. I, Theory Probab.
  Appl. 1 (1956), 65-80.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.TotalVariationDistance MathlibExt.InformationTheory.MeasurePinsker

namespace MathlibExt.InformationTheory.DobrushinContraction

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- **Dobrushin's contraction coefficient** of a Markov kernel `κ`:
`η_TV(κ) = sup_{x, x'} TV(κ x, κ x')`, where `TV(μ, ν) = sup_B |μ(B) - ν(B)|`. It lies in
`[0, 1]`; it is `0` for an empty input space.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 33.4 (the right-hand side `sup_{x ≠ x'} TV(P_{Y|X=x},
P_{Y|X=x'})`; the diagonal terms vanish). -/
noncomputable def dobrushinCoeff (κ : Kernel X Y) [IsMarkovKernel κ] : ℝ :=
  ⨆ x, ⨆ x', totalVariationDist (κ x) (κ x')

/-- Every pair of rows is within `dobrushinCoeff κ` in total variation.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 33.4. -/
theorem totalVariationDist_le_dobrushinCoeff (κ : Kernel X Y) [IsMarkovKernel κ] (x x' : X) :
    totalVariationDist (κ x) (κ x') ≤ dobrushinCoeff κ := by
  have hb : ∀ x, BddAbove (Set.range fun x' => totalVariationDist (κ x) (κ x')) :=
    fun x => ⟨1, by rintro _ ⟨x', rfl⟩; exact totalVariationDist_le_one⟩
  have hb' : BddAbove (Set.range fun x => ⨆ x', totalVariationDist (κ x) (κ x')) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact Real.iSup_le (fun x' => totalVariationDist_le_one) zero_le_one
  exact (le_ciSup (hb x) x').trans (le_ciSup hb' x)

/-- `dobrushinCoeff κ` lies in `[0, 1]`.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Section 33.2 (`η_TV ≤ 1`). -/
theorem dobrushinCoeff_mem_Icc (κ : Kernel X Y) [IsMarkovKernel κ] :
    dobrushinCoeff κ ∈ Set.Icc 0 1 :=
  ⟨Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => totalVariationDist_nonneg,
    Real.iSup_le (fun _ => Real.iSup_le (fun _ => totalVariationDist_le_one) zero_le_one)
      zero_le_one⟩

/-- Averaging lemma: if `f x - f x' ≤ η` for all `x, x'` and the finite measures `μ₁`, `ν₁` have
the same total mass `t`, then `∫ f dμ₁ - ∫ f dν₁ ≤ η t`. -/
private lemma integral_sub_integral_le {μ₁ ν₁ : Measure X} [IsFiniteMeasure μ₁]
    [IsFiniteMeasure ν₁] {f : X → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C)
    {η : ℝ} (hη : ∀ x x', f x - f x' ≤ η) {t : ℝ} (ht : 0 < t) (hμ : μ₁.real Set.univ = t)
    (hν : ν₁.real Set.univ = t) :
    ∫ x, f x ∂μ₁ - ∫ x, f x ∂ν₁ ≤ η * t := by
  have hint : ∀ ρ : Measure X, [IsFiniteMeasure ρ] → Integrable f ρ := fun ρ _ =>
    Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hC x)
  -- inner integral: `∫ (f x - f x') dν₁(x') = t f x - ∫ f dν₁ ≤ η t`
  have hinner : ∀ x, t * f x - ∫ x', f x' ∂ν₁ ≤ η * t := by
    intro x
    have h1 : ∫ x', (f x - f x') ∂ν₁ = t * f x - ∫ x', f x' ∂ν₁ := by
      rw [integral_sub (integrable_const _) (hint ν₁), integral_const, hν, smul_eq_mul]
    have h2 : ∫ x', (f x - f x') ∂ν₁ ≤ ∫ _x', η ∂ν₁ :=
      integral_mono ((integrable_const _).sub (hint ν₁)) (integrable_const _) fun x' => hη x x'
    rw [integral_const, hν, smul_eq_mul] at h2
    linarith
  have houter : ∫ x, (t * f x - ∫ x', f x' ∂ν₁) ∂μ₁ ≤ ∫ _x, η * t ∂μ₁ :=
    integral_mono (((hint μ₁).const_mul t).sub (integrable_const _)) (integrable_const _) hinner
  rw [integral_sub ((hint μ₁).const_mul t) (integrable_const _), integral_const_mul,
    integral_const, integral_const, hμ, smul_eq_mul, smul_eq_mul] at houter
  have : t * (∫ x, f x ∂μ₁ - ∫ x, f x ∂ν₁) ≤ t * (η * t) := by nlinarith
  exact le_of_mul_le_mul_left this ht

/-- **Dobrushin's contraction**: for a Markov kernel `κ` and probability measures `μ`, `ν`,
`TV(κ ∘ₘ μ, κ ∘ₘ ν) ≤ η_TV(κ) · TV(μ, ν)` with `η_TV(κ) = sup_{x, x'} TV(κ x, κ x')`.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 33.4 (the inequality `η_TV ≤ sup_{x ≠ x'} TV(P_{Y|X=x},
P_{Y|X=x'})`); R. L. Dobrushin (1956). -/
theorem totalVariationDist_comp_le (κ : Kernel X Y) [IsMarkovKernel κ] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    totalVariationDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ dobrushinCoeff κ * totalVariationDist μ ν := by
  set t := totalVariationDist μ ν with ht_def
  have ht0 : 0 ≤ t := totalVariationDist_nonneg
  rcases ht0.lt_or_eq with htpos | ht0'
  swap
  · -- `TV(μ, ν) = 0`: the measures coincide
    have hμν : μ = ν := (totalVariationDist_eq_zero_iff).mp ht0'.symm
    subst hμν
    rw [totalVariationDist_self, ← ht0', mul_zero]
  obtain ⟨m, hm₀, hm₁, hmass⟩ := exists_le_le_measure_univ_eq μ ν
  have : IsFiniteMeasure m := isFiniteMeasure_of_le μ hm₀
  set μ₁ := μ - m
  set ν₁ := ν - m
  have : IsFiniteMeasure μ₁ := isFiniteMeasure_of_le μ Measure.sub_le
  have : IsFiniteMeasure ν₁ := isFiniteMeasure_of_le ν Measure.sub_le
  have hμ : μ = μ₁ + m := (Measure.sub_add_cancel_of_le hm₀).symm
  have hν : ν = ν₁ + m := (Measure.sub_add_cancel_of_le hm₁).symm
  have hmreal : m.real Set.univ = 1 - t := by
    rw [measureReal_def, hmass, ENNReal.toReal_ofReal (sub_nonneg.mpr totalVariationDist_le_one)]
  have hμ₁ : μ₁.real Set.univ = t := by
    have := congrArg (fun ρ : Measure X => ρ.real Set.univ) hμ
    rw [probReal_univ, measureReal_add_apply] at this
    linarith
  have hν₁ : ν₁.real Set.univ = t := by
    have := congrArg (fun ρ : Measure X => ρ.real Set.univ) hν
    rw [probReal_univ, measureReal_add_apply] at this
    linarith
  -- the comparison on a fixed measurable set
  have hcomp : ∀ (ρ : Measure X) [IsFiniteMeasure ρ] {B : Set Y}, MeasurableSet B →
      (κ ∘ₘ ρ).real B = ∫ x, (κ x).real B ∂ρ := by
    intro ρ _ B hB
    rw [measureReal_def, Measure.bind_apply hB κ.aemeasurable]
    exact (integral_toReal (κ.measurable_coe hB).aemeasurable
      (Filter.Eventually.of_forall fun x => measure_lt_top _ _)).symm
  apply ciSup_le
  rintro ⟨B, hB⟩
  change |(κ ∘ₘ μ).real B - (κ ∘ₘ ν).real B| ≤ dobrushinCoeff κ * t
  have hf : Measurable fun x => (κ x).real B := (κ.measurable_coe hB).ennreal_toReal
  have hC : ∀ x, |(κ x).real B| ≤ 1 := fun x => by
    rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one
  have hη : ∀ x x', (κ x).real B - (κ x').real B ≤ dobrushinCoeff κ := fun x x' =>
    (le_abs_self _).trans ((abs_sub_le_totalVariationDist hB).trans
      (totalVariationDist_le_dobrushinCoeff κ x x'))
  have e₁ : (κ ∘ₘ μ).real B - (κ ∘ₘ ν).real B
      = ∫ x, (κ x).real B ∂μ₁ - ∫ x, (κ x).real B ∂ν₁ := by
    rw [hμ, hν, Measure.comp_add, Measure.comp_add, measureReal_add_apply, measureReal_add_apply,
      hcomp μ₁ hB, hcomp ν₁ hB]
    ring
  rw [e₁, abs_sub_le_iff]
  exact ⟨integral_sub_integral_le hf hC hη htpos hμ₁ hν₁,
    integral_sub_integral_le hf hC hη htpos hν₁ hμ₁⟩

/-- **Data-processing inequality for total variation**: a Markov kernel does not increase the
total variation distance, `TV(κ ∘ₘ μ, κ ∘ₘ ν) ≤ TV(μ, ν)`.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 7.4 (data processing for f-divergences, `f(x) = ½|x - 1|`). -/
theorem totalVariationDist_comp_le_self (κ : Kernel X Y) [IsMarkovKernel κ] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    totalVariationDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ totalVariationDist μ ν := by
  refine (totalVariationDist_comp_le κ μ ν).trans ?_
  have h := dobrushinCoeff_mem_Icc κ
  have := totalVariationDist_nonneg (μ := μ) (ν := ν)
  nlinarith [h.1, h.2]

/-- **Sharpness of Dobrushin's coefficient**: if singletons of `X` are measurable and a constant
`c ≥ 0` satisfies `TV(κ ∘ₘ μ, κ ∘ₘ ν) ≤ c · TV(μ, ν)` for all probability measures `μ`, `ν`, then
`dobrushinCoeff κ ≤ c`: the inequality for the point masses `δ_x` and `δ_{x'}` gives
`TV(κ x, κ x') ≤ c` for every pair, so `c` bounds their supremum. Together with
`totalVariationDist_comp_le`, `dobrushinCoeff κ` is therefore the least contraction constant
`η_TV(κ)`, although no pair of point masses need attain it.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 33.4 (the inequality `η_TV ≥ sup_{x ≠ x'} TV(P_{Y|X=x},
P_{Y|X=x'})`, from `P_X = δ_x`, `Q_X = δ_{x'}`). -/
theorem dobrushinCoeff_le_of_forall [MeasurableSingletonClass X] (κ : Kernel X Y)
    [IsMarkovKernel κ] {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      totalVariationDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ c * totalVariationDist μ ν) :
    dobrushinCoeff κ ≤ c := by
  classical
  refine Real.iSup_le (fun x => Real.iSup_le (fun x' => ?_) hc) hc
  have hx := h (Measure.dirac x) (Measure.dirac x')
  have e : totalVariationDist (κ ∘ₘ Measure.dirac x) (κ ∘ₘ Measure.dirac x')
      = totalVariationDist (κ x) (κ x') := by
    simp only [totalVariationDist, Measure.dirac_bind κ.measurable]
  rw [e] at hx
  by_cases hxx : x = x'
  · subst hxx
    rw [totalVariationDist_self]; exact hc
  · simp only [totalVariationDist_dirac, hxx, ↓reduceIte, mul_one] at hx
    exact hx

end MathlibExt.InformationTheory.DobrushinContraction
