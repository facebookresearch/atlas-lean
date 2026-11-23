/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.DobrushinContraction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import MathlibExt.InformationTheory.FiniteEntropy

/-!
# Strong data processing for Kullback-Leibler divergence

For a Markov kernel `κ` between finite alphabets and probability measures `μ`, `ν` on its input,

`D(κ ∘ μ ‖ κ ∘ ν) ≤ η_TV(κ) · D(μ ‖ ν)`,

where `η_TV(κ) = dobrushinCoeff κ = sup_{x, x'} TV(κ x, κ x')` is Dobrushin's coefficient from
`MathlibExt.InformationTheory.DobrushinContraction`. In other words, the contraction coefficient
`η_KL(κ)` of the Kullback-Leibler divergence is at most `η_TV(κ)`. Both divergences take values
in `[0, ∞]`. If `μ` is not absolutely continuous with respect to `ν`, the right-hand side is `∞`
unless `η_TV(κ) = 0`; in that case all rows of `κ` coincide and the left-hand side is `0`.

## Proof outline

The proof follows the route through hockey-stick divergences of Cohen, Iwasa, Rautu, Ruskai,
Seneta and Zbăganu. They prove the inequality for strictly positive probability vectors and
row-allowable stochastic matrices (their Theorem 3.1) by reducing a convex function to affine
functions and the functions `|x - c|` (their Lemma 3.3). Polyanskiy and Wu sketch the same route
for their Theorem 33.6(a). The statement here allows zero probabilities and any Markov kernel.

1. *Integral representation.* Taylor's formula with integral remainder for
   `klFun t = t log t + 1 - t`, whose second derivative is `1 / t` and which vanishes with its
   derivative at `1`, gives for `t ≥ 0`
   `klFun t = ∫_{(1, ∞)} (t - γ)⁺ / γ dγ + ∫_{(0, 1]} (γ - t)⁺ / γ dγ`.
   On a finite alphabet with `μ ≪ ν`, `D(μ ‖ ν) = ∑_a ν{a} klFun (μ{a} / ν{a})`, hence
   `D(μ ‖ ν) = ∫_{(1, ∞)} E_γ(μ, ν) / γ dγ + ∫_{(0, 1]} F_γ(μ, ν) / γ dγ`, where
   `E_γ(μ, ν) = ∑_a (μ{a} - γ ν{a})⁺` and `F_γ(μ, ν) = ∑_a (γ ν{a} - μ{a})⁺`.
2. *Contraction of the hockey-stick divergences.* If `a : X → ℝ` satisfies `∑_x a x ≤ 0`, then
   `∑_y (∑_x a x κ x {y})⁺ ≤ η_TV(κ) ∑_x (a x)⁺`. Indeed, the left-hand side is
   `∑_x a x κ x (B)` for the set `B` of outputs where the inner sum is positive. Subtracting
   `c ∑_x a x ≤ 0` with `c = min_x κ x (B)` leaves the weights `κ x (B) - c`, which lie in
   `[0, η_TV(κ)]`. Taking `a = μ - γ ν` for `γ ≥ 1` and `a = γ ν - μ` for `γ ≤ 1` gives
   `E_γ(κ ∘ μ, κ ∘ ν) ≤ η_TV(κ) E_γ(μ, ν)` and `F_γ(κ ∘ μ, κ ∘ ν) ≤ η_TV(κ) F_γ(μ, ν)`.
3. Integrating these bounds against `dγ / γ` proves the inequality.

## Main results

* `klDiv_comp_le_dobrushinCoeff_mul`: `D(κ ∘ₘ μ ‖ κ ∘ₘ ν) ≤ η_TV(κ) · D(μ ‖ ν)` for a Markov
  kernel `κ` between finite alphabets with measurable singletons.

## Implementation notes

The theorem keeps the full name it had in the former wanted module, so its namespace still reads
`StrongDataProcessingWanted`.

## References

* Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University
  Press, 2025, Theorem 33.6(a) (`η_f ≤ η_TV` for every `f`; its proof sketch goes through the
  `E_γ` divergences).
* J. E. Cohen, Y. Iwasa, G. Rautu, M. B. Ruskai, E. Seneta and G. Zbăganu, Relative entropy under
  mappings by stochastic matrices, *Linear Algebra Appl.* 179 (1993), 211-235, Theorem 3.1 and
  Lemma 3.3.
* J. E. Cohen, J. H. B. Kemperman and G. Zbăganu, *Comparisons of Stochastic Matrices with
  Applications in Information Theory, Statistics, Economics and Population Sciences*,
  Birkhäuser, 1998.
-/

namespace MathlibExt.InformationTheory.StrongDataProcessingWanted

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.InformationTheory.DobrushinContraction
open MathlibExt.Probability.TotalVariationDistance MathlibExt.InformationTheory.MeasurePinsker
open Set Real

/-! ### The integral representation of `klFun` -/

/-- For `f` interval integrable on `[a, b]` and nonnegative on `(a, b]`, the Lebesgue integral of
`ofReal ∘ f` over `(a, b]` is `ofReal` of the interval integral of `f`. -/
private lemma setLIntegral_Ioc_ofReal {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (h0 : ∀ γ ∈ Ioc a b, 0 ≤ f γ) :
    ∫⁻ γ in Ioc a b, ENNReal.ofReal (f γ) = ENNReal.ofReal (∫ γ in a..b, f γ) := by
  rw [intervalIntegral.integral_of_le hab, ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hf)
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall h0))]

/-- `∫_{(1, t]} (t - γ) / γ dγ = klFun t` for `t ≥ 1`. -/
private lemma setLIntegral_Ioc_one_eq_klFun {t : ℝ} (ht : 1 ≤ t) :
    ∫⁻ γ in Ioc 1 t, ENNReal.ofReal ((t - γ) / γ) =
      ENNReal.ofReal (_root_.InformationTheory.klFun t) := by
  have hne : ∀ γ ∈ uIcc (1 : ℝ) t, γ ≠ 0 := fun γ hγ => by
    rw [uIcc_of_le ht] at hγ
    exact (zero_lt_one.trans_le hγ.1).ne'
  have hint : IntervalIntegrable (fun γ => (t - γ) / γ) volume 1 t :=
    ((continuousOn_const.sub continuousOn_id).div continuousOn_id hne).intervalIntegrable
  have hderiv : ∀ γ ∈ uIcc (1 : ℝ) t,
      HasDerivAt (fun γ => t * log γ - γ) ((t - γ) / γ) γ := fun γ hγ =>
    (((hasDerivAt_log (hne γ hγ)).const_mul t).sub (hasDerivAt_id' γ)).congr_deriv
      (by field_simp [hne γ hγ])
  rw [setLIntegral_Ioc_ofReal ht hint fun γ hγ =>
      div_nonneg (sub_nonneg.2 hγ.2) (zero_le_one.trans hγ.1.le),
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  congr 1
  simp only [log_one, mul_zero, zero_sub, _root_.InformationTheory.klFun_apply]
  ring

/-- `∫_{(t, 1]} (γ - t) / γ dγ = klFun t` for `0 ≤ t ≤ 1`. -/
private lemma setLIntegral_Ioc_eq_klFun {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫⁻ γ in Ioc t 1, ENNReal.ofReal ((γ - t) / γ) =
      ENNReal.ofReal (_root_.InformationTheory.klFun t) := by
  rcases ht0.eq_or_lt with rfl | ht0
  · -- `t = 0`: the integrand is `1`
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => 1) fun γ hγ => by
        simp only [sub_zero, div_self hγ.1.ne', ENNReal.ofReal_one],
      setLIntegral_const, one_mul, Real.volume_Ioc, sub_zero,
      _root_.InformationTheory.klFun_zero]
  have hne : ∀ γ ∈ uIcc t 1, γ ≠ 0 := fun γ hγ => by
    rw [uIcc_of_le ht1] at hγ
    exact (ht0.trans_le hγ.1).ne'
  have hint : IntervalIntegrable (fun γ => (γ - t) / γ) volume t 1 :=
    ((continuousOn_id.sub continuousOn_const).div continuousOn_id hne).intervalIntegrable
  have hderiv : ∀ γ ∈ uIcc t 1,
      HasDerivAt (fun γ => γ - t * log γ) ((γ - t) / γ) γ := fun γ hγ =>
    ((hasDerivAt_id' γ).sub ((hasDerivAt_log (hne γ hγ)).const_mul t)).congr_deriv
      (by field_simp [hne γ hγ])
  rw [setLIntegral_Ioc_ofReal ht1 hint fun γ hγ =>
      div_nonneg (sub_nonneg.2 hγ.1.le) (ht0.trans hγ.1).le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  congr 1
  simp only [log_one, mul_zero, sub_zero, _root_.InformationTheory.klFun_apply]
  ring

/-- The Lebesgue integral of `ofReal ((g γ)⁺ / γ)` over a measurable set where `g ≤ 0` is `0`. -/
private lemma setLIntegral_ofReal_div_eq_zero {s : Set ℝ} (hs : MeasurableSet s) {g : ℝ → ℝ}
    (hg : ∀ γ ∈ s, g γ ≤ 0) :
    ∫⁻ γ in s, ENNReal.ofReal (max (g γ) 0 / γ) = 0 := by
  rw [setLIntegral_congr_fun hs (g := fun _ => 0) fun γ hγ => by
    simp only [max_eq_right (hg γ hγ), zero_div, ENNReal.ofReal_zero]]
  exact lintegral_zero

/-- **Hockey-stick representation of `klFun`**: for `t ≥ 0`,
`klFun t = ∫_{(1, ∞)} (t - γ)⁺ / γ dγ + ∫_{(0, 1]} (γ - t)⁺ / γ dγ`. -/
private lemma lintegral_add_lintegral_eq_klFun {t : ℝ} (ht : 0 ≤ t) :
    (∫⁻ γ in Ioi 1, ENNReal.ofReal (max (t - γ) 0 / γ)) +
      ∫⁻ γ in Ioc 0 1, ENNReal.ofReal (max (γ - t) 0 / γ) =
      ENNReal.ofReal (_root_.InformationTheory.klFun t) := by
  rcases le_or_gt 1 t with h1 | h1
  · rw [setLIntegral_ofReal_div_eq_zero measurableSet_Ioc fun γ hγ => by linarith [hγ.2],
      add_zero, ← Ioc_union_Ioi_eq_Ioi h1, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same,
      setLIntegral_ofReal_div_eq_zero measurableSet_Ioi fun γ hγ => by linarith [mem_Ioi.1 hγ],
      add_zero, ← setLIntegral_Ioc_one_eq_klFun h1]
    exact setLIntegral_congr_fun measurableSet_Ioc fun γ hγ => by
      simp only [max_eq_left (sub_nonneg.2 hγ.2)]
  · rw [setLIntegral_ofReal_div_eq_zero measurableSet_Ioi fun γ hγ => by
        linarith [mem_Ioi.1 hγ], zero_add, ← Ioc_union_Ioc_eq_Ioc ht h1.le,
      lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioi_same.mono_right Ioc_subset_Ioi_self),
      setLIntegral_ofReal_div_eq_zero measurableSet_Ioc fun γ hγ => by linarith [hγ.2],
      zero_add, ← setLIntegral_Ioc_eq_klFun ht h1.le]
    exact setLIntegral_congr_fun measurableSet_Ioc fun γ hγ => by
      simp only [max_eq_left (sub_nonneg.2 hγ.1.le)]

/-- The representation of `q · klFun (p / q)` by the hockey-stick integrands `(p - γ q)⁺` and
`(γ q - p)⁺`, for `p, q ≥ 0` with `p = 0` whenever `q = 0`. -/
private lemma ofReal_mul_klFun_div_eq {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : q = 0 → p = 0) :
    ENNReal.ofReal (q * _root_.InformationTheory.klFun (p / q)) =
      (∫⁻ γ in Ioi 1, ENNReal.ofReal (max (p - γ * q) 0 / γ)) +
        ∫⁻ γ in Ioc 0 1, ENNReal.ofReal (max (γ * q - p) 0 / γ) := by
  rcases hq.eq_or_lt with rfl | hq0
  · simp [hpq rfl]
  have hscale : ∀ c : ℝ, ∀ γ : ℝ, ENNReal.ofReal (max (q * c) 0 / γ) =
      ENNReal.ofReal q * ENNReal.ofReal (max c 0 / γ) := fun c γ => by
    rw [← ENNReal.ofReal_mul hq, ← mul_div_assoc, mul_max_of_nonneg _ _ hq, mul_zero]
  have h1 : ∀ γ : ℝ, p - γ * q = q * (p / q - γ) := fun γ => by field_simp
  have h2 : ∀ γ : ℝ, γ * q - p = q * (γ - p / q) := fun γ => by field_simp
  simp_rw [h1, h2, hscale]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_add,
    lintegral_add_lintegral_eq_klFun (div_nonneg hp hq), ENNReal.ofReal_mul hq]

/-! ### Kullback-Leibler divergence on a finite alphabet -/

/-- The masses of the points of a finite alphabet add up to `1` under a probability measure. -/
private lemma sum_measureReal_singleton_eq_one {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ρ : Measure α) [IsProbabilityMeasure ρ] :
    ∑ a, ρ.real {a} = 1 := by
  rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]

/-- If `μ ≪ ν` are finite measures, a point of `ν`-mass `0` has `μ`-mass `0`. -/
private lemma measureReal_singleton_eq_zero_of_ac {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) {a : α}
    (ha : ν.real {a} = 0) : μ.real {a} = 0 :=
  (measureReal_eq_zero_iff).2 (hμν ((measureReal_eq_zero_iff).1 ha))

/-- On a finite alphabet, `D(μ ‖ ν) = ∑_a ν{a} klFun (μ{a} / ν{a})` for probability measures
`μ ≪ ν`. -/
private lemma klDiv_eq_sum_ofReal {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : μ ≪ ν) :
    _root_.InformationTheory.klDiv μ ν = ∑ a, ENNReal.ofReal
      (ν.real {a} * _root_.InformationTheory.klFun (μ.real {a} / ν.real {a})) := by
  have hne := _root_.InformationTheory.klDiv_ne_top hμν Integrable.of_finite
  rw [← ENNReal.ofReal_toReal hne, _root_.InformationTheory.toReal_klDiv_eq_sum hμν (by simp),
    ← ENNReal.ofReal_sum_of_nonneg fun a _ => mul_nonneg measureReal_nonneg
      (_root_.InformationTheory.klFun_nonneg (div_nonneg measureReal_nonneg measureReal_nonneg))]
  congr 1
  have hterm : ∀ a, ν.real {a} * _root_.InformationTheory.klFun (μ.real {a} / ν.real {a}) =
      μ.real {a} * log (μ.real {a} / ν.real {a}) + ν.real {a} - μ.real {a} := fun a => by
    by_cases ha : ν.real {a} = 0
    · simp [ha, measureReal_singleton_eq_zero_of_ac hμν ha]
    · rw [_root_.InformationTheory.klFun_apply]
      field_simp
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_measureReal_singleton_eq_one, add_sub_cancel_right]

/-- On finite alphabets, `(κ ∘ₘ μ){y} = ∑_x μ{x} κ x {y}`. -/
private lemma comp_real_singleton {X Y : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (κ : Kernel X Y) [IsMarkovKernel κ] (μ : Measure X) [IsFiniteMeasure μ] (y : Y) :
    (κ ∘ₘ μ).real {y} = ∑ x, μ.real {x} * (κ x).real {y} := by
  rw [measureReal_def, Measure.bind_apply (measurableSet_singleton y) κ.aemeasurable,
    lintegral_fintype, ENNReal.toReal_sum fun x _ => ENNReal.mul_ne_top (measure_ne_top _ _)
      (measure_ne_top _ _)]
  exact Finset.sum_congr rfl fun x _ => by rw [ENNReal.toReal_mul, mul_comm]; rfl

/-- **Hockey-stick representation of the Kullback-Leibler divergence** on a finite alphabet, for
probability measures `μ ≪ ν`: `D(μ ‖ ν)` is
`∫_{(1, ∞)} ∑_a (μ{a} - γ ν{a})⁺ / γ dγ + ∫_{(0, 1]} ∑_a (γ ν{a} - μ{a})⁺ / γ dγ`. -/
private lemma klDiv_eq_lintegral_add_lintegral {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : μ ≪ ν) :
    _root_.InformationTheory.klDiv μ ν =
      (∫⁻ γ in Ioi 1, ENNReal.ofReal ((∑ a, max (μ.real {a} - γ * ν.real {a}) 0) / γ)) +
        ∫⁻ γ in Ioc 0 1, ENNReal.ofReal ((∑ a, max (γ * ν.real {a} - μ.real {a}) 0) / γ) := by
  rw [klDiv_eq_sum_ofReal hμν, Finset.sum_congr rfl fun a _ =>
      ofReal_mul_klFun_div_eq measureReal_nonneg measureReal_nonneg
        (measureReal_singleton_eq_zero_of_ac hμν),
    Finset.sum_add_distrib, ← lintegral_finsetSum _ fun a _ => by fun_prop,
    ← lintegral_finsetSum _ fun a _ => by fun_prop]
  congr 1
  · refine setLIntegral_congr_fun measurableSet_Ioi fun γ hγ => ?_
    have hγ0 : 0 < γ := zero_lt_one.trans hγ
    rw [Finset.sum_div, ENNReal.ofReal_sum_of_nonneg fun a _ =>
      div_nonneg (le_max_right _ _) hγ0.le]
  · refine setLIntegral_congr_fun measurableSet_Ioc fun γ hγ => ?_
    rw [Finset.sum_div, ENNReal.ofReal_sum_of_nonneg fun a _ =>
      div_nonneg (le_max_right _ _) hγ.1.le]

/-! ### Contraction of the hockey-stick divergences -/

/-- If `∑_x a x ≤ 0`, then `∑_y (∑_x a x κ x {y})⁺ ≤ η_TV(κ) ∑_x (a x)⁺`. -/
private lemma sum_max_le_dobrushinCoeff_mul {X Y : Type*} [Fintype X] [Fintype Y]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (κ : Kernel X Y) [IsMarkovKernel κ] (a : X → ℝ) (ha : ∑ x, a x ≤ 0) :
    ∑ y, max (∑ x, a x * (κ x).real {y}) 0 ≤ dobrushinCoeff κ * ∑ x, max (a x) 0 := by
  rcases isEmpty_or_nonempty X with hX | hX
  · simp
  set B : Finset Y := Finset.univ.filter fun y => 0 < ∑ x, a x * (κ x).real {y} with hB_def
  set k : X → ℝ := fun x => (κ x).real (B : Set Y) with hk_def
  obtain ⟨x₀, hx₀⟩ := Finite.exists_min k
  have hpos : ∑ y, max (∑ x, a x * (κ x).real {y}) 0 = ∑ x, a x * k x := by
    rw [hk_def]
    simp only [← sum_measureReal_singleton, Finset.mul_sum]
    rw [Finset.sum_comm, hB_def, Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs with h
    · exact max_eq_left h.le
    · exact max_eq_right (not_lt.1 h)
  have hk : ∀ x, k x - k x₀ ≤ dobrushinCoeff κ := fun x =>
    (le_abs_self _).trans ((abs_sub_le_totalVariationDist B.measurableSet).trans
      (totalVariationDist_le_dobrushinCoeff κ x x₀))
  have hk₀ : 0 ≤ k x₀ := measureReal_nonneg
  rw [hpos]
  calc ∑ x, a x * k x = ∑ x, a x * (k x - k x₀) + k x₀ * ∑ x, a x := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ ≤ ∑ x, a x * (k x - k x₀) := add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hk₀ ha)
    _ ≤ ∑ x, max (a x) 0 * dobrushinCoeff κ := Finset.sum_le_sum fun x _ =>
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sub_nonneg.2 (hx₀ x))).trans
          (mul_le_mul_of_nonneg_left (hk x) (le_max_right _ _))
    _ = dobrushinCoeff κ * ∑ x, max (a x) 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- **Strong data-processing inequality for KL divergence** (`η_KL ≤ η_TV`). For a Markov kernel
`κ` between finite alphabets with measurable singletons and probability measures `μ`, `ν`,
`D(κ ∘ₘ μ ‖ κ ∘ₘ ν) ≤ η_TV(κ) · D(μ ‖ ν)`, where `η_TV(κ) = dobrushinCoeff κ`.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 33.6(a) with `f(x) = x log x`; J. E. Cohen, J. H. B. Kemperman
and G. Zbăganu (1998). -/
public theorem klDiv_comp_le_dobrushinCoeff_mul {X Y : Type*} [Finite X] [Finite Y]
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] (κ : Kernel X Y) [IsMarkovKernel κ] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    _root_.InformationTheory.klDiv (κ ∘ₘ μ) (κ ∘ₘ ν) ≤
      ENNReal.ofReal (dobrushinCoeff κ) * _root_.InformationTheory.klDiv μ ν := by
  have := Fintype.ofFinite X
  have := Fintype.ofFinite Y
  have hη0 : 0 ≤ dobrushinCoeff κ := (dobrushinCoeff_mem_Icc κ).1
  rcases hη0.eq_or_lt with hη | hη
  · -- `η_TV(κ) = 0`: all rows of `κ` coincide, so both outputs are the common row
    obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure μ
    have hrow : (κ : X → Measure Y) = fun _ => κ x₀ := funext fun x =>
      totalVariationDist_eq_zero_iff.1 (le_antisymm
        (hη ▸ totalVariationDist_le_dobrushinCoeff κ x x₀) totalVariationDist_nonneg)
    have hcomp : ∀ ρ : Measure X, [IsProbabilityMeasure ρ] → κ ∘ₘ ρ = κ x₀ := fun ρ _ => by
      rw [hrow, Measure.bind_const, measure_univ, one_smul]
    rw [hcomp μ, hcomp ν, _root_.InformationTheory.klDiv_self]
    exact zero_le
  by_cases hμν : μ ≪ ν
  swap
  · rw [_root_.InformationTheory.klDiv_of_not_ac hμν,
      ENNReal.mul_top (ENNReal.ofReal_pos.2 hη).ne']
    exact le_top
  -- the hockey-stick integrands of the outputs are linear images of those of the inputs
  have hlin : ∀ (c d : ℝ) (y : Y), ∑ x, (c * μ.real {x} + d * ν.real {x}) * (κ x).real {y} =
      c * (κ ∘ₘ μ).real {y} + d * (κ ∘ₘ ν).real {y} := fun c d y => by
    simp only [comp_real_singleton, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have hmass : ∀ c d : ℝ, ∑ x, (c * μ.real {x} + d * ν.real {x}) = c + d := fun c d => by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_measureReal_singleton_eq_one, sum_measureReal_singleton_eq_one, mul_one, mul_one]
  have hstep : ∀ {γ A B : ℝ}, 0 < γ → A ≤ dobrushinCoeff κ * B →
      ENNReal.ofReal (A / γ) ≤ ENNReal.ofReal (dobrushinCoeff κ) * ENNReal.ofReal (B / γ) :=
    fun hγ h => by
      rw [← ENNReal.ofReal_mul hη0, ← mul_div_assoc]
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right h hγ.le)
  rw [klDiv_eq_lintegral_add_lintegral (hμν.comp_right κ), klDiv_eq_lintegral_add_lintegral hμν,
    mul_add, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine add_le_add (setLIntegral_mono' measurableSet_Ioi fun γ hγ => ?_)
    (setLIntegral_mono' measurableSet_Ioc fun γ hγ => ?_)
  · -- `γ > 1`: the vector `μ - γ ν` has total mass `1 - γ ≤ 0`
    have hγ1 : 1 < γ := hγ
    refine hstep (zero_lt_one.trans hγ1) ?_
    have h := sum_max_le_dobrushinCoeff_mul κ (fun x => 1 * μ.real {x} + -γ * ν.real {x})
      (by rw [hmass]; linarith)
    simp only [hlin] at h
    simpa [one_mul, neg_mul, ← sub_eq_add_neg] using h
  · -- `0 < γ ≤ 1`: the vector `γ ν - μ` has total mass `γ - 1 ≤ 0`
    refine hstep hγ.1 ?_
    have h := sum_max_le_dobrushinCoeff_mul κ (fun x => -1 * μ.real {x} + γ * ν.real {x})
      (by rw [hmass]; linarith [hγ.2])
    simp only [hlin] at h
    simpa [neg_one_mul, neg_add_eq_sub] using h

end

end MathlibExt.InformationTheory.StrongDataProcessingWanted
