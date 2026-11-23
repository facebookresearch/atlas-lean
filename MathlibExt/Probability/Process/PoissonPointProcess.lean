/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Probability.Distributions.Poisson.Basic

import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Poisson point processes with finite intensity on a general measurable space

Let `E` be any measurable space and `μ` a finite measure on `E` (the intensity). The Poisson
point process with intensity `μ` is the random counting measure `η = ∑_{i < K} δ_{X_i}`, where
`K` has the Poisson law of mean `μ(E)` and, given `K = n`, the points `X_1, …, X_n` are i.i.d.
with law `μ / μ(E)` (the mixed binomial construction, Last–Penrose Prop. 3.5). We record its
law, a probability measure on `Measure E`, as
`poissonPointProcess μ = ∑_n e^{-μ(E)} / n! • (μ^{⊗n}).map (x ↦ ∑_{i < n} δ_{x_i})`,
which is the same measure because `e^{-μ(E)} μ(E)^n / n! • (μ/μ(E))^{⊗n} = e^{-μ(E)} / n! • μ^{⊗n}`.

## Main definitions

* `poissonPointProcess μ`: the law of the Poisson point process with finite intensity `μ`.

## Main results

* `map_apply_eq_poissonMeasure`: the count `η(B)` of a measurable set has the Poisson law of
  mean `μ(B)`.
* `map_apply_pi`: the counts of pairwise disjoint measurable sets are independent Poisson
  variables, so `η` is a Poisson process with intensity `μ` in the sense of Last–Penrose
  Def. 3.1 (their Prop. 3.5).
* `lintegral_lintegral`: **Campbell's formula** `E ∫ f dη = ∫ f dμ`.
* `integral_exp_neg`: the **Laplace functional** `E exp(-∫ f dη) = exp(-∫ (1 - e^{-f}) dμ)`.
* `lintegral_lintegral_mecke`: the **Mecke equation**
  `E ∫ h(x, η) η(dx) = ∫ E h(x, η + δ_x) μ(dx)`.
* `map_map`: **mapping theorem** — the image of `η` under a measurable map `T` is the Poisson
  point process with intensity `μ ∘ T⁻¹`.

## Scope

Only finite intensities are treated. Not covered: the σ-finite case (a countable superposition
of independent finite pieces), the restriction theorem in its process-level form (the
restrictions to disjoint sets are independent Poisson processes; recorded as wanted in
`WantedExt.Probability.Process.PoissonPointProcessWanted`), and position-dependent marking,
which needs a product of kernels. Uniqueness of the law of a Poisson process given its
intensity (Last–Penrose Prop. 3.2) is not formalized, so the results are stated for this
construction.

## References

* G. Last, M. Penrose, *Lectures on the Poisson Process*, IMS Textbooks, Cambridge University
  Press (2017), Def. 3.1, Prop. 2.7, Prop. 3.5, Thm. 3.9, Thm. 4.1, Thm. 5.1.
* J. F. C. Kingman, *Poisson Processes*, Oxford University Press (1993).
* J. Mecke, Stationäre zufällige Maße auf lokalkompakten Abelschen Gruppen,
  *Z. Wahrscheinlichkeitstheorie verw. Gebiete* 9 (1967), 36–58.
-/

@[expose] public section

open Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Nat

namespace MathlibExt.Probability.PoissonPointProcess

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]

/-- The counting measure `∑_{i < n} δ_{x_i}` of a finite tuple of points. -/
noncomputable def countingMeasure {n : ℕ} (x : Fin n → E) : Measure E :=
  ∑ i, Measure.dirac (x i)

/-- The law of the Poisson point process with finite intensity `μ` on `E`:
`∑_n e^{-μ(E)} / n! • (μ^{⊗n}).map countingMeasure`, a probability measure on `Measure E`
(Last–Penrose Prop. 3.5, mixed binomial construction). -/
noncomputable def poissonPointProcess (μ : Measure E) [IsFiniteMeasure μ] :
    Measure (Measure E) :=
  Measure.sum fun n : ℕ => ENNReal.ofReal (Real.exp (-μ.real univ) / n !) •
    (Measure.pi fun _ : Fin n => μ).map countingMeasure

/-- `(∑ δ_{x_i})(s) = #{i | x_i ∈ s}`, as a sum of indicators. -/
theorem countingMeasure_apply {n : ℕ} (x : Fin n → E) {s : Set E} (hs : MeasurableSet s) :
    countingMeasure x s = ∑ i, s.indicator 1 (x i) := by
  simp [countingMeasure, Measure.dirac_apply' _ hs]

/-- The counting measure of a tuple depends measurably on the tuple. -/
theorem measurable_countingMeasure (n : ℕ) :
    Measurable (countingMeasure : (Fin n → E) → Measure E) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [countingMeasure_apply _ hs]
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_one.indicator hs).comp (measurable_pi_apply i)

/-- `∫ f d(∑ δ_{x_i}) = ∑ f(x_i)`. -/
theorem lintegral_countingMeasure {n : ℕ} (x : Fin n → E) {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(countingMeasure x) = ∑ i, f (x i) := by
  simp [countingMeasure, lintegral_dirac' _ hf]

/-- The Poisson weights sum to one: `∑_n e^{-μ(E)} μ(E)^n / n! = 1`. -/
theorem tsum_coeff_mul_pow (μ : Measure E) [IsFiniteMeasure μ] :
    ∑' n : ℕ, ENNReal.ofReal (Real.exp (-μ.real univ) / n !) * μ univ ^ n = 1 := by
  have hμ : μ univ = ENNReal.ofReal (μ.real univ) :=
    (ofReal_measureReal (measure_ne_top _ _)).symm
  have h := hasSum_one_poissonMeasure (μ univ).toNNReal
  have hc : ((μ univ).toNNReal : ℝ) = μ.real univ := rfl
  rw [hc] at h
  simp_rw [hμ, ← ENNReal.ofReal_pow measureReal_nonneg,
    ← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _))]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    (h.summable.congr fun n => by ring), ← ENNReal.ofReal_one, ← h.tsum_eq]
  exact congrArg ENNReal.ofReal (tsum_congr fun n => by ring)

/-- `∫ f(x_i) dμ^{⊗n}(x) = μ(E)^{n-1} ∫ f dμ`. -/
theorem lintegral_pi_eval (μ : Measure E) [IsFiniteMeasure μ] {n : ℕ} (i : Fin n)
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f (x i) ∂(Measure.pi fun _ : Fin n => μ) = μ univ ^ (n - 1) * ∫⁻ y, f y ∂μ := by
  rw [← lintegral_map hf (measurable_pi_apply i)]
  change ∫⁻ y, f y ∂((Measure.pi fun _ : Fin n => μ).map (Function.eval i)) = _
  rw [Measure.pi_map_eval, lintegral_smul_measure, Finset.prod_const, Finset.card_erase_of_mem
    (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- The image of `∑ δ_{x_i}` under `T` is `∑ δ_{T(x_i)}`. -/
theorem countingMeasure_comp {n : ℕ} (x : Fin n → E) {T : E → F} (hT : Measurable T) :
    countingMeasure (T ∘ x) = (countingMeasure x).map T := by
  ext s hs
  rw [Measure.map_apply hT hs, countingMeasure_apply _ hs, countingMeasure_apply _ (hT hs)]
  rfl

variable (μ : Measure E) [IsFiniteMeasure μ]

/-- The Poisson point process law is a probability measure. -/
instance isProbabilityMeasure_poissonPointProcess :
    IsProbabilityMeasure (poissonPointProcess μ) := by
  constructor
  rw [poissonPointProcess, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul]
  simp_rw [Measure.map_apply (measurable_countingMeasure _) MeasurableSet.univ,
    preimage_univ, Measure.pi_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact tsum_coeff_mul_pow μ

/-- The count `⌊η(B)⌋` as a natural number (equal to `η(B)` on counting measures). -/
private noncomputable def natCount (B : Set E)
    (η : Measure E) : ℕ := ⌊(η B).toReal⌋₊

private theorem measurable_natCount {B : Set E}
    (hB : MeasurableSet B) : Measurable (natCount B) :=
  (Measure.measurable_coe hB).ennreal_toReal.nat_floor

private theorem countingMeasure_apply_nat {n : ℕ}
    (x : Fin n → E) {B : Set E} [DecidablePred (· ∈ B)] (hB : MeasurableSet B) :
    countingMeasure x B = ((∑ i, if x i ∈ B then 1 else 0 : ℕ) : ℝ≥0∞) := by
  classical
  simp only [countingMeasure, Measure.finsetSum_apply, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.dirac_apply' _ hB]
  by_cases hi : x i ∈ B <;> simp [hi, Set.indicator]

private theorem count_charFun {B : Set E} (hB : MeasurableSet B) (t : ℝ) :
    charFun (((poissonPointProcess μ).map (natCount B)).map (Nat.cast : ℕ → ℝ)) t =
      Complex.exp ((μ.real B : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) - 1)) := by
  classical
  let z := Complex.exp ((t : ℂ) * Complex.I)
  let g : E → ℂ := fun x => if x ∈ B then z else 1
  let L : Measure E → ℂ := fun η =>
    Complex.exp ((t : ℂ) * (natCount B η : ℂ) * Complex.I)
  have hN := measurable_natCount hB
  have hL : Measurable L := by dsimp [L]; fun_prop
  have hLi : Integrable L (poissonPointProcess μ) :=
    (integrable_const (1 : ℝ)).mono' hL.aestronglyMeasurable <|
      Filter.Eventually.of_forall fun η => by simp [L, Complex.norm_exp]
  have htuple (n : ℕ) (x : Fin n → E) : L (countingMeasure x) = ∏ i, g (x i) := by
    dsimp [L, natCount]
    rw [countingMeasure_apply_nat _ hB]
    rw [ENNReal.toReal_natCast, Nat.floor_natCast]
    simp only [Nat.cast_sum]
    rw [Finset.mul_sum, Finset.sum_mul, Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : x i ∈ B <;> simp [hi, g, z]
  have hcomponent (n : ℕ) :
      (∫ η, L η ∂(ENNReal.ofReal (Real.exp (-μ.real univ) / n !) •
        (Measure.pi fun _ : Fin n => μ).map countingMeasure)) =
          (Real.exp (-μ.real univ) / n !) • (∫ x, g x ∂μ) ^ n := by
    rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]
    rw [integral_map (measurable_countingMeasure n).aemeasurable hL.aestronglyMeasurable]
    simp_rw [htuple]
    rw [integral_fintype_prod_eq_prod (fun _ : Fin n => g)]
    simp
  have hgint : (∫ x, g x ∂μ) = (μ.real B : ℂ) * z + (μ.real Bᶜ : ℂ) := by
    change (∫ x, B.piecewise (fun _ => z) (fun _ => 1) x ∂μ) = _
    rw [integral_piecewise hB (integrable_const z) (integrable_const (1 : ℂ))]
    simp [integral_const]
  rw [charFun_apply_real,
    integral_map (by fun_prop) (by fun_prop), integral_map hN.aemeasurable (by fun_prop)]
  change ∫ η, L η ∂poissonPointProcess μ = _
  rw [poissonPointProcess, integral_sum_measure hLi]
  simp_rw [hcomponent]
  have hseries :
      (∑' n : ℕ, (Real.exp (-μ.real univ) / n !) • (∫ x, g x ∂μ) ^ n) =
        (Real.exp (-μ.real univ) : ℂ) * Complex.exp (∫ x, g x ∂μ) := by
    have h := (NormedSpace.expSeries_div_hasSum_exp (∫ x, g x ∂μ)).mul_left
      (Real.exp (-μ.real univ) : ℂ)
    convert h.tsum_eq using 1
    · congr 1
      ext n
      simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_natCast]
      ring
    · rw [← Complex.exp_eq_exp_ℂ]
  rw [hseries, Complex.ofReal_exp, ← Complex.exp_add, hgint,
    measureReal_compl hB, Complex.ofReal_sub, Complex.ofReal_neg]
  congr 1
  dsimp [z]
  ring

/-- The number of points `η(B)` in a measurable set `B` has the Poisson law of mean `μ(B)`. -/
theorem map_apply_eq_poissonMeasure {B : Set E} (hB : MeasurableSet B) :
    (poissonPointProcess μ).map (fun η => η B) =
      (poissonMeasure (μ B).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞) := by
  classical
  have hN := measurable_natCount hB
  have hLaw : (poissonPointProcess μ).map (natCount B) = poissonMeasure (μ B).toNNReal := by
    apply (MeasurableEmbedding.natCast (α := ℝ)).map_injective
    apply Measure.ext_of_charFun
    ext t
    rw [count_charFun μ hB, charFun_map_cast_poissonMeasure]
    rfl
  have hcast : Measurable (Nat.cast : ℕ → ℝ≥0∞) := .of_discrete
  have hNC := hcast.comp hN
  have hmap : (poissonPointProcess μ).map (fun η => η B) =
      ((poissonPointProcess μ).map (natCount B)).map (Nat.cast : ℕ → ℝ≥0∞) := by
    rw [Measure.map_map hcast hN]
    simp only [poissonPointProcess, Measure.map_sum (Measure.measurable_coe hB).aemeasurable,
      Measure.map_sum hNC.aemeasurable]
    congr 1
    ext n : 1
    rw [Measure.map_smul _ (Measure.measurable_coe hB).aemeasurable,
      Measure.map_smul _ hNC.aemeasurable]
    congr 1
    rw [Measure.map_map (Measure.measurable_coe hB) (measurable_countingMeasure n),
      Measure.map_map hNC (measurable_countingMeasure n)]
    congr 1
    ext x
    dsimp [Function.comp_def, natCount]
    rw [countingMeasure_apply_nat _ hB]
    simp
  rw [hmap, hLaw]

/-- The joint characteristic function of the counts `η(A i)` of pairwise disjoint sets. -/
private theorem counts_charFun {ι : Type*} [Fintype ι] (A : ι → Set E)
    (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise (Disjoint on A))
    (t : PiLp 2 (fun _ : ι => ℝ)) :
    charFun (((poissonPointProcess μ).map
        (fun η i => (natCount (A i) η : ℝ))).map (WithLp.toLp 2)) t =
      ∏ i, charFun ((poissonMeasure (μ (A i)).toNNReal).map (Nat.cast : ℕ → ℝ)) (t i) := by
  classical
  let z : ι → ℂ := fun i => Complex.exp ((t i : ℂ) * Complex.I)
  let g : E → ℂ := fun x => ∏ i, if x ∈ A i then z i else 1
  let L : Measure E → ℂ := fun η =>
    Complex.exp ((∑ i, (t i : ℂ) * (natCount (A i) η : ℂ)) * Complex.I)
  have hN : ∀ i, Measurable (natCount (A i)) := fun i => measurable_natCount (hA i)
  have hvec : Measurable fun η : Measure E => fun i => (natCount (A i) η : ℝ) :=
    Measurable.of_eval fun i => measurable_from_nat.comp (hN i)
  have hL : Measurable L := by
    dsimp only [L]
    refine Complex.measurable_exp.comp (Measurable.mul_const ?_ _)
    exact Finset.measurable_sum _ fun i _ =>
      measurable_const.mul (measurable_from_nat.comp (hN i))
  have hLi : Integrable L (poissonPointProcess μ) :=
    (integrable_const (1 : ℝ)).mono' hL.aestronglyMeasurable <|
      Filter.Eventually.of_forall fun η => by
        simp only [L, Complex.norm_exp]
        simp [Complex.mul_re]
  have htuple (n : ℕ) (x : Fin n → E) : L (countingMeasure x) = ∏ p, g (x p) := by
    simp only [L, g, natCount]
    simp_rw [countingMeasure_apply_nat _ (hA _), ENNReal.toReal_natCast, Nat.floor_natCast,
      Nat.cast_sum, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm, Complex.exp_sum]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hp : x p ∈ A i <;> simp [hp, z]
  have hg : g = fun x => 1 + ∑ i, (A i).indicator (fun _ => z i - 1) x := by
    funext x
    by_cases hx : ∃ j, x ∈ A j
    · obtain ⟨j, hj⟩ := hx
      have hother : ∀ i, i ≠ j → x ∉ A i := fun i hij hi =>
        Set.disjoint_left.1 (hd hij) hi hj
      simp only [g]
      rw [Finset.prod_eq_single j (fun i _ hij => by simp [hother i hij]) (by simp),
        Finset.sum_eq_single j (fun i _ hij => Set.indicator_of_notMem (hother i hij) _)
          (by simp), Set.indicator_of_mem hj]
      simp [hj]
    · simp only [not_exists] at hx
      simp [g, hx]
  have hgint : (∫ x, g x ∂μ) = (μ.real univ : ℂ) + ∑ i, (z i - 1) * (μ.real (A i) : ℂ) := by
    rw [hg, integral_add (integrable_const _) (integrable_finsetSum _ fun i _ =>
      (integrable_const _).indicator (hA i)), integral_const, integral_finsetSum _ fun i _ =>
      (integrable_const _).indicator (hA i)]
    simp_rw [integral_indicator_const _ (hA _)]
    simp [mul_comm]
  have hcomponent (n : ℕ) :
      (∫ η, L η ∂(ENNReal.ofReal (Real.exp (-μ.real univ) / n !) •
        (Measure.pi fun _ : Fin n => μ).map countingMeasure)) =
          (Real.exp (-μ.real univ) / n !) • (∫ x, g x ∂μ) ^ n := by
    rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
      integral_map (measurable_countingMeasure n).aemeasurable hL.aestronglyMeasurable]
    simp_rw [htuple]
    rw [integral_fintype_prod_eq_pow g, Fintype.card_fin]
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop),
    integral_map hvec.aemeasurable (by fun_prop)]
  have hinner : ∀ η : Measure E,
      Complex.exp ((inner ℝ (WithLp.toLp 2 (fun i => (natCount (A i) η : ℝ))) t : ℂ) *
        Complex.I) =
        L η := by
    intro η
    simp only [L, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Complex.ofReal_sum,
      Complex.ofReal_mul, Complex.ofReal_natCast]
  simp_rw [hinner]
  rw [poissonPointProcess, integral_sum_measure hLi]
  simp_rw [hcomponent]
  have hseries :
      (∑' n : ℕ, (Real.exp (-μ.real univ) / n !) • (∫ x, g x ∂μ) ^ n) =
        (Real.exp (-μ.real univ) : ℂ) * Complex.exp (∫ x, g x ∂μ) := by
    have h := (NormedSpace.expSeries_div_hasSum_exp (∫ x, g x ∂μ)).mul_left
      (Real.exp (-μ.real univ) : ℂ)
    convert h.tsum_eq using 1
    · congr 1
      ext n
      simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_natCast]
      ring
    · rw [← Complex.exp_eq_exp_ℂ]
  rw [hseries, Complex.ofReal_exp, ← Complex.exp_add, hgint]
  simp_rw [charFun_map_cast_poissonMeasure]
  rw [← Complex.exp_sum]
  congr 1
  simp only [z]
  have hr : ∀ i, (((μ (A i)).toNNReal : ℝ) : ℂ) = (μ.real (A i) : ℂ) := fun i => rfl
  simp_rw [hr]
  push_cast
  rw [neg_add_cancel_left]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The counts `η(A i)` of pairwise disjoint measurable sets are independent, and `η(A i)`
has the Poisson law of mean `μ(A i)`: the mixed binomial process is a Poisson process with
intensity `μ` in the sense of Last–Penrose Def. 3.1 (Last–Penrose Prop. 3.5). -/
theorem map_apply_pi {ι : Type*} [Fintype ι] (A : ι → Set E)
    (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise (Disjoint on A)) :
    (poissonPointProcess μ).map (fun η i => η (A i)) =
      Measure.pi fun i => (poissonMeasure (μ (A i)).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞) := by
  classical
  have hN : ∀ i, Measurable (natCount (A i)) := fun i => measurable_natCount (hA i)
  have hvec : Measurable fun η : Measure E => fun i => (natCount (A i) η : ℝ) :=
    Measurable.of_eval fun i => measurable_from_nat.comp (hN i)
  have hof : Measurable fun (y : ι → ℝ) (i : ι) => ENNReal.ofReal (y i) :=
    Measurable.of_eval fun i => ENNReal.measurable_ofReal.comp (measurable_pi_apply i)
  have hcount : Measurable fun η : Measure E => fun i => η (A i) :=
    Measurable.of_eval fun i => Measure.measurable_coe (hA i)
  have hR : (poissonPointProcess μ).map (fun η i => (natCount (A i) η : ℝ)) =
      Measure.pi fun i => (poissonMeasure (μ (A i)).toNNReal).map (Nat.cast : ℕ → ℝ) :=
    (charFun_eq_pi_iff).1 (counts_charFun μ A hA hd)
  have hmap : (poissonPointProcess μ).map (fun η i => η (A i)) =
      ((poissonPointProcess μ).map (fun η i => (natCount (A i) η : ℝ))).map
        (fun y i => ENNReal.ofReal (y i)) := by
    rw [Measure.map_map hof hvec]
    simp only [poissonPointProcess, Measure.map_sum hcount.aemeasurable,
      Measure.map_sum (hof.comp hvec).aemeasurable]
    congr 1
    ext n : 1
    rw [Measure.map_smul _ hcount.aemeasurable, Measure.map_smul _ (hof.comp hvec).aemeasurable,
      Measure.map_map hcount (measurable_countingMeasure n),
      Measure.map_map (hof.comp hvec) (measurable_countingMeasure n)]
    congr 2
    funext x i
    simp only [Function.comp_apply, natCount, countingMeasure_apply_nat _ (hA i),
      ENNReal.toReal_natCast, Nat.floor_natCast, ENNReal.ofReal_natCast]
  rw [hmap, hR, Measure.pi_map_pi (fun _ => ENNReal.measurable_ofReal.aemeasurable)]
  congr 1
  funext i
  rw [Measure.map_map ENNReal.measurable_ofReal measurable_from_nat]
  congr 1
  funext k
  simp

/-- **Campbell's formula.** `E ∫ f dη = ∫ f dμ` for measurable `f : E → [0, ∞]`
(Last–Penrose Prop. 2.7). -/
theorem lintegral_lintegral {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ η, ∫⁻ x, f x ∂η ∂(poissonPointProcess μ) = ∫⁻ x, f x ∂μ := by
  rw [poissonPointProcess, lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, lintegral_map (Measure.measurable_lintegral hf)
    (measurable_countingMeasure _), lintegral_countingMeasure _ hf]
  have key : ∀ n : ℕ, ∫⁻ x, ∑ i, f (x i) ∂(Measure.pi fun _ : Fin n => μ) =
      (n : ℝ≥0∞) * (μ univ ^ (n - 1) * ∫⁻ y, f y ∂μ) := fun n => by
    rw [lintegral_finsetSum (f := fun i (x : Fin n → E) => f (x i)) _
      (fun i _ => hf.comp (measurable_pi_apply i))]
    simp_rw [lintegral_pi_eval μ _ hf]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [key, smul_eq_mul]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.add_sub_cancel]
  calc ∑' n : ℕ, ENNReal.ofReal (Real.exp (-μ.real univ) / (n + 1)!) *
        (((n + 1 : ℕ) : ℝ≥0∞) * (μ univ ^ n * ∫⁻ x, f x ∂μ))
      = ∑' n : ℕ, ENNReal.ofReal (Real.exp (-μ.real univ) / n !) * μ univ ^ n *
          ∫⁻ x, f x ∂μ := by
        refine tsum_congr fun n => ?_
        have : ENNReal.ofReal (Real.exp (-μ.real univ) / (n + 1)!) * ((n + 1 : ℕ) : ℝ≥0∞) =
            ENNReal.ofReal (Real.exp (-μ.real univ) / n !) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [Nat.factorial_succ]; push_cast; field_simp
        rw [← mul_assoc, this, mul_assoc]
    _ = ∫⁻ x, f x ∂μ := by rw [ENNReal.tsum_mul_right, tsum_coeff_mul_pow, one_mul]

/-- **Laplace functional.** For measurable `f : E → [0, ∞)`,
`E exp(-∫ f dη) = exp(-∫ (1 - e^{-f}) dμ)` (Last–Penrose Thm. 3.9). The integral `∫ f dη` is a
finite sum `∑ f(x_i)` for every configuration charged by the process. -/
theorem integral_exp_neg {f : E → ℝ≥0} (hf : Measurable f) :
    ∫ η, Real.exp (-(∫⁻ x, (f x : ℝ≥0∞) ∂η).toReal) ∂(poissonPointProcess μ) =
      Real.exp (-∫ x, (1 - Real.exp (-(f x : ℝ))) ∂μ) := by
  have hfE : Measurable fun x => (f x : ℝ≥0∞) := hf.coe_nnreal_ennreal
  set g : Measure E → ℝ := fun η => Real.exp (-(∫⁻ x, (f x : ℝ≥0∞) ∂η).toReal) with hg
  have hgm : Measurable g :=
    Real.measurable_exp.comp ((Measure.measurable_lintegral hfE).ennreal_toReal.neg)
  have hgb : ∀ η, ‖g η‖ ≤ 1 := fun η => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 ENNReal.toReal_nonneg)
  have hint : Integrable g (poissonPointProcess μ) :=
    Integrable.of_bound hgm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hgb)
  have hgx : ∀ n (x : Fin n → E), g (countingMeasure x) = ∏ i, Real.exp (-(f (x i) : ℝ)) := by
    intro n x
    rw [hg]; dsimp only
    rw [lintegral_countingMeasure _ hfE, ← Real.exp_sum, ← ENNReal.ofNNReal_finsetSum,
      ENNReal.coe_toReal, NNReal.coe_sum, Finset.sum_neg_distrib]
  set a : ℝ := ∫ x, Real.exp (-(f x : ℝ)) ∂μ with ha
  have hint1 : Integrable (fun x => Real.exp (-(f x : ℝ))) μ := by
    refine Integrable.of_bound (Real.measurable_exp.comp
      hf.coe_nnreal_real.neg).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (f x).coe_nonneg)
  have hrhs : ∫ x, (1 - Real.exp (-(f x : ℝ))) ∂μ = μ.real univ - a := by
    rw [integral_sub (integrable_const 1) hint1, integral_const, smul_eq_mul, mul_one]
  rw [hrhs, poissonPointProcess, integral_sum_measure (by rwa [← poissonPointProcess])]
  simp_rw [integral_smul_measure]
  have key : ∀ n : ℕ, ∫ η, Real.exp (-(∫⁻ x, (f x : ℝ≥0∞) ∂η).toReal)
      ∂((Measure.pi fun _ : Fin n => μ).map countingMeasure) = a ^ n := fun n => by
    rw [integral_map (measurable_countingMeasure n).aemeasurable hgm.aestronglyMeasurable]
    simp_rw [hgx]
    rw [integral_fintype_prod_eq_pow (fun y => Real.exp (-(f y : ℝ))), Fintype.card_fin]
  have hcoef : ∀ n : ℕ, (ENNReal.ofReal (Real.exp (-μ.real univ) / n !)).toReal =
      Real.exp (-μ.real univ) / n ! := fun n => ENNReal.toReal_ofReal (by positivity)
  simp_rw [key, smul_eq_mul, hcoef]
  have hs := (NormedSpace.expSeries_div_hasSum_exp a).mul_left (Real.exp (-μ.real univ))
  rw [← Real.exp_eq_exp_ℝ] at hs
  rw [show -(μ.real univ - a) = -μ.real univ + a by ring, Real.exp_add, ← hs.tsum_eq]
  exact tsum_congr fun n => by ring

private theorem countingMeasure_univ {n : ℕ}
    (x : Fin n → E) : countingMeasure x univ = n := by
  simp [countingMeasure, Measure.finsetSum_apply]

private theorem countingMeasure_split {n : ℕ}
    (x : Fin (n + 1) → E) (i : Fin (n + 1)) :
    countingMeasure x = countingMeasure (fun j => x (i.succAbove j)) +
      Measure.dirac (x i) := by
  unfold countingMeasure
  rw [Fin.sum_univ_succAbove _ i, add_comm]

private theorem lintegral_counting_map {n : ℕ}
    (ν : Measure (Fin n → E)) {h : E → Measure E → ℝ≥0∞}
    (hh : Measurable (Function.uncurry h)) :
    ∫⁻ η, ∫⁻ y, h y η ∂η ∂(ν.map countingMeasure) =
      ∫⁻ x, ∫⁻ y, h y (countingMeasure x) ∂(countingMeasure x) ∂ν := by
  classical
  have hs : MeasurableSet {η : Measure E | η univ ≤ (n : ℝ≥0∞)} :=
    measurableSet_le (Measure.measurable_coe MeasurableSet.univ) measurable_const
  let κ : Kernel (Measure E) E :=
    ⟨fun η => if η univ ≤ (n : ℝ≥0∞) then η else 0,
      Measurable.ite hs measurable_id measurable_const⟩
  have : IsFiniteKernel κ := ⟨n, by simp, fun η => by
    change (if η univ ≤ (n : ℝ≥0∞) then η else 0) univ ≤ n
    split_ifs with hη
    · exact hη
    · simp⟩
  have hf : Measurable (fun η => ∫⁻ y, h y η ∂κ η) :=
    hh.lintegral_kernel_prod_left
  have hsupport : ∀ᵐ η ∂ν.map countingMeasure, η univ ≤ (n : ℝ≥0∞) := by
    rw [ae_map_iff (measurable_countingMeasure n).aemeasurable hs]
    exact Filter.Eventually.of_forall fun x => by simp [countingMeasure_univ]
  have hf' : AEMeasurable (fun η => ∫⁻ y, h y η ∂η) (ν.map countingMeasure) :=
    hf.aemeasurable.congr (hsupport.mono fun η hη => by
      change (∫⁻ y, h y η ∂(if η univ ≤ (n : ℝ≥0∞) then η else 0)) = _
      rw [ite_eq_left hη])
  exact lintegral_map' hf' (measurable_countingMeasure n).aemeasurable

private theorem lintegral_countingMeasure_self {n : ℕ}
    (x : Fin n → E) {h : E → Measure E → ℝ≥0∞}
    (hh : Measurable (Function.uncurry h)) :
    ∫⁻ y, h y (countingMeasure x) ∂(countingMeasure x) =
      ∑ i, h (x i) (countingMeasure x) := by
  change (∫⁻ y, h y (countingMeasure x) ∂∑ i, Measure.dirac (x i)) = _
  rw [lintegral_finsetSum_measure]
  congr 1
  funext i
  exact lintegral_dirac' _ (hh.comp (measurable_id.prodMk measurable_const))

private theorem lintegral_coordinate (n : ℕ) (i : Fin (n + 1)) {h : E → Measure E → ℝ≥0∞}
    (hh : Measurable (Function.uncurry h)) :
    ∫⁻ x, h (x i) (countingMeasure x) ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
      ∫⁻ y, ∫⁻ x, h y (countingMeasure x + Measure.dirac y)
        ∂(Measure.pi fun _ : Fin n => μ) ∂μ := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) i
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  have heq : (fun x : Fin (n + 1) → E => h (x i) (countingMeasure x)) =
      (fun p : E × (Fin n → E) => h p.1 (countingMeasure p.2 + Measure.dirac p.1)) ∘
        e := by
    funext x
    exact congrArg (h (x i)) (countingMeasure_split x i)
  rw [heq]
  change (∫⁻ x, h (e x).1 (countingMeasure (e x).2 + Measure.dirac (e x).1)
    ∂(Measure.pi fun _ : Fin (n + 1) => μ)) = _
  rw [← he.lintegral_map_equiv
    (fun p => h p.1 (countingMeasure p.2 + Measure.dirac p.1)) e, lintegral_prod]
  exact (hh.comp (measurable_fst.prodMk
    (((measurable_countingMeasure n).comp measurable_snd).add
      (Measure.measurable_dirac.comp measurable_fst)))).aemeasurable

private theorem coefficient_succ (c : ℝ) (n : ℕ) :
    ENNReal.ofReal (Real.exp (-c) / (n + 1) !) * (n + 1) =
      ENNReal.ofReal (Real.exp (-c) / n !) := by
  have he : (n : ℝ≥0∞) + 1 = ENNReal.ofReal (n + 1 : ℝ) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    simp
  rw [he, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hn : (n ! : ℝ) ≠ 0 := by positivity
  have hn' : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  simp

/-- **Mecke equation.** For measurable `h : E × Measure E → [0, ∞]`,
`E ∫ h(x, η) η(dx) = ∫ E h(x, η + δ_x) μ(dx)` (Mecke 1967; Last–Penrose Thm. 4.1). -/
theorem lintegral_lintegral_mecke {h : E → Measure E → ℝ≥0∞}
    (hh : Measurable (Function.uncurry h)) :
    ∫⁻ η, ∫⁻ x, h x η ∂η ∂(poissonPointProcess μ) =
      ∫⁻ x, ∫⁻ η, h x (η + Measure.dirac x) ∂(poissonPointProcess μ) ∂μ := by
  let c : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (Real.exp (-μ.real univ) / n !)
  let b : ℕ → ℝ≥0∞ := fun n => ∫⁻ y, ∫⁻ x,
    h y (countingMeasure x + Measure.dirac y) ∂(Measure.pi fun _ : Fin n => μ) ∂μ
  have hm (n : ℕ) : Measurable (fun p : E × (Fin n → E) =>
      h p.1 (countingMeasure p.2 + Measure.dirac p.1)) :=
    hh.comp (measurable_fst.prodMk
      (((measurable_countingMeasure n).comp measurable_snd).add
        (Measure.measurable_dirac.comp measurable_fst)))
  have hleft : (∫⁻ η, ∫⁻ x, h x η ∂η ∂(poissonPointProcess μ)) =
      ∑' n, c n * b n := by
    unfold poissonPointProcess
    rw [lintegral_sum_measure]
    simp_rw [lintegral_smul_measure, smul_eq_mul, lintegral_counting_map _ hh,
      lintegral_countingMeasure_self _ hh]
    rw [tsum_eq_zero_add' ENNReal.summable]
    simp only [Fin.sum_univ_zero, lintegral_zero, mul_zero, zero_add]
    apply tsum_congr
    intro n
    rw [lintegral_finsetSum (f := fun i x => h (x i) (countingMeasure x)) _ (fun i _ =>
      hh.comp ((measurable_pi_apply i).prodMk (measurable_countingMeasure (n + 1))))]
    simp_rw [lintegral_coordinate μ n _ hh]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← mul_assoc]
    change ENNReal.ofReal (Real.exp (-μ.real univ) / (n + 1) !) *
      ((n + 1 : ℕ) : ℝ≥0∞) * b n = c n * b n
    rw [Nat.cast_add, Nat.cast_one, coefficient_succ]
  rw [hleft]
  symm
  unfold poissonPointProcess
  simp_rw [lintegral_sum_measure, lintegral_smul_measure, smul_eq_mul]
  have hmap (y : E) (n : ℕ) :
      (∫⁻ η, h y (η + Measure.dirac y)
        ∂((Measure.pi fun _ : Fin n => μ).map countingMeasure)) =
      ∫⁻ x, h y (countingMeasure x + Measure.dirac y)
        ∂(Measure.pi fun _ : Fin n => μ) := by
    apply lintegral_map _ (measurable_countingMeasure n)
    exact hh.comp (measurable_const.prodMk (measurable_id.add measurable_const))
  simp_rw [hmap]
  rw [lintegral_tsum (fun n => ((hm n).lintegral_prod_right'.const_mul (c n)).aemeasurable)]
  apply tsum_congr
  intro n
  exact lintegral_const_mul (c n) (hm n).lintegral_prod_right'

/-- **Mapping theorem.** The image `η ∘ T⁻¹` of a Poisson point process under a measurable map
`T : E → F` is the Poisson point process with intensity `μ ∘ T⁻¹` (Last–Penrose Thm. 5.1). -/
theorem map_map {T : E → F} (hT : Measurable T) :
    (poissonPointProcess μ).map (fun η => η.map T) = poissonPointProcess (μ.map T) := by
  have hmT : Measurable fun η : Measure E => η.map T := Measure.measurable_map T hT
  have hreal : (μ.map T).real univ = μ.real univ := by
    simp [measureReal_def, Measure.map_apply hT MeasurableSet.univ]
  rw [poissonPointProcess, poissonPointProcess, Measure.map_sum hmT.aemeasurable, hreal]
  congr 1; funext n
  rw [Measure.map_smul, Measure.map_map hmT (measurable_countingMeasure n)]
  on_goal 2 => exact hmT.aemeasurable
  congr 1
  have hcomp : (fun η : Measure E => η.map T) ∘ countingMeasure =
      countingMeasure ∘ (fun (x : Fin n → E) (i : Fin n) => T (x i)) := by
    funext x; exact (countingMeasure_comp x hT).symm
  have hTn : Measurable fun (x : Fin n → E) (i : Fin n) => T (x i) :=
    Measurable.of_eval fun i => hT.comp (measurable_pi_apply i)
  rw [hcomp, ← Measure.map_map (measurable_countingMeasure n) hTn,
    Measure.pi_map_pi (fun _ => hT.aemeasurable)]

end MathlibExt.Probability.PoissonPointProcess
