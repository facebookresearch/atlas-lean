/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance

/-!
# The Itô integral of elementary integrands

An **elementary** (simple predictable) integrand with respect to a filtration `F` indexed by
`ℝ≥0` is a process `H u = ∑ i, ξ i 1_{(t_i, t_{i+1}]}(u)` for partition times
`t_0 ≤ t_1 ≤ ⋯ ≤ t_n` and bounded coefficients `ξ i` measurable with respect to `F t_i`. Its Itô
integral against a process `B` is the finite sum
`∫_0^t H dB = ∑ i, ξ i (B (t_{i+1} ∧ t) - B (t_i ∧ t))`.

When `B` is a pre-Brownian motion adapted to `F` whose increments `B t - B s` are independent of
`F s`, this integral satisfies the (polarized) Itô isometry and is an `F`-martingale. These are
the facts on which the `L²` extension of the Itô integral rests (Karatzas–Shreve 1991,
Section 3.2); the extension is `MathlibExt.Probability.ItoIntegral`.

## Main definitions

* `ProbabilityTheory.ElementaryIntegrand F`: elementary integrands for the filtration `F`.
* `ProbabilityTheory.ElementaryIntegrand.toProcess`: the integrand as a process `ℝ≥0 → Ω → ℝ`.
* `ProbabilityTheory.ElementaryIntegrand.itoIntegral`: the integral process `t ↦ ∫_0^t H dB`.
* `ProbabilityTheory.ElementaryIntegrand.single`: the integrand `ξ 1_{(a, b]}`.

## Main results

* `ElementaryIntegrand.itoIntegral_single`: `∫_0^t ξ 1_{(a, b]} dB = ξ (B (b ∧ t) - B (a ∧ t))`.
* `ElementaryIntegrand.integral_itoIntegral_sq_eq_sum`: `E[(∫_0^t H dB)²] = ∑ E[ξ_i²] Δ_i`.
* `ElementaryIntegrand.integral_itoIntegral_sq`: the **Itô isometry**
  `E[(∫_0^t H dB)²] = E ∫_0^t H_u² du`.
* `ElementaryIntegrand.integral_itoIntegral_mul`: the **polarized Itô isometry**
  `E[(∫_0^t H dB) (∫_0^t K dB)] = E ∫_0^t H_u K_u du` for two elementary integrands with possibly
  different partitions.
* `ElementaryIntegrand.martingale_itoIntegral`: `t ↦ ∫_0^t H dB` is an `F`-martingale.
* `IsPreBrownianReal.integral_sub_sq`, `integral_mul_sub_eq_zero`, `integral_mul_sub_sq`: the
  moment identities `E[(B v - B r)²] = v - r`, `E[Z (B v - B r)] = 0` and
  `E[Z (B v - B r)²] = E[Z] (v - r)` for `F r`-measurable `Z`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer,
  1991, Section 3.2.A (simple processes, their stochastic integral, isometry and martingale
  property).
* B. Øksendal, *Stochastic Differential Equations*, 6th ed., Springer, 2003, Lemma 3.1.5.
-/

@[expose] public section

open MeasureTheory Real
open scoped NNReal ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- An **elementary integrand** for a filtration `F` indexed by `ℝ≥0`: partition times
`time 0 ≤ ⋯ ≤ time n` and coefficients `coeff i`, bounded by `bound` and measurable with respect
to `F (time i)`, representing the process `∑ i, coeff i 1_{(time i, time (i + 1)]}`. Equal
consecutive times are allowed (the corresponding interval is empty). -/
structure ElementaryIntegrand (F : Filtration ℝ≥0 mΩ) where
  /-- The number of partition intervals. -/
  n : ℕ
  /-- The partition times `time 0 ≤ time 1 ≤ ⋯ ≤ time n`. -/
  time : Fin (n + 1) → ℝ≥0
  /-- The partition times are nondecreasing. -/
  monotone_time : Monotone time
  /-- The coefficient on the interval `(time i, time (i + 1)]`. -/
  coeff : Fin n → Ω → ℝ
  /-- Each coefficient is known at the left end of its interval. -/
  measurable_coeff : ∀ i, Measurable[F (time i.castSucc)] (coeff i)
  /-- A uniform bound on the coefficients. -/
  bound : ℝ
  /-- The coefficients are bounded by `bound`. -/
  abs_coeff_le : ∀ i ω, |coeff i ω| ≤ bound

/-- The second moment of a Brownian increment: `E[(B v - B r)²] = v - r` for `r ≤ v`. -/
theorem IsPreBrownianReal.integral_sub_sq {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) {r v : ℝ≥0} (hrv : r ≤ v) :
    P[fun ω ↦ (B v ω - B r ω) ^ 2] = (v : ℝ) - r := by
  have h := hB.hasLaw_sub v r
  have hmean : P[fun ω ↦ B v ω - B r ω] = 0 := by
    rw [integral_sub (hB.integrable_eval v) (hB.integrable_eval r), hB.integral_eval,
      hB.integral_eval, sub_zero]
  have hv := h.variance_eq
  rw [variance_id_gaussianReal, variance_of_integral_eq_zero h.aemeasurable hmean] at hv
  rw [show (fun ω ↦ (B v ω - B r ω) ^ 2) = fun ω ↦ (B v - B r) ω ^ 2 from rfl, hv]
  rw [coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hrv))]
  rfl

private theorem indepFun_of_le {F : Filtration ℝ≥0 mΩ} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) {r v : ℝ≥0} (hrv : r ≤ v) {Y : Ω → ℝ} (hY : Measurable[F r] Y)
    {φ : ℝ → ℝ} (hφ : Measurable φ) :
    IndepFun Y (fun ω ↦ φ (B v ω - B r ω)) P := by
  rw [IndepFun_iff_Indep]
  refine (indep_of_indep_of_le_right (indep_of_indep_of_le_left (hInd r v hrv) ?_)
    hY.comap_le).symm
  exact (hφ.comp (comap_measurable _)).comap_le


/-- A factor known at time `r` times a later Brownian increment has mean zero:
`E[Z (B v - B r)] = 0` for `r ≤ v` and `F r`-measurable `Z`, when the increment is independent of
`F r`. No integrability hypothesis on `Z` is needed: independence factorizes the integral for
all measurable factors. -/
theorem integral_mul_sub_eq_zero {F : Filtration ℝ≥0 mΩ} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) {r v : ℝ≥0} (hrv : r ≤ v) {Z : Ω → ℝ} (hZ : Measurable[F r] Z) :
    P[fun ω ↦ Z ω * (B v ω - B r ω)] = 0 := by
  have hBm : ∀ u, Measurable (B u) := fun u ↦ (hBF u).mono (F.le u) le_rfl
  have hI := indepFun_of_le hInd hrv hZ (φ := fun x ↦ x) measurable_id
  have hmul := IndepFun.integral_mul_eq_mul_integral hI
    (hZ.mono (F.le _) le_rfl).aestronglyMeasurable ((hBm v).sub (hBm r)).aestronglyMeasurable
  have hmean : P[fun ω ↦ B v ω - B r ω] = 0 := by
    rw [integral_sub (hB.integrable_eval _) (hB.integrable_eval _), hB.integral_eval,
      hB.integral_eval, sub_zero]
  exact hmul.trans (by rw [hmean, mul_zero])

/-- A factor known at time `r` times a squared later Brownian increment:
`E[Z (B v - B r)²] = E[Z] (v - r)` for `r ≤ v` and `F r`-measurable `Z`, when the increment is
independent of `F r`. -/
theorem integral_mul_sub_sq {F : Filtration ℝ≥0 mΩ} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) {r v : ℝ≥0} (hrv : r ≤ v) {Z : Ω → ℝ} (hZ : Measurable[F r] Z) :
    P[fun ω ↦ Z ω * (B v ω - B r ω) ^ 2] = P[Z] * ((v : ℝ) - r) := by
  have hBm : ∀ u, Measurable (B u) := fun u ↦ (hBF u).mono (F.le u) le_rfl
  have hI := indepFun_of_le hInd hrv hZ (φ := fun x ↦ x ^ 2) (measurable_id.pow_const 2)
  have hmul := IndepFun.integral_mul_eq_mul_integral hI
    (hZ.mono (F.le _) le_rfl).aestronglyMeasurable
    (((hBm v).sub (hBm r)).pow_const 2).aestronglyMeasurable
  exact hmul.trans (by rw [hB.integral_sub_sq hrv])

namespace ElementaryIntegrand

variable {F : Filtration ℝ≥0 mΩ}

/-- The elementary integrand as a process: `u ↦ ∑ i, coeff i 1_{(time i, time (i + 1)]}(u)`. -/
noncomputable def toProcess (H : ElementaryIntegrand F) (u : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, (Set.Ioc (H.time i.castSucc) (H.time i.succ)).indicator (fun _ ↦ H.coeff i ω) u

/-- The **Itô integral** of an elementary integrand against a process `B`:
`t ↦ ∑ i, coeff i (B (time (i + 1) ∧ t) - B (time i ∧ t))`. -/
def itoIntegral (H : ElementaryIntegrand F) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, H.coeff i ω * (B (min (H.time i.succ) t) ω - B (min (H.time i.castSucc) t) ω)

/-- The elementary integrand `ξ 1_{(a, b]}` for `a ≤ b` and an `F a`-measurable `ξ` bounded by
`C`. -/
def single (a b : ℝ≥0) (hab : a ≤ b) (ξ : Ω → ℝ) (hξ : Measurable[F a] ξ) (C : ℝ)
    (hξC : ∀ ω, |ξ ω| ≤ C) : ElementaryIntegrand F where
  n := 1
  time := ![a, b]
  monotone_time := by
    refine Fin.monotone_iff_le_succ.mpr fun i ↦ ?_
    fin_cases i
    simpa using hab
  coeff := fun _ ↦ ξ
  measurable_coeff := fun i ↦ by obtain rfl : i = 0 := Subsingleton.elim _ _; exact hξ
  bound := C
  abs_coeff_le := fun _ ↦ hξC

/-- The process of `single a b hab ξ hξ C hξC` is `u ↦ ξ 1_{(a, b]}(u)`. -/
theorem toProcess_single (a b : ℝ≥0) (hab : a ≤ b) (ξ : Ω → ℝ) (hξ : Measurable[F a] ξ)
    (C : ℝ) (hξC : ∀ ω, |ξ ω| ≤ C) :
    (single a b hab ξ hξ C hξC).toProcess =
      fun u ω ↦ (Set.Ioc a b).indicator (fun _ ↦ ξ ω) u := by
  ext u ω
  exact Fin.sum_univ_one _

/-- **Elementary integrands.** The Itô integral of `ξ 1_{(a, b]}` is
`ξ (B (b ∧ t) - B (a ∧ t))` (Karatzas–Shreve 1991, Section 3.2.A); this holds for every
process `B` and every `ω`, by definition. -/
theorem itoIntegral_single (a b : ℝ≥0) (hab : a ≤ b) (ξ : Ω → ℝ) (hξ : Measurable[F a] ξ)
    (C : ℝ) (hξC : ∀ ω, |ξ ω| ≤ C) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    (single a b hab ξ hξ C hξC).itoIntegral B t ω =
      ξ ω * (B (min b t) ω - B (min a t) ω) :=
  Fin.sum_univ_one _

/-- The elementary Itô integral vanishes at time `0`. -/
@[simp]
theorem itoIntegral_zero (H : ElementaryIntegrand F) (B : ℝ≥0 → Ω → ℝ) :
    H.itoIntegral B 0 = 0 := by
  ext ω
  simp [itoIntegral]

/-- The `i`-th summand of the elementary Itô integral at time `t`. -/
private def term (H : ElementaryIntegrand F) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (i : Fin H.n)
    (ω : Ω) : ℝ :=
  H.coeff i ω * (B (min (H.time i.succ) t) ω - B (min (H.time i.castSucc) t) ω)

private theorem integrable_term_mul_term (H : ElementaryIntegrand F) {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (t : ℝ≥0)
    (i j : Fin H.n) : Integrable (fun ω ↦ H.term B t i ω * H.term B t j ω) P := by
  have hL : ∀ u w, MemLp (fun ω ↦ B u ω - B w ω) 2 P := fun u w ↦
    hB.isGaussianProcess.hasGaussianLaw_fun_sub.memLp_two
  have hprod := (hL (min (H.time i.succ) t) (min (H.time i.castSucc) t)).integrable_mul
    (hL (min (H.time j.succ) t) (min (H.time j.castSucc) t))
  have hm : ∀ k, Measurable (H.coeff k) := fun k ↦ (H.measurable_coeff k).mono (F.le _) le_rfl
  have := hprod.bdd_mul (c := H.bound * H.bound) ((hm i).mul (hm j)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω ↦ by
      rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (H.abs_coeff_le i ω) (H.abs_coeff_le j ω) (abs_nonneg _)
        ((abs_nonneg _).trans (H.abs_coeff_le i ω)))
  refine this.congr (Filter.Eventually.of_forall fun ω ↦ ?_)
  simp only [term, Pi.mul_apply]
  ring

private theorem integral_term_mul_term_of_lt (H : ElementaryIntegrand F) {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) (t : ℝ≥0) {i j : Fin H.n} (hij : i < j) :
    P[fun ω ↦ H.term B t i ω * H.term B t j ω] = 0 := by
  have hj := H.monotone_time (Fin.castSucc_le_succ j)
  rcases le_or_gt (H.time j.castSucc) t with h | h
  · have hle : H.time i.succ ≤ H.time j.castSucc :=
      H.monotone_time (Fin.succ_le_castSucc_iff.mpr hij)
    have hi := H.monotone_time (Fin.castSucc_le_succ i)
    let Y : Ω → ℝ := fun ω ↦ H.term B t i ω * H.coeff j ω
    have hY : Measurable[F (H.time j.castSucc)] Y :=
      (((H.measurable_coeff i).mono (F.mono (hi.trans hle)) le_rfl).mul
        (((hBF (min (H.time i.succ) t)).mono (F.mono ((min_le_left _ _).trans hle)) le_rfl).sub
          ((hBF (min (H.time i.castSucc) t)).mono
            (F.mono ((min_le_left _ _).trans (hi.trans hle))) le_rfl))).mul
        (H.measurable_coeff j)
    have hrv : H.time j.castSucc ≤ min (H.time j.succ) t := le_min hj h
    have hI := indepFun_of_le hInd hrv hY (φ := fun x ↦ x) measurable_id
    have hBm : ∀ u, Measurable (B u) := fun u ↦ (hBF u).mono (F.le u) le_rfl
    let g : Ω → ℝ := fun ω ↦ B (min (H.time j.succ) t) ω - B (H.time j.castSucc) ω
    have hmul := IndepFun.integral_mul_eq_mul_integral hI
      (hY.mono (F.le _) le_rfl).aestronglyMeasurable
      ((hBm (min (H.time j.succ) t)).sub (hBm (H.time j.castSucc))).aestronglyMeasurable
    have hmean : P[g] = 0 := by
      rw [integral_sub (hB.integrable_eval _) (hB.integrable_eval _),
        hB.integral_eval, hB.integral_eval, sub_zero]
    calc ∫ ω, H.term B t i ω * H.term B t j ω ∂P
        = ∫ ω, (Y * g) ω ∂P := by
          congr 1
          funext ω
          simp only [Y, g, term, Pi.mul_apply, min_eq_left h]
          ring
      _ = 0 := by rw [hmul, hmean, mul_zero]
  · have h1 : min (H.time j.castSucc) t = t := min_eq_right h.le
    have h2 : min (H.time j.succ) t = t := min_eq_right (h.le.trans hj)
    simp [term, h1, h2]

private theorem integral_term_mul_self (H : ElementaryIntegrand F) {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) (t : ℝ≥0) (i : Fin H.n) :
    P[fun ω ↦ H.term B t i ω * H.term B t i ω] = P[fun ω ↦ H.coeff i ω ^ 2] *
        ((min (H.time i.succ) t : ℝ) - (min (H.time i.castSucc) t : ℝ)) := by
  have hi := H.monotone_time (Fin.castSucc_le_succ i)
  rcases le_or_gt (H.time i.castSucc) t with h | h
  · have hrv : H.time i.castSucc ≤ min (H.time i.succ) t := le_min hi h
    have hY : Measurable[F (H.time i.castSucc)] (fun ω ↦ H.coeff i ω ^ 2) :=
      (H.measurable_coeff i).pow_const 2
    have hI := indepFun_of_le hInd hrv hY (φ := fun x ↦ x ^ 2) (measurable_id.pow_const 2)
    have hBm : ∀ u, Measurable (B u) := fun u ↦ (hBF u).mono (F.le u) le_rfl
    have hmul := IndepFun.integral_mul_eq_mul_integral hI
      (hY.mono (F.le _) le_rfl).aestronglyMeasurable
      (((hBm (min (H.time i.succ) t)).sub (hBm (H.time i.castSucc))).pow_const
        2).aestronglyMeasurable
    have hsq := hB.integral_sub_sq hrv
    calc ∫ ω, H.term B t i ω * H.term B t i ω ∂P
        = ∫ ω, ((fun ω ↦ H.coeff i ω ^ 2) *
            fun ω ↦ (B (min (H.time i.succ) t) ω - B (H.time i.castSucc) ω) ^ 2) ω ∂P := by
          congr 1
          funext ω
          simp only [term, Pi.mul_apply, min_eq_left h]
          ring
      _ = _ := by
          rw [hmul, hsq, NNReal.coe_min, min_eq_left (show (H.time i.castSucc : ℝ) ≤ t by
            exact_mod_cast h)]
  · have h1 : min (H.time i.castSucc) t = t := min_eq_right h.le
    have h2 : min (H.time i.succ) t = t := min_eq_right (h.le.trans hi)
    rw [← NNReal.coe_min, ← NNReal.coe_min, h1, h2, sub_self, mul_zero]
    simp [term, h1, h2]

/-- **Itô isometry, discrete form.** For a pre-Brownian motion `B` adapted to `F` whose
increments `B t - B s` are independent of `F s`,
`E[(∫_0^t H dB)²] = ∑ i, E[ξ_i²] (t_{i+1} ∧ t - t_i ∧ t)`. -/
theorem integral_itoIntegral_sq_eq_sum (H : ElementaryIntegrand F) {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) (t : ℝ≥0) :
    P[fun ω ↦ H.itoIntegral B t ω ^ 2] =
      ∑ i, P[fun ω ↦ H.coeff i ω ^ 2] *
        ((min (H.time i.succ) t : ℝ) - (min (H.time i.castSucc) t : ℝ)) := by
  have hsq : (fun ω ↦ H.itoIntegral B t ω ^ 2) =
      fun ω ↦ ∑ i, ∑ j, H.term B t i ω * H.term B t j ω := by
    funext ω
    rw [sq, itoIntegral, Finset.sum_mul_sum]
    rfl
  rw [hsq, integral_finsetSum _ fun i _ ↦
    integrable_finsetSum _ fun j _ ↦ H.integrable_term_mul_term hB t i j]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ H.integrable_term_mul_term hB t i j,
    Finset.sum_eq_single i (fun j _ hji ↦ ?_) (by simp)]
  · exact H.integral_term_mul_self hB hBF hInd t i
  · rcases lt_or_gt_of_ne hji with h | h
    · have := H.integral_term_mul_term_of_lt hB hBF hInd t h
      rwa [show (fun ω ↦ H.term B t j ω * H.term B t i ω) =
        fun ω ↦ H.term B t i ω * H.term B t j ω from funext fun _ ↦ mul_comm _ _] at this
    · exact H.integral_term_mul_term_of_lt hB hBF hInd t h

/-- The partition intervals of an elementary integrand are pairwise disjoint. -/
theorem disjoint_Ioc_time
    (H : ElementaryIntegrand F) {i j : Fin H.n} (hij : i ≠ j) :
    Disjoint (Set.Ioc (H.time i.castSucc) (H.time i.succ))
      (Set.Ioc (H.time j.castSucc) (H.time j.succ)) := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [Set.Ioc_disjoint_Ioc]
    exact (min_le_left _ _).trans <| (H.monotone_time (Fin.succ_le_castSucc_iff.mpr h)).trans
      (le_max_right _ _)
  · rw [Set.Ioc_disjoint_Ioc]
    exact (min_le_right _ _).trans <| (H.monotone_time (Fin.succ_le_castSucc_iff.mpr h)).trans
      (le_max_left _ _)

/-- On its `i`-th interval, an elementary integrand equals its `i`-th coefficient. -/
theorem toProcess_eq_of_mem (H : ElementaryIntegrand F) {i : Fin H.n} {u : ℝ≥0}
    (hu : u ∈ Set.Ioc (H.time i.castSucc) (H.time i.succ)) (ω : Ω) :
    H.toProcess u ω = H.coeff i ω := by
  rw [toProcess, Finset.sum_eq_single i (fun j _ hj ↦ Set.indicator_of_notMem
    (fun hu' ↦ Set.disjoint_left.mp (H.disjoint_Ioc_time hj) hu' hu) _) (by simp),
    Set.indicator_of_mem hu]

private theorem toProcess_sq (H : ElementaryIntegrand F) (u : ℝ≥0) (ω : Ω) :
    H.toProcess u ω ^ 2 = ∑ i, (Set.Ioc (H.time i.castSucc) (H.time i.succ)).indicator
      (fun _ ↦ H.coeff i ω ^ 2) u := by
  by_cases h : ∃ i : Fin H.n, u ∈ Set.Ioc (H.time i.castSucc) (H.time i.succ)
  · obtain ⟨i, hi⟩ := h
    have hz : ∀ j, j ≠ i → u ∉ Set.Ioc (H.time j.castSucc) (H.time j.succ) :=
      fun j hj hu ↦ Set.disjoint_left.mp (H.disjoint_Ioc_time hj) hu hi
    rw [toProcess, Finset.sum_eq_single i (fun j _ hj ↦ Set.indicator_of_notMem (hz j hj) _)
      (by simp), Finset.sum_eq_single i (fun j _ hj ↦ Set.indicator_of_notMem (hz j hj) _)
      (by simp), Set.indicator_of_mem hi, Set.indicator_of_mem hi]
  · push Not at h
    simp [toProcess, Set.indicator_of_notMem (h _)]

private theorem indicator_toNNReal (a b : ℝ≥0) (c u : ℝ) :
    (Set.Ioc a b).indicator (fun _ ↦ c) u.toNNReal =
      (Set.Ioc (a : ℝ) b).indicator (fun _ ↦ c) u := by
  by_cases hu : 0 ≤ u
  · have : u.toNNReal ∈ Set.Ioc a b ↔ u ∈ Set.Ioc (a : ℝ) b := by
      rw [Set.mem_Ioc, Set.mem_Ioc, ← NNReal.coe_lt_coe, ← NNReal.coe_le_coe,
        Real.coe_toNNReal _ hu]
    by_cases h : u ∈ Set.Ioc (a : ℝ) b
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (this.mpr h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt this.mp h)]
  · push Not at hu
    have h1 : u ∉ Set.Ioc (a : ℝ) b := fun h ↦ by linarith [h.1, NNReal.coe_nonneg a]
    have h2 : u.toNNReal ∉ Set.Ioc a b := by
      rw [Real.toNNReal_of_nonpos hu.le]
      simp
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]

private theorem integral_indicator_Ioc {a b t : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 ≤ t)
    (c : ℝ) :
    ∫ u in (0 : ℝ)..t, (Set.Ioc a b).indicator (fun _ ↦ c) u = c * (min b t - min a t) := by
  rw [intervalIntegral.integral_of_le ht, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, setIntegral_const, Set.Ioc_inter_Ioc,
    Real.volume_real_Ioc, smul_eq_mul, mul_comm, max_eq_left ha]
  congr 1
  rcases le_total a t with h | h
  · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr (le_min hab h))]
  · rw [min_eq_right h, min_eq_right (h.trans hab), max_eq_right (by linarith)]
    ring

/-- The time integral of the squared elementary integrand, path by path:
`∫_0^t H_u² du = ∑ i, ξ_i² (t_{i+1} ∧ t - t_i ∧ t)`. -/
theorem integral_toProcess_sq (H : ElementaryIntegrand F) (t : ℝ≥0) (ω : Ω) :
    ∫ u in (0 : ℝ)..t, H.toProcess (Real.toNNReal u) ω ^ 2 =
      ∑ i, H.coeff i ω ^ 2 *
        ((min (H.time i.succ) t : ℝ) - (min (H.time i.castSucc) t : ℝ)) := by
  simp_rw [toProcess_sq, indicator_toNNReal]
  rw [intervalIntegral.integral_finsetSum fun i _ ↦ ?_]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact integral_indicator_Ioc (NNReal.coe_nonneg _)
      (by exact_mod_cast H.monotone_time (Fin.castSucc_le_succ i)) (NNReal.coe_nonneg t) _
  · exact (intervalIntegrable_const (c := H.coeff i ω ^ 2)).mono_fun
      ((aestronglyMeasurable_const.indicator measurableSet_Ioc))
      (Filter.Eventually.of_forall fun u ↦ by
        by_cases h : u ∈ Set.Ioc (H.time i.castSucc : ℝ) (H.time i.succ)
        · simp [Set.indicator_of_mem h]
        · simp [Set.indicator_of_notMem h, sq_nonneg])

/-- **Itô isometry** for elementary integrands: for a pre-Brownian motion `B` adapted to `F`
whose increments `B t - B s` are independent of `F s`,
`E[(∫_0^t H dB)²] = E ∫_0^t H_u² du` (Karatzas–Shreve 1991, Section 3.2.A). -/
theorem integral_itoIntegral_sq (H : ElementaryIntegrand F) {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) (t : ℝ≥0) :
    P[fun ω ↦ H.itoIntegral B t ω ^ 2] =
      P[fun ω ↦ ∫ u in (0 : ℝ)..t, H.toProcess (Real.toNNReal u) ω ^ 2] := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  simp_rw [integral_toProcess_sq, H.integral_itoIntegral_sq_eq_sum hB hBF hInd t]
  rw [integral_finsetSum _ fun i _ ↦ ?_]
  · simp_rw [integral_mul_const]
  refine Integrable.mul_const (Integrable.of_bound (C := H.bound ^ 2) ?_ ?_) _
  · exact (((H.measurable_coeff i).mono (F.le _) le_rfl).pow_const 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω ↦ ?_
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (H.abs_coeff_le i ω) 2

/-- A bounded `F r`-measurable factor times a later increment has zero conditional
expectation given `F r`. -/
private theorem condExp_mul_increment {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) {r v : ℝ≥0} (hrv : r ≤ v) {Z : Ω → ℝ} (hZ : Measurable[F r] Z) {C : ℝ}
    (hZC : ∀ ω, |Z ω| ≤ C) :
    P[fun ω ↦ Z ω * (B v ω - B r ω) | F r] =ᵐ[P] 0 := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hint : Integrable (fun ω ↦ B v ω - B r ω) P :=
    (hB.integrable_eval v).sub (hB.integrable_eval r)
  have hZm : Measurable Z := hZ.mono (F.le r) le_rfl
  have hprod : Integrable (fun ω ↦ Z ω * (B v ω - B r ω)) P :=
    hint.bdd_mul hZm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hZC ω)
  have h1 := condExp_mul_of_stronglyMeasurable_left (m := F r) (μ := P)
    hZ.stronglyMeasurable hprod hint
  have hincm : StronglyMeasurable[MeasurableSpace.comap (fun ω ↦ B v ω - B r ω) inferInstance]
      (fun ω ↦ B v ω - B r ω) :=
    (comap_measurable _).stronglyMeasurable
  have hBm : ∀ u, Measurable (B u) := fun u ↦ (hBF u).mono (F.le u) le_rfl
  have h2 := condExp_indep_eq (m₁ := MeasurableSpace.comap (fun ω ↦ B v ω - B r ω) inferInstance)
    (m₂ := F r) (μ := P) ((hBm v).sub (hBm r)).comap_le (F.le r) hincm (hInd r v hrv)
  have h0 : P[fun ω ↦ B v ω - B r ω] = 0 := by
    rw [integral_sub (hB.integrable_eval v) (hB.integrable_eval r), hB.integral_eval,
      hB.integral_eval, sub_zero]
  refine h1.trans ?_
  filter_upwards [h2] with ω hω
  simp [hω, h0]


private theorem martingale_term {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) {a b : ℝ≥0} (hab : a ≤ b) {ξ : Ω → ℝ} (hξ : Measurable[F a] ξ) {C : ℝ}
    (hξC : ∀ ω, |ξ ω| ≤ C) :
    Martingale (fun t ω ↦ ξ ω * (B (min b t) ω - B (min a t) ω)) F P := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hBm : ∀ u, Measurable (B u) := fun u ↦ (hBF u).mono (F.le u) le_rfl
  -- before `a` the term vanishes
  have hzero : ∀ t, t ≤ a → (fun ω ↦ ξ ω * (B (min b t) ω - B (min a t) ω)) = 0 := by
    intro t ht
    funext ω
    simp [min_eq_right ht, min_eq_right (ht.trans hab)]
  refine ⟨fun t ↦ ?_, fun s t hst ↦ ?_⟩ <;> dsimp only
  · rcases le_total t a with h | h
    · rw [hzero t h]
      exact stronglyMeasurable_const
    · refine Measurable.stronglyMeasurable ?_
      exact (hξ.mono (F.mono h) le_rfl).mul
        (((hBF _).mono (F.mono (min_le_right _ _)) le_rfl).sub
          ((hBF _).mono (F.mono (min_le_right _ _)) le_rfl))
  · rcases le_total s a with hsa | has
    · -- `s ≤ a`: the term vanishes at `s`, and conditioning through `F a` kills it at `t`
      rw [hzero s hsa]
      rcases le_total t a with hta | hat
      · rw [hzero t hta]
        simp
      · have hK := condExp_mul_increment hB hBF hInd (le_min hab hat) hξ hξC
        have hat' : min a t = a := min_eq_left hat
        simp_rw [hat']
        refine (condExp_condExp_of_le (F.mono hsa) (F.le a)).symm.trans ?_
        refine (condExp_congr_ae hK).trans ?_
        simp
    · -- `a ≤ s`: split off the increment after `s`
      have hat : a ≤ t := has.trans hst
      have hsplit : (fun ω ↦ ξ ω * (B (min b t) ω - B (min a t) ω)) =
          (fun ω ↦ ξ ω * (B (min b s) ω - B (min a s) ω)) +
            fun ω ↦ ξ ω * (B (min b t) ω - B (min b s) ω) := by
        funext ω
        simp only [Pi.add_apply, min_eq_left has, min_eq_left hat]
        ring
      have hξm : Measurable ξ := hξ.mono (F.le a) le_rfl
      have hint : ∀ u v, Integrable (fun ω ↦ ξ ω * (B u ω - B v ω)) P := fun u v ↦
        ((hB.integrable_eval u).sub (hB.integrable_eval v)).bdd_mul hξm.aestronglyMeasurable
          (Filter.Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hξC ω)
      have hsm : StronglyMeasurable[F s] (fun ω ↦ ξ ω * (B (min b s) ω - B (min a s) ω)) :=
        Measurable.stronglyMeasurable <| (hξ.mono (F.mono has) le_rfl).mul
          (((hBF _).mono (F.mono (min_le_right _ _)) le_rfl).sub
            ((hBF _).mono (F.mono (min_le_right _ _)) le_rfl))
      rw [hsplit]
      refine (condExp_add (hint _ _) (hint _ _) _).trans ?_
      rw [condExp_of_stronglyMeasurable (F.le s) hsm (hint _ _)]
      rcases le_total b s with hbs | hsb
      · have hbt : b ≤ t := hbs.trans hst
        simp only [min_eq_left hbs, min_eq_left hbt, sub_self, mul_zero]
        rw [show (fun _ : Ω ↦ (0 : ℝ)) = 0 from rfl, condExp_zero, add_zero]
      · have hK := condExp_mul_increment hB hBF hInd (le_min hsb hst)
          (hξ.mono (F.mono has) le_rfl) hξC
        rw [min_eq_right hsb]
        filter_upwards [hK] with ω hω
        simp [hω]

/-- **Martingale property.** For a pre-Brownian motion `B` adapted to `F` whose increments
`B t - B s` are independent of `F s`, the elementary Itô integral `t ↦ ∫_0^t H dB` is an
`F`-martingale. -/
theorem martingale_itoIntegral (H : ElementaryIntegrand F) {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) :
    Martingale (H.itoIntegral B) F P := by
  have hsum : H.itoIntegral B = ∑ i, fun t ω ↦
      H.coeff i ω * (B (min (H.time i.succ) t) ω - B (min (H.time i.castSucc) t) ω) := by
    funext t ω
    simp [itoIntegral, Finset.sum_apply]
  rw [hsum]
  refine Finset.sum_induction _ (fun f ↦ Martingale f F P) (fun f g hf hg ↦ hf.add hg)
    (martingale_zero (E := ℝ) F P) fun i _ ↦ ?_
  exact martingale_term hB hBF hInd (H.monotone_time (Fin.castSucc_le_succ i))
    (H.measurable_coeff i) (H.abs_coeff_le i)

/-! ### Polarized isometry -/

private theorem integrable_bdd_mul_sub_mul_sub {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) {Z : Ω → ℝ} (hZ : Measurable Z) {C : ℝ}
    (hZC : ∀ ω, |Z ω| ≤ C) (u v u' v' : ℝ≥0) :
    Integrable (fun ω ↦ Z ω * (B u ω - B v ω) * (B u' ω - B v' ω)) P := by
  have hL : ∀ u w, MemLp (fun ω ↦ B u ω - B w ω) 2 P := fun u w ↦
    hB.isGaussianProcess.hasGaussianLaw_fun_sub.memLp_two
  have hprod := (hL u v).integrable_mul (hL u' v')
  refine (hprod.bdd_mul (c := C) hZ.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hZC ω)).congr
    (Filter.Eventually.of_forall fun ω ↦ ?_)
  simp only [Pi.mul_apply]
  ring

private theorem integral_pair_of_le {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) {a b a' b' : ℝ≥0} (hab' : a' ≤ b') (haa : a ≤ a')
    {ξ η : Ω → ℝ} (hξ : Measurable[F a] ξ) (hη : Measurable[F a'] η) {C C' : ℝ}
    (hξC : ∀ ω, |ξ ω| ≤ C) (hηC : ∀ ω, |η ω| ≤ C') (t : ℝ≥0) :
    P[fun ω ↦ ξ ω * (B (min b t) ω - B (min a t) ω) * (η ω * (B (min b' t) ω - B (min a' t) ω))]
      = P[fun ω ↦ ξ ω * η ω] *
        max (((min (min b b') t : ℝ≥0) : ℝ) - ((max a a' : ℝ≥0) : ℝ)) 0 := by
  have hBm : ∀ u, Measurable (B u) := fun u ↦ (hBF u).mono (F.le u) le_rfl
  have hBF' : ∀ {u c}, u ≤ c → Measurable[F c] (B u) := fun h ↦ (hBF _).mono (F.mono h) le_rfl
  have hξ' : ∀ {c}, a ≤ c → Measurable[F c] ξ := fun h ↦ hξ.mono (F.mono h) le_rfl
  have hη' : ∀ {c}, a' ≤ c → Measurable[F c] η := fun h ↦ hη.mono (F.mono h) le_rfl
  have hmax : max a a' = a' := max_eq_right haa
  rcases le_or_gt t a' with hta | hat
  · have h1 : min a' t = t := min_eq_right hta
    have h2 : min b' t = t := min_eq_right (hta.trans hab')
    have hle : ((min (min b b') t : ℝ≥0) : ℝ) - ((max a a' : ℝ≥0) : ℝ) ≤ 0 := by
      rw [hmax, sub_nonpos]
      exact_mod_cast (min_le_right _ _).trans hta
    rw [h1, h2, max_eq_right hle]
    simp
  have ha't : min a' t = a' := min_eq_left hat.le
  have hat2 : min a t = a := min_eq_left (haa.trans hat.le)
  have hbt' : a' ≤ min b' t := le_min hab' hat.le
  have hmin : min (min b b') t = min (min b t) (min b' t) := by
    refine le_antisymm (le_min (min_le_min_right _ (min_le_left _ _))
      (min_le_min_right _ (min_le_right _ _))) (le_min (le_min ((min_le_left _ _).trans
        (min_le_left _ _)) ((min_le_right _ _).trans (min_le_left _ _)))
        ((min_le_left _ _).trans (min_le_right _ _)))
  rw [ha't, hat2, hmax, hmin]
  rcases le_or_gt (min b t) a' with hb | hb
  · have hZ : Measurable[F a'] (fun ω ↦ ξ ω * η ω * (B (min b t) ω - B a ω)) :=
      ((hξ' haa).mul hη).mul ((hBF' hb).sub (hBF' haa))
    have h0 := integral_mul_sub_eq_zero hB hBF hInd hbt' hZ
    have hle : ((min (min b t) (min b' t) : ℝ≥0) : ℝ) - (a' : ℝ) ≤ 0 := by
      rw [sub_nonpos]; exact_mod_cast (min_le_left _ _).trans hb
    rw [max_eq_right hle, mul_zero, ← h0]
    congr 1
    funext ω
    ring
  · set c := min (min b t) (min b' t) with hc
    set d := max (min b t) (min b' t) with hd
    have hac : a' ≤ c := le_min hb.le hbt'
    have hcd : c ≤ d := min_le_max
    have hpt : ∀ ω, ξ ω * (B (min b t) ω - B a ω) * (η ω * (B (min b' t) ω - B a' ω)) =
        ξ ω * η ω * (B a' ω - B a ω) * (B (min b' t) ω - B a' ω) +
          (ξ ω * η ω * (B c ω - B a' ω) ^ 2 +
            ξ ω * η ω * (B c ω - B a' ω) * (B d ω - B c ω)) := by
      intro ω
      rcases le_total (min b t) (min b' t) with h | h
      · rw [hc, hd, min_eq_left h, max_eq_right h]; ring
      · rw [hc, hd, min_eq_right h, max_eq_left h]; ring
    have hξη : Measurable (fun ω ↦ ξ ω * η ω) :=
      (hξ.mono (F.le a) le_rfl).mul (hη.mono (F.le a') le_rfl)
    have hξηC : ∀ ω, |ξ ω * η ω| ≤ C * C' := fun ω ↦ by
      rw [abs_mul]
      exact mul_le_mul (hξC ω) (hηC ω) (abs_nonneg _) ((abs_nonneg _).trans (hξC ω))
    have hi1 := integrable_bdd_mul_sub_mul_sub hB hξη hξηC a' a (min b' t) a'
    have hi2 : Integrable (fun ω ↦ ξ ω * η ω * (B c ω - B a' ω) ^ 2) P :=
      (integrable_bdd_mul_sub_mul_sub hB hξη hξηC c a' c a').congr
        (Filter.Eventually.of_forall fun ω ↦ by simp only; ring)
    have hi3 := integrable_bdd_mul_sub_mul_sub hB hξη hξηC c a' d c
    beta_reduce at hi1 hi3
    simp_rw [hpt]
    have hadd := integral_add hi1 (hi2.add hi3)
    simp only [Pi.add_apply] at hadd
    rw [hadd, integral_add hi2 hi3]
    have hZ1 : Measurable[F a'] (fun ω ↦ ξ ω * η ω * (B a' ω - B a ω)) :=
      ((hξ' haa).mul hη).mul ((hBF' le_rfl).sub (hBF' haa))
    have hZ3 : Measurable[F c] (fun ω ↦ ξ ω * η ω * (B c ω - B a' ω)) :=
      ((hξ' (haa.trans hac)).mul (hη' hac)).mul ((hBF' le_rfl).sub (hBF' hac))
    have hZ2 : Measurable[F a'] (fun ω ↦ ξ ω * η ω) := (hξ' haa).mul hη
    rw [integral_mul_sub_eq_zero hB hBF hInd hbt' hZ1,
      integral_mul_sub_eq_zero hB hBF hInd hcd hZ3,
      integral_mul_sub_sq hB hBF hInd hac hZ2,
      max_eq_left (sub_nonneg.mpr (by exact_mod_cast hac))]
    ring

private theorem integral_pair {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) {a b a' b' : ℝ≥0} (hab : a ≤ b) (hab' : a' ≤ b')
    {ξ η : Ω → ℝ} (hξ : Measurable[F a] ξ) (hη : Measurable[F a'] η) {C C' : ℝ}
    (hξC : ∀ ω, |ξ ω| ≤ C) (hηC : ∀ ω, |η ω| ≤ C') (t : ℝ≥0) :
    P[fun ω ↦ ξ ω * (B (min b t) ω - B (min a t) ω) * (η ω * (B (min b' t) ω - B (min a' t) ω))]
      = P[fun ω ↦ ξ ω * η ω] *
        max (((min (min b b') t : ℝ≥0) : ℝ) - ((max a a' : ℝ≥0) : ℝ)) 0 := by
  rcases le_total a a' with h | h
  · exact integral_pair_of_le hB hBF hInd hab' h hξ hη hξC hηC t
  · have := integral_pair_of_le (b := b') hB hBF hInd hab h hη hξ hηC hξC t
    rw [min_comm b' b, max_comm a' a] at this
    have h1 : (fun ω ↦ ξ ω * (B (min b t) ω - B (min a t) ω) *
        (η ω * (B (min b' t) ω - B (min a' t) ω))) = fun ω ↦
          η ω * (B (min b' t) ω - B (min a' t) ω) * (ξ ω * (B (min b t) ω - B (min a t) ω)) :=
      funext fun ω ↦ by ring
    have h2 : (fun ω ↦ ξ ω * η ω) = fun ω ↦ η ω * ξ ω := funext fun ω ↦ mul_comm _ _
    rw [h1, h2]
    exact this

private theorem integral_indicator_Ioc' {a b t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (c : ℝ) :
    ∫ u in (0 : ℝ)..t, (Set.Ioc a b).indicator (fun _ ↦ c) u = c * max (min b t - a) 0 := by
  rw [intervalIntegral.integral_of_le ht, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, setIntegral_const, Set.Ioc_inter_Ioc,
    Real.volume_real_Ioc, smul_eq_mul, mul_comm, max_eq_left ha]

private theorem indicator_mul_indicator (a b a' b' : ℝ≥0) (c d : ℝ) (u : ℝ≥0) :
    (Set.Ioc a b).indicator (fun _ ↦ c) u * (Set.Ioc a' b').indicator (fun _ ↦ d) u =
      (Set.Ioc (max a a') (min b b')).indicator (fun _ ↦ c * d) u := by
  rw [← Set.Ioc_inter_Ioc]
  by_cases h : u ∈ Set.Ioc a b <;> by_cases h' : u ∈ Set.Ioc a' b' <;>
    simp [h, h', Set.indicator_of_mem, Set.indicator_of_notMem]

private theorem integral_toProcess_mul (H K : ElementaryIntegrand F) (t : ℝ≥0) (ω : Ω) :
    ∫ u in (0 : ℝ)..t, H.toProcess (Real.toNNReal u) ω * K.toProcess (Real.toNNReal u) ω =
      ∑ i, ∑ j, H.coeff i ω * K.coeff j ω *
        max (((min (min (H.time i.succ) (K.time j.succ)) t : ℝ≥0) : ℝ) -
          ((max (H.time i.castSucc) (K.time j.castSucc) : ℝ≥0) : ℝ)) 0 := by
  have hpt : ∀ u : ℝ, H.toProcess (Real.toNNReal u) ω * K.toProcess (Real.toNNReal u) ω =
      ∑ i, ∑ j, (Set.Ioc ((max (H.time i.castSucc) (K.time j.castSucc) : ℝ≥0) : ℝ)
        ((min (H.time i.succ) (K.time j.succ) : ℝ≥0) : ℝ)).indicator
          (fun _ ↦ H.coeff i ω * K.coeff j ω) u := by
    intro u
    rw [toProcess, toProcess, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [indicator_mul_indicator, indicator_toNNReal]
  simp_rw [hpt]
  have hii : ∀ (A Bb : ℝ) (c : ℝ), IntervalIntegrable
      (fun u ↦ (Set.Ioc A Bb).indicator (fun _ ↦ c) u) volume 0 t := fun A Bb c ↦
    (intervalIntegrable_const (c := |c|)).mono_fun
      (aestronglyMeasurable_const.indicator measurableSet_Ioc)
      (Filter.Eventually.of_forall fun u ↦ by
        by_cases h : u ∈ Set.Ioc A Bb
        · simp [Set.indicator_of_mem h]
        · simp [Set.indicator_of_notMem h])
  rw [intervalIntegral.integral_finsetSum]
  swap
  · intro i _
    have := IntervalIntegrable.sum Finset.univ fun j _ ↦
      hii ((max (H.time i.castSucc) (K.time j.castSucc) : ℝ≥0) : ℝ)
        ((min (H.time i.succ) (K.time j.succ) : ℝ≥0) : ℝ) (H.coeff i ω * K.coeff j ω)
    simpa only [Finset.sum_fn] using this
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [intervalIntegral.integral_finsetSum]
  swap
  · exact fun j _ ↦ hii _ _ _
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_indicator_Ioc' (NNReal.coe_nonneg _) (NNReal.coe_nonneg t),
    NNReal.coe_min (min _ _) t]

/-- **Polarized Itô isometry** for elementary integrands: for a pre-Brownian motion `B` adapted
to `F` whose increments `B t - B s` are independent of `F s`, and two elementary integrands
`H`, `K` (with possibly different partitions),
`E[(∫_0^t H dB) (∫_0^t K dB)] = E ∫_0^t H_u K_u du`. -/
theorem integral_itoIntegral_mul (H K : ElementaryIntegrand F) {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) (t : ℝ≥0) :
    P[fun ω ↦ H.itoIntegral B t ω * K.itoIntegral B t ω] =
      P[fun ω ↦ ∫ u in (0 : ℝ)..t, H.toProcess (Real.toNNReal u) ω *
        K.toProcess (Real.toNNReal u) ω] := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hm : ∀ (L : ElementaryIntegrand F) k, Measurable (L.coeff k) := fun L k ↦
    (L.measurable_coeff k).mono (F.le _) le_rfl
  have hprod : ∀ i j, Integrable (fun ω ↦ H.term B t i ω * K.term B t j ω) P := by
    intro i j
    refine (integrable_bdd_mul_sub_mul_sub hB ((hm H i).mul (hm K j)) (C := H.bound * K.bound)
      (fun ω ↦ by
        rw [Pi.mul_apply, abs_mul]
        exact mul_le_mul (H.abs_coeff_le i ω) (K.abs_coeff_le j ω) (abs_nonneg _)
          ((abs_nonneg _).trans (H.abs_coeff_le i ω)))
      (min (H.time i.succ) t) (min (H.time i.castSucc) t) (min (K.time j.succ) t)
      (min (K.time j.castSucc) t)).congr (Filter.Eventually.of_forall fun ω ↦ ?_)
    simp only [term, Pi.mul_apply]
    ring
  have hlhs : (fun ω ↦ H.itoIntegral B t ω * K.itoIntegral B t ω) =
      fun ω ↦ ∑ i, ∑ j, H.term B t i ω * K.term B t j ω := by
    funext ω
    rw [itoIntegral, itoIntegral, Finset.sum_mul_sum]
    rfl
  simp_rw [hlhs, integral_toProcess_mul]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hprod i j,
    integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ ?_]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_finsetSum _ fun j _ ↦ hprod i j, integral_finsetSum _ fun j _ ↦ ?_]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [integral_mul_const]
      exact integral_pair hB hBF hInd (H.monotone_time (Fin.castSucc_le_succ i))
        (K.monotone_time (Fin.castSucc_le_succ j)) (H.measurable_coeff i)
        (K.measurable_coeff j) (H.abs_coeff_le i) (K.abs_coeff_le j) t
    · exact (Integrable.of_bound (C := H.bound * K.bound)
        ((hm H i).mul (hm K j)).aestronglyMeasurable (Filter.Eventually.of_forall fun ω ↦ by
          rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (H.abs_coeff_le i ω) (K.abs_coeff_le j ω) (abs_nonneg _)
            ((abs_nonneg _).trans (H.abs_coeff_le i ω)))).mul_const _
  · exact (Integrable.of_bound (C := H.bound * K.bound)
      ((hm H i).mul (hm K j)).aestronglyMeasurable (Filter.Eventually.of_forall fun ω ↦ by
        rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (H.abs_coeff_le i ω) (K.abs_coeff_le j ω) (abs_nonneg _)
          ((abs_nonneg _).trans (H.abs_coeff_le i ω)))).mul_const _

end ElementaryIntegrand

end ProbabilityTheory
