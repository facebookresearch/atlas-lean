/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ElementaryItoIntegral
public import MathlibExt.Probability.ItoRiemannSums
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# The Itô integral

The Itô integral `∫_0^t H dB` of an integrand `H : ℝ≥0 → Ω → ℝ` against a pre-Brownian motion
`B` is the `L²(P)` limit of the elementary Itô integrals of elementary integrands converging to
`H` in `L²(P ⊗ du)` on `(0, t] × Ω` (extension by isometry; Karatzas–Shreve 1991, Section 3.2).
The polarized Itô isometry for elementary integrands
(`ProbabilityTheory.ElementaryIntegrand.integral_itoIntegral_mul`) makes the elementary integrals
of an approximating sequence a Cauchy sequence in `L²(P)` and shows that the limit does not depend
on the sequence.

An integrand is *Itô-approximable on `[0, t]`* (`ProbabilityTheory.IsItoApproximable`) if it is
jointly measurable and such an approximating sequence exists. For other integrands the definition
returns `0`; every result below assumes approximability (or proves it, as for elementary and
continuous deterministic integrands). That every progressive square-integrable integrand is
Itô-approximable (Karatzas–Shreve 1991, Lemma 3.2.4 and Proposition 3.2.6) is not proved here.

Brownian motion with respect to a filtration `F` is spelled out by hypotheses:
`IsPreBrownianReal B P` (or `IsBrownianReal B P` when continuity of paths is used),
`Adapted F B`, and independence of each increment `B t - B s` from `F s`.

## Main definitions

* `ProbabilityTheory.integrandDist P H K t`: the squared `L²(P ⊗ du)` distance on `(0, t] × Ω`.
* `ProbabilityTheory.IsItoApproximable P F H t`: `H` is an `L²(P ⊗ du)`-limit of elementary
  integrands on `(0, t] × Ω`.
* `ProbabilityTheory.itoIntegralL2 P F B H t`: the Itô integral as an element of `L²(P)`.
* `ProbabilityTheory.itoIntegral P F B H`: the Itô integral as a real process, with an
  `F t`-strongly measurable version at each time.

## Main results

* `ProbabilityTheory.tendsto_toL2_itoIntegral`: the elementary integrals of *any* approximating
  sequence converge in `L²(P)` to the Itô integral.
* `ProbabilityTheory.itoIntegral_indicator_Ioc`: the Itô integral of `ξ 1_{(a, b]}` is
  `ξ (B (b ∧ t) - B (a ∧ t))`.
* `ProbabilityTheory.lintegral_itoIntegral_sq`: the **Itô isometry**
  `E[(∫_0^t H dB)²] = E ∫_0^t H_u² du`.
* `ProbabilityTheory.martingale_itoIntegral`: `t ↦ ∫_0^t H dB` is an `F`-martingale.
* `ProbabilityTheory.itoIntegral_deterministic_eq`: **Wiener's integration by parts**
  `∫_0^t g dB = g t B t - g 0 B 0 - ∫_0^t g'(u) B u du` for deterministic `C¹` integrands.
* `ProbabilityTheory.ito_ou_solution_eq_ouPathSolution`: the Itô form
  `e^{-θt} X₀ + σ e^{-θt} ∫_0^t e^{θs} dB_s` of the Ornstein–Uhlenbeck solution equals the
  pathwise solution `ouPathSolution` almost surely.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer,
  1991, Section 3.2 (construction, isometry, martingale property), Section 3.3 (integration by
  parts), Section 5.6 (the Ornstein–Uhlenbeck process).
* B. Øksendal, *Stochastic Differential Equations*, 6th ed., Springer, 2003, Chapter 3 and
  Theorem 4.1.5.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped NNReal ENNReal ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The squared `L²(P ⊗ du)` distance on `(0, t] × Ω` between two processes, in `ℝ≥0∞`:
`∫⁻ ω, ∫⁻ u in (0, t], |H u ω - K u ω|² du dP`. -/
noncomputable def integrandDist (P : Measure Ω) (H K : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω - K u.toNNReal ω‖ₑ ^ 2) ∂P

/-- A process `H` is **Itô-approximable on `[0, t]`** for the filtration `F` if it is jointly
measurable and is the `L²(P ⊗ du)`-limit on `(0, t] × Ω` of elementary integrands. -/
def IsItoApproximable (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    Prop :=
  Measurable (fun p : ℝ × Ω ↦ H p.1.toNNReal p.2) ∧
    ∃ Hn : ℕ → ElementaryIntegrand F,
      Tendsto (fun n ↦ integrandDist P (Hn n).toProcess H t) atTop (𝓝 0)

open Classical in
/-- A function as an element of `L²(P)`, or `0` if it is not square integrable. -/
noncomputable def toL2 (P : Measure Ω) (f : Ω → ℝ) : Lp ℝ 2 P :=
  if h : MemLp f 2 P then h.toLp f else 0

open Classical in
/-- The **Itô integral** `∫_0^t H dB` as an element of `L²(P)`: the `L²` limit of the elementary
Itô integrals of an approximating sequence of elementary integrands when `H` is Itô-approximable
on `[0, t]`, and `0` otherwise. -/
noncomputable def itoIntegralL2 (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (B H : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) : Lp ℝ 2 P :=
  if h : IsItoApproximable P F H t then
    limUnder atTop fun n ↦ toL2 P ((h.2.choose n).itoIntegral B t)
  else 0

open Classical in
/-- The **Itô integral** `t ↦ ∫_0^t H dB` as a real process: an `F t`-strongly measurable
version of `itoIntegralL2 P F B H t` when one exists (which is the case under the hypotheses of
the theorems below), and a representative of `itoIntegralL2 P F B H t` otherwise. -/
noncomputable def itoIntegral (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (B H : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) : Ω → ℝ :=
  if h : AEStronglyMeasurable[F t] (itoIntegralL2 P F B H t) P then h.mk _
  else itoIntegralL2 P F B H t

/-- The Itô integral process is almost surely equal to `itoIntegralL2` at each time. -/
theorem itoIntegral_ae_eq (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (B H : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) : itoIntegral P F B H t =ᵐ[P] itoIntegralL2 P F B H t := by
  unfold itoIntegral
  split_ifs with h
  · exact h.ae_eq_mk.symm
  · rfl


private theorem integrable_intervalIntegral {P : Measure Ω} [IsFiniteMeasure P] {f : ℝ → Ω → ℝ}
    (hf : Measurable fun p : ℝ × Ω ↦ f p.1 p.2) {C : ℝ} (hC : ∀ u ω, |f u ω| ≤ C) (t : ℝ≥0) :
    Integrable (fun ω ↦ ∫ u in (0 : ℝ)..t, f u ω) P := by
  refine Integrable.of_bound (C := C * t) ?_ (Filter.Eventually.of_forall fun ω ↦ ?_)
  · simp_rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
    exact (StronglyMeasurable.integral_prod_right (ν := volume.restrict (Set.Ioc (0 : ℝ) t))
      (f := fun ω u ↦ f u ω) (hf.comp measurable_swap).stronglyMeasurable).aestronglyMeasurable
  · refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := C) fun u _ ↦ ?_).trans_eq ?_
    · rw [Real.norm_eq_abs]; exact hC u ω
    · rw [sub_zero, abs_of_nonneg (NNReal.coe_nonneg t)]

private theorem intervalIntegrable_of_bound {f : ℝ → Ω → ℝ}
    (hf : Measurable fun p : ℝ × Ω ↦ f p.1 p.2) {C : ℝ} (hC : ∀ u ω, |f u ω| ≤ C) (t : ℝ≥0)
    (ω : Ω) : IntervalIntegrable (fun u ↦ f u ω) volume 0 t :=
  (intervalIntegrable_const (c := C)).mono_fun
    (hf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u ↦ by
      change ‖f u ω‖ ≤ |C|
      rw [Real.norm_eq_abs]
      exact (hC u ω).trans (le_abs_self C))

private theorem lintegral_lintegral_ofReal {P : Measure Ω} [IsFiniteMeasure P] {f : ℝ → Ω → ℝ}
    (hf : Measurable fun p : ℝ × Ω ↦ f p.1 p.2) {C : ℝ} (hC : ∀ u ω, |f u ω| ≤ C)
    (hnn : ∀ u ω, 0 ≤ f u ω) (t : ℝ≥0) :
    ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (f u ω)) ∂P =
      ENNReal.ofReal (∫ ω, (∫ u in (0 : ℝ)..t, f u ω) ∂P) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_intervalIntegral hf hC t)
    (Filter.Eventually.of_forall fun ω ↦ intervalIntegral.integral_nonneg (NNReal.coe_nonneg t)
      fun u _ ↦ hnn u ω)]
  refine lintegral_congr fun ω ↦ ?_
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t), ofReal_integral_eq_lintegral_ofReal]
  · exact (intervalIntegrable_of_bound hf hC t ω).1
  · exact Filter.Eventually.of_forall fun u ↦ hnn u ω

private theorem norm_toLp_sq {P : Measure Ω} {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with ω hω
  simp only [hω, RCLike.inner_apply, conj_trivial]
  ring

namespace ElementaryIntegrand

variable {F : Filtration ℝ≥0 mΩ}

/-- An elementary integrand is jointly measurable in `(u, ω)` (reading `u : ℝ` through
`Real.toNNReal`). -/
theorem measurable_toProcess (H : ElementaryIntegrand F) :
    Measurable (fun p : ℝ × Ω ↦ H.toProcess p.1.toNNReal p.2) := by
  unfold toProcess
  refine Finset.measurable_sum _ fun i _ ↦ ?_
  have : (fun p : ℝ × Ω ↦ (Set.Ioc (H.time i.castSucc) (H.time i.succ)).indicator
      (fun _ ↦ H.coeff i p.2) p.1.toNNReal) =
      {p : ℝ × Ω | p.1.toNNReal ∈ Set.Ioc (H.time i.castSucc) (H.time i.succ)}.indicator
        (fun p ↦ H.coeff i p.2) := by
    funext p
    by_cases h : p.1.toNNReal ∈ Set.Ioc (H.time i.castSucc) (H.time i.succ)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (by exact h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (by exact h)]
  rw [this]
  exact (((H.measurable_coeff i).mono (F.le _) le_rfl).comp measurable_snd).indicator
    (measurableSet_Ioc.preimage (measurable_real_toNNReal.comp measurable_fst))

/-- An elementary integrand with `n` intervals is bounded by `n * bound`. -/
theorem abs_toProcess_le (H : ElementaryIntegrand F) (u : ℝ≥0) (ω : Ω) :
    |H.toProcess u ω| ≤ H.n * H.bound := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _i : Fin H.n, H.bound := Finset.sum_le_sum fun i _ ↦ ?_
    _ = H.n * H.bound := by simp
  by_cases h : u ∈ Set.Ioc (H.time i.castSucc) (H.time i.succ)
  · rw [Set.indicator_of_mem h]; exact H.abs_coeff_le i ω
  · rw [Set.indicator_of_notMem h, abs_zero]
    exact (abs_nonneg _).trans (H.abs_coeff_le i ω)

/-- The elementary Itô integral against a pre-Brownian motion is square integrable. -/
theorem memLp_itoIntegral (H : ElementaryIntegrand F) {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    MemLp (H.itoIntegral B t) 2 P := by
  have hfun : H.itoIntegral B t = ∑ i, (H.coeff i * fun ω ↦
      B (min (H.time i.succ) t) ω - B (min (H.time i.castSucc) t) ω) := by
    funext ω
    simp [itoIntegral, Finset.sum_apply]
  rw [hfun]
  refine memLp_finsetSum' _ fun i _ ↦ ?_
  have hc : MemLp (H.coeff i) ∞ P := memLp_top_of_bound
    ((H.measurable_coeff i).mono (F.le _) le_rfl).aestronglyMeasurable H.bound
    (Filter.Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact H.abs_coeff_le i ω)
  exact hc.mul hB.isGaussianProcess.hasGaussianLaw_fun_sub.memLp_two

private theorem norm_toL2_sub_sq (H K : ElementaryIntegrand F) {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) (t : ℝ≥0) :
    ‖toL2 P (H.itoIntegral B t) - toL2 P (K.itoIntegral B t)‖ ^ 2 =
      (integrandDist P H.toProcess K.toProcess t).toReal := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hH := H.memLp_itoIntegral hB t
  have hK := K.memLp_itoIntegral hB t
  simp only [toL2, hH, hK, ↓reduceDIte]
  rw [← MemLp.toLp_sub hH hK, norm_toLp_sq (hH.sub hK)]
  -- the integrand side
  have hXm := H.measurable_toProcess
  have hYm := K.measurable_toProcess
  have hprodm : ∀ (L M : ElementaryIntegrand F), Measurable fun p : ℝ × Ω ↦
      L.toProcess p.1.toNNReal p.2 * M.toProcess p.1.toNNReal p.2 := fun L M ↦
    L.measurable_toProcess.mul M.measurable_toProcess
  have hprodb : ∀ (L M : ElementaryIntegrand F) u ω,
      |L.toProcess (Real.toNNReal u) ω * M.toProcess (Real.toNNReal u) ω| ≤
        (L.n * L.bound) * (M.n * M.bound) := fun L M u ω ↦ by
    rw [abs_mul]
    exact mul_le_mul (L.abs_toProcess_le _ ω) (M.abs_toProcess_le _ ω) (abs_nonneg _)
      ((abs_nonneg _).trans (L.abs_toProcess_le (Real.toNNReal u) ω))
  have hfm : Measurable fun p : ℝ × Ω ↦
      (H.toProcess p.1.toNNReal p.2 - K.toProcess p.1.toNNReal p.2) ^ 2 :=
    (hXm.sub hYm).pow_const 2
  have hfb : ∀ u ω, |(H.toProcess (Real.toNNReal u) ω - K.toProcess (Real.toNNReal u) ω) ^ 2|
      ≤ (H.n * H.bound + K.n * K.bound) ^ 2 := fun u ω ↦ by
    rw [abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans ?_) 2
    exact add_le_add (H.abs_toProcess_le _ ω) (K.abs_toProcess_le _ ω)
  have hdist : integrandDist P H.toProcess K.toProcess t = ENNReal.ofReal (∫ ω,
      (∫ u in (0 : ℝ)..t, (H.toProcess (Real.toNNReal u) ω -
        K.toProcess (Real.toNNReal u) ω) ^ 2) ∂P) := by
    rw [integrandDist, ← lintegral_lintegral_ofReal hfm hfb (fun _ _ ↦ sq_nonneg _)]
    refine lintegral_congr fun ω ↦ setLIntegral_congr_fun measurableSet_Ioc fun u _ ↦ ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [hdist, ENNReal.toReal_ofReal (integral_nonneg fun ω ↦
    intervalIntegral.integral_nonneg (NNReal.coe_nonneg t) fun u _ ↦ sq_nonneg _)]
  -- pathwise expansion
  have hpath : ∀ ω, (∫ u in (0 : ℝ)..t, (H.toProcess (Real.toNNReal u) ω -
        K.toProcess (Real.toNNReal u) ω) ^ 2) =
      (∫ u in (0 : ℝ)..t, H.toProcess (Real.toNNReal u) ω * H.toProcess (Real.toNNReal u) ω) -
        2 * (∫ u in (0 : ℝ)..t, H.toProcess (Real.toNNReal u) ω *
          K.toProcess (Real.toNNReal u) ω) +
        ∫ u in (0 : ℝ)..t, K.toProcess (Real.toNNReal u) ω * K.toProcess (Real.toNNReal u) ω := by
    intro ω
    have i1 := intervalIntegrable_of_bound (hprodm H H) (hprodb H H) t ω
    have i2 := intervalIntegrable_of_bound (hprodm H K) (hprodb H K) t ω
    have i3 := intervalIntegrable_of_bound (hprodm K K) (hprodb K K) t ω
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub i1 (i2.const_mul 2),
      ← intervalIntegral.integral_add (i1.sub (i2.const_mul 2)) i3]
    congr 1
    funext u
    ring
  simp_rw [hpath]
  have j1 := integrable_intervalIntegral (P := P) (hprodm H H) (hprodb H H) t
  have j2 := integrable_intervalIntegral (P := P) (hprodm H K) (hprodb H K) t
  have j3 := integrable_intervalIntegral (P := P) (hprodm K K) (hprodb K K) t
  have j12 : Integrable (fun ω ↦ (∫ u in (0 : ℝ)..t, H.toProcess (Real.toNNReal u) ω *
      H.toProcess (Real.toNNReal u) ω) - 2 * ∫ u in (0 : ℝ)..t,
        H.toProcess (Real.toNNReal u) ω * K.toProcess (Real.toNNReal u) ω) P :=
    j1.sub (j2.const_mul 2)
  have j2' : Integrable (fun ω ↦ 2 * ∫ u in (0 : ℝ)..t,
        H.toProcess (Real.toNNReal u) ω * K.toProcess (Real.toNNReal u) ω) P := j2.const_mul 2
  rw [integral_add j12 j3, integral_sub j1 j2', integral_const_mul,
    ← integral_itoIntegral_mul H H hB hBF hInd t,
    ← integral_itoIntegral_mul H K hB hBF hInd t, ← integral_itoIntegral_mul K K hB hBF hInd t]
  have k1 : Integrable (fun ω ↦ H.itoIntegral B t ω * H.itoIntegral B t ω) P :=
    hH.integrable_mul hH
  have k2 : Integrable (fun ω ↦ H.itoIntegral B t ω * K.itoIntegral B t ω) P :=
    hH.integrable_mul hK
  have k3 : Integrable (fun ω ↦ K.itoIntegral B t ω * K.itoIntegral B t ω) P :=
    hK.integrable_mul hK
  have k2' : Integrable (fun ω ↦ 2 * (H.itoIntegral B t ω * K.itoIntegral B t ω)) P :=
    k2.const_mul 2
  have k12 : Integrable (fun ω ↦ H.itoIntegral B t ω * H.itoIntegral B t ω -
      2 * (H.itoIntegral B t ω * K.itoIntegral B t ω)) P := k1.sub k2'
  rw [← integral_const_mul, ← integral_sub k1 k2', ← integral_add k12 k3]
  congr 1
  funext ω
  simp only [Pi.sub_apply]
  ring

/-- The `L²(P ⊗ du)` distance between two elementary integrands is finite. -/
theorem integrandDist_ne_top (H K : ElementaryIntegrand F) {P : Measure Ω} [IsFiniteMeasure P]
    (t : ℝ≥0) : integrandDist P H.toProcess K.toProcess t ≠ ⊤ := by
  have hfm : Measurable fun p : ℝ × Ω ↦
      (H.toProcess p.1.toNNReal p.2 - K.toProcess p.1.toNNReal p.2) ^ 2 :=
    (H.measurable_toProcess.sub K.measurable_toProcess).pow_const 2
  have hfb : ∀ u ω, |(H.toProcess (Real.toNNReal u) ω - K.toProcess (Real.toNNReal u) ω) ^ 2|
      ≤ (H.n * H.bound + K.n * K.bound) ^ 2 := fun u ω ↦ by
    rw [abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans ?_) 2
    exact add_le_add (H.abs_toProcess_le _ ω) (K.abs_toProcess_le _ ω)
  have : integrandDist P H.toProcess K.toProcess t = ENNReal.ofReal (∫ ω,
      (∫ u in (0 : ℝ)..t, (H.toProcess (Real.toNNReal u) ω -
        K.toProcess (Real.toNNReal u) ω) ^ 2) ∂P) := by
    rw [integrandDist, ← lintegral_lintegral_ofReal hfm hfb (fun _ _ ↦ sq_nonneg _)]
    refine lintegral_congr fun ω ↦ setLIntegral_congr_fun measurableSet_Ioc fun u _ ↦ ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [this]
  exact ENNReal.ofReal_ne_top

/-- `integrandDist` of two elementary integrands is the squared `L²(P)` distance of their Itô
integrals. -/
theorem integrandDist_eq_dist_sq (H K : ElementaryIntegrand F) {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) (t : ℝ≥0) :
    integrandDist P H.toProcess K.toProcess t =
      ENNReal.ofReal (dist (toL2 P (H.itoIntegral B t)) (toL2 P (K.itoIntegral B t)) ^ 2) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  rw [dist_eq_norm, norm_toL2_sub_sq H K hB hBF hInd t,
    ENNReal.ofReal_toReal (integrandDist_ne_top H K t)]

end ElementaryIntegrand

/-- Pointwise `|x - y|² ≤ 2 |x - z|² + 2 |y - z|²`, integrated: a quasi-triangle inequality
for `integrandDist` between jointly measurable processes. -/
theorem integrandDist_le {P : Measure Ω} {X Y Z : ℝ≥0 → Ω → ℝ}
    (hX : Measurable fun p : ℝ × Ω ↦ X p.1.toNNReal p.2)
    (hY : Measurable fun p : ℝ × Ω ↦ Y p.1.toNNReal p.2)
    (hZ : Measurable fun p : ℝ × Ω ↦ Z p.1.toNNReal p.2) (t : ℝ≥0) :
    integrandDist P X Y t ≤ 2 * integrandDist P X Z t + 2 * integrandDist P Y Z t := by
  have hpt : ∀ x y z : ℝ, ‖x - y‖ₑ ^ 2 ≤ 2 * ‖x - z‖ₑ ^ 2 + 2 * ‖y - z‖ₑ ^ 2 := by
    intro x y z
    simp only [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (x + y - 2 * z)])
  have hin : ∀ {U V : ℝ≥0 → Ω → ℝ}, (Measurable fun p : ℝ × Ω ↦ U p.1.toNNReal p.2) →
      (Measurable fun p : ℝ × Ω ↦ V p.1.toNNReal p.2) → ∀ ω,
      Measurable fun u : ℝ ↦ ‖U u.toNNReal ω - V u.toNNReal ω‖ₑ ^ 2 :=
    fun hU hV ω ↦ (((hU.sub hV).comp (measurable_id.prodMk measurable_const)).enorm).pow_const 2
  have hout : ∀ {U V : ℝ≥0 → Ω → ℝ}, (Measurable fun p : ℝ × Ω ↦ U p.1.toNNReal p.2) →
      (Measurable fun p : ℝ × Ω ↦ V p.1.toNNReal p.2) →
      Measurable fun ω ↦ ∫⁻ u in Set.Ioc (0 : ℝ) t, ‖U u.toNNReal ω - V u.toNNReal ω‖ₑ ^ 2 :=
    fun {U V} hU hV ↦ Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Ioc (0 : ℝ) t))
      (f := fun p : Ω × ℝ ↦ ‖U p.2.toNNReal p.1 - V p.2.toNNReal p.1‖ₑ ^ 2)
      ((((hU.sub hV).comp measurable_swap).enorm).pow_const 2)
  calc integrandDist P X Y t
      ≤ ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, 2 * ‖X u.toNNReal ω - Z u.toNNReal ω‖ₑ ^ 2 +
          2 * ‖Y u.toNNReal ω - Z u.toNNReal ω‖ₑ ^ 2) ∂P :=
        lintegral_mono fun ω ↦ lintegral_mono fun u ↦ hpt _ _ _
    _ = 2 * integrandDist P X Z t + 2 * integrandDist P Y Z t := by
        rw [integrandDist, integrandDist, ← lintegral_const_mul, ← lintegral_const_mul,
          ← lintegral_add_left]
        · refine lintegral_congr fun ω ↦ ?_
          rw [lintegral_add_left, lintegral_const_mul, lintegral_const_mul]
          · exact hin hY hZ ω
          · exact hin hX hZ ω
          · exact (hin hX hZ ω).const_mul _
        · exact (hout hX hZ).const_mul _
        · exact hout hY hZ
        · exact hout hX hZ

private theorem tendsto_of_ofReal_sq {ι : Type*} {l : Filter ι} {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i)
    (h : Tendsto (fun i ↦ ENNReal.ofReal (f i ^ 2)) l (𝓝 0)) : Tendsto f l (𝓝 0) := by
  have h2 : Tendsto (fun i ↦ f i ^ 2) l (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    simpa [Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _)] using this
  have := (Real.continuous_sqrt.tendsto 0).comp h2
  simpa [Function.comp_def, Real.sqrt_sq (hf _)] using this

private theorem tendsto_dist_toL2 {F : Filtration ℝ≥0 mΩ} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) {H : ℝ≥0 → Ω → ℝ} {t : ℝ≥0}
    (hH : Measurable fun p : ℝ × Ω ↦ H p.1.toNNReal p.2) {ι : Type*} {l : Filter ι}
    {A C : ι → ElementaryIntegrand F}
    (hA : Tendsto (fun i ↦ integrandDist P (A i).toProcess H t) l (𝓝 0))
    (hC : Tendsto (fun i ↦ integrandDist P (C i).toProcess H t) l (𝓝 0)) :
    Tendsto (fun i ↦ dist (toL2 P ((A i).itoIntegral B t)) (toL2 P ((C i).itoIntegral B t)))
      l (𝓝 0) := by
  refine tendsto_of_ofReal_sq (fun _ ↦ dist_nonneg) ?_
  have hup : Tendsto (fun i ↦ 2 * integrandDist P (A i).toProcess H t +
      2 * integrandDist P (C i).toProcess H t) l (𝓝 0) := by
    simpa using (ENNReal.Tendsto.const_mul hA (Or.inr ENNReal.ofNat_ne_top)).add
      (ENNReal.Tendsto.const_mul hC (Or.inr ENNReal.ofNat_ne_top))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ ↦ bot_le)
    fun i ↦ ?_
  rw [← ElementaryIntegrand.integrandDist_eq_dist_sq _ _ hB hBF hInd t]
  exact integrandDist_le (A i).measurable_toProcess (C i).measurable_toProcess hH t

/-- **The Itô integral is well defined.** For a pre-Brownian motion `B` adapted to `F` with
increments independent of the past, a jointly measurable `H`, and *any* sequence of elementary
integrands `Kn` converging to `H` in `L²(P ⊗ du)` on `(0, t] × Ω`, the elementary Itô integrals
of `Kn` converge in `L²(P)` to `itoIntegralL2 P F B H t`. -/
theorem tendsto_toL2_itoIntegral {F : Filtration ℝ≥0 mΩ} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) {H : ℝ≥0 → Ω → ℝ} {t : ℝ≥0}
    (hH : Measurable fun p : ℝ × Ω ↦ H p.1.toNNReal p.2) {Kn : ℕ → ElementaryIntegrand F}
    (hK : Tendsto (fun n ↦ integrandDist P (Kn n).toProcess H t) atTop (𝓝 0)) :
    Tendsto (fun n ↦ toL2 P ((Kn n).itoIntegral B t)) atTop (𝓝 (itoIntegralL2 P F B H t)) := by
  have happ : IsItoApproximable P F H t := ⟨hH, Kn, hK⟩
  have hHn := happ.2.choose_spec
  have hc : CauchySeq fun n ↦ toL2 P ((happ.2.choose n).itoIntegral B t) := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0, ← prod_atTop_atTop_eq]
    exact tendsto_dist_toL2 hB hBF hInd hH (hHn.comp tendsto_fst) (hHn.comp tendsto_snd)
  have hlim := tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete hc)
  have heq : itoIntegralL2 P F B H t =
      limUnder atTop fun n ↦ toL2 P ((happ.2.choose n).itoIntegral B t) := by
    simp only [itoIntegralL2, happ, ↓reduceDIte]
  rw [heq]
  exact hlim.congr_dist (tendsto_dist_toL2 hB hBF hInd hH hHn hK)

/-- An elementary integrand is Itô-approximable on every `[0, t]` (by itself). -/
theorem isItoApproximable_toProcess {F : Filtration ℝ≥0 mΩ} (P : Measure Ω)
    (K : ElementaryIntegrand F) (t : ℝ≥0) : IsItoApproximable P F K.toProcess t :=
  ⟨K.measurable_toProcess, fun _ ↦ K, by simp [integrandDist]⟩

/-- On an elementary integrand, the Itô integral agrees almost surely with the elementary Itô
integral. -/
theorem itoIntegral_toProcess_ae_eq {F : Filtration ℝ≥0 mΩ} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) (K : ElementaryIntegrand F) (t : ℝ≥0) :
    itoIntegral P F B K.toProcess t =ᵐ[P] K.itoIntegral B t := by
  have h0 : integrandDist P K.toProcess K.toProcess t = 0 := by simp [integrandDist]
  have hlim := tendsto_toL2_itoIntegral hB hBF hInd K.measurable_toProcess
    (Kn := fun _ ↦ K) (by rw [h0]; exact tendsto_const_nhds)
  have heq := tendsto_nhds_unique tendsto_const_nhds hlim
  have hK := K.memLp_itoIntegral hB t
  refine (itoIntegral_ae_eq P F B K.toProcess t).trans ?_
  rw [← heq]
  simp only [toL2, hK, ↓reduceDIte]
  exact hK.coeFn_toLp

/-- **Elementary integrands.** For `a ≤ b` and a bounded `F a`-measurable `ξ`, the Itô integral
of `ξ 1_{(a, b]}` against a pre-Brownian motion `B` adapted to `F` with increments independent
of the past is `ξ (B (b ∧ t) - B (a ∧ t))` almost surely (Karatzas–Shreve 1991,
Section 3.2.A). -/
theorem itoIntegral_indicator_Ioc {F : Filtration ℝ≥0 mΩ} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) {a b : ℝ≥0} (hab : a ≤ b) {ξ : Ω → ℝ} (hξ : Measurable[F a] ξ) (C : ℝ)
    (hξC : ∀ ω, |ξ ω| ≤ C) (t : ℝ≥0) :
    itoIntegral P F B (fun u ω ↦ Set.indicator (Set.Ioc a b) (fun _ ↦ ξ ω) u) t =ᵐ[P]
      fun ω ↦ ξ ω * (B (min b t) ω - B (min a t) ω) := by
  have h := itoIntegral_toProcess_ae_eq hB hBF hInd
    (ElementaryIntegrand.single a b hab ξ hξ C hξC) t
  rw [ElementaryIntegrand.toProcess_single] at h
  refine h.trans (Filter.Eventually.of_forall fun ω ↦ ?_)
  exact ElementaryIntegrand.itoIntegral_single a b hab ξ hξ C hξC B t ω

/-- On `(t k / n, t (k + 1) / n]` the left-point approximation equals `g (t k / n)`. -/
private theorem abs_toProcess_riemann_sub_le {F : Filtration ℝ≥0 mΩ} {g : ℝ → ℝ} {t : ℝ≥0}
    {n : ℕ} {η δ : ℝ} (hδ : ∀ x ∈ Set.Icc (0 : ℝ) t, ∀ y ∈ Set.Icc (0 : ℝ) t,
      dist x y < δ → dist (g x) (g y) < η) (hn0 : 0 < n) (hn : (t : ℝ) / n < δ) {u : ℝ}
    (hu : u ∈ Set.Ioc (0 : ℝ) t) (ω : Ω) :
    |(ElementaryIntegrand.riemann F g t n).toProcess u.toNNReal ω - g u| ≤ η := by
  have ht : (0 : ℝ) < t := hu.1.trans_le hu.2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  set x : ℝ := u * n / t with hx
  have hxpos : 0 < x := div_pos (mul_pos hu.1 hnR) ht
  set k : ℕ := ⌈x⌉₊ - 1 with hk
  have hceil1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hxpos).ne'
  have hk1 : ((k + 1 : ℕ) : ℝ) = ⌈x⌉₊ := by rw [hk, Nat.sub_add_cancel hceil1]
  have hxle : x ≤ ((k + 1 : ℕ) : ℝ) := hk1 ▸ Nat.le_ceil x
  have hkx : (k : ℝ) < x := by
    have := Nat.ceil_lt_add_one hxpos.le
    have h2 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    linarith [hk1]
  have hxt : x ≤ n := by
    rw [hx, div_le_iff₀ ht]; nlinarith [hu.2]
  have hkn : k < n := by
    have : (k : ℝ) < n := hkx.trans_le hxt
    exact_mod_cast this
  -- the interval containing `u`
  have hlo : (t : ℝ) * k / n < u := by
    rw [div_lt_iff₀ hnR]; rw [hx, lt_div_iff₀ ht] at hkx; linarith
  have hhi : u ≤ (t : ℝ) * ((k + 1 : ℕ) : ℝ) / n := by
    rw [le_div_iff₀ hnR]; rw [hx, div_le_iff₀ ht] at hxle; linarith
  have hmem : u.toNNReal ∈ Set.Ioc ((ElementaryIntegrand.riemann F g t n).time
      (⟨k, hkn⟩ : Fin n).castSucc) ((ElementaryIntegrand.riemann F g t n).time
        (⟨k, hkn⟩ : Fin n).succ) := by
    simp only [ElementaryIntegrand.riemann, Set.mem_Ioc, Fin.val_castSucc, Fin.val_succ]
    rw [← NNReal.coe_lt_coe, ← NNReal.coe_le_coe, Real.coe_toNNReal _ hu.1.le]
    push_cast at hlo hhi ⊢
    exact ⟨hlo, hhi⟩
  rw [ElementaryIntegrand.toProcess_eq_of_mem _ hmem]
  simp only [ElementaryIntegrand.riemann, Fin.val_castSucc]
  have hsk : ((t * (k : ℝ≥0) / n : ℝ≥0) : ℝ) = (t : ℝ) * k / n := by push_cast; ring
  rw [hsk, ← Real.dist_eq]
  refine (hδ _ ⟨by positivity, ?_⟩ u ⟨hu.1.le, hu.2⟩ ?_).le
  · rw [div_le_iff₀ hnR]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hkn.le) ht.le
  · rw [Real.dist_eq, abs_of_neg (by linarith)]
    have : u - (t : ℝ) * k / n ≤ (t : ℝ) / n := by
      have h2 : (t : ℝ) * ((k + 1 : ℕ) : ℝ) / n = (t : ℝ) * k / n + t / n := by
        push_cast; ring
      linarith
    linarith

/-- The left-point approximations of a continuous deterministic `g` converge to `g` in
`L²(P ⊗ du)` on `(0, t] × Ω`. -/
theorem tendsto_integrandDist_riemann {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
    [IsProbabilityMeasure P] {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ≥0) :
    Tendsto (fun n ↦ integrandDist P (ElementaryIntegrand.riemann F g t n).toProcess
      (fun u _ ↦ g u) t) atTop (𝓝 0) := by
  rcases eq_zero_or_pos t with ht | ht
  · subst ht
    simp [integrandDist]
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous
    (hg.continuousOn (s := Set.Icc (0 : ℝ) t))
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with hεt | hεt
  · simp [hεt]
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
  set η := Real.sqrt (ε.toReal / t) with hη
  have hηpos : 0 < η := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuousOn_iff.mp huc η hηpos
  obtain ⟨N, hN⟩ := exists_nat_gt ((t : ℝ) / δ)
  filter_upwards [eventually_gt_atTop N] with n hn
  have hmesh : (t : ℝ) / n < δ := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_le N).trans_lt hn
    rw [div_lt_iff₀ hnR]
    rw [div_lt_iff₀ hδ] at hN
    calc (t : ℝ) < N * δ := hN
      _ ≤ δ * n := by rw [mul_comm]; gcongr
  calc integrandDist P (ElementaryIntegrand.riemann F g t n).toProcess (fun u _ ↦ g u) t
      ≤ ∫⁻ _ω, (∫⁻ _u in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (η ^ 2)) ∂P := by
        refine lintegral_mono fun ω ↦ setLIntegral_mono measurable_const fun u hu ↦ ?_
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _)]
        refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _) ?_ 2)
        have := abs_toProcess_riemann_sub_le (F := F) (ω := ω) hδg
          ((Nat.zero_le N).trans_lt hn) hmesh hu
        simpa only [Real.coe_toNNReal _ hu.1.le] using this
    _ = ε := by
        rw [lintegral_const, setLIntegral_const, Real.volume_Ioc, sub_zero, measure_univ,
          mul_one, ← ENNReal.ofReal_mul (sq_nonneg _), hη, Real.sq_sqrt (by positivity),
          div_mul_cancel₀ _ htR.ne', ENNReal.ofReal_toReal hεt]

/-- **Wiener's integration by parts.** For a Brownian motion `B` adapted to `F` with
increments independent of the past and a deterministic `C¹` integrand `g`, the Itô integral is
`∫_0^t g dB = g t B t - g 0 B 0 - ∫_0^t g'(u) B u du` almost surely (Karatzas–Shreve 1991,
Section 3.3; the right side is a pathwise Riemann integral). -/
theorem itoIntegral_deterministic_eq {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (t : ℝ≥0) :
    itoIntegral P F B (fun u _ ↦ g u) t =ᵐ[P]
      fun ω ↦ g t * B t ω - g 0 * B 0 ω -
        ∫ u in (0 : ℝ)..t, deriv g u * B (Real.toNNReal u) ω := by
  have hpre := hB.toIsPreBrownianReal
  have := hpre.isGaussianProcess.isProbabilityMeasure
  have hHm : Measurable fun p : ℝ × Ω ↦ (fun u _ ↦ g u : ℝ≥0 → Ω → ℝ) p.1.toNNReal p.2 :=
    (hg.continuous.measurable.comp (NNReal.continuous_coe.measurable.comp
      measurable_real_toNNReal)).comp measurable_fst
  have hlim := tendsto_toL2_itoIntegral hpre hBF hInd hHm
    (tendsto_integrandDist_riemann (F := F) (P := P) hg.continuous t)
  obtain ⟨ns, hns_mono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hrep : ∀ n, (toL2 P ((ElementaryIntegrand.riemann F g t n).itoIntegral B t) : Ω → ℝ)
      =ᵐ[P] (ElementaryIntegrand.riemann F g t n).itoIntegral B t := fun n ↦ by
    have hm := (ElementaryIntegrand.riemann F g t n).memLp_itoIntegral hpre t
    simp only [toL2, hm, ↓reduceDIte]
    exact hm.coeFn_toLp
  refine (itoIntegral_ae_eq P F B _ t).trans ?_
  filter_upwards [hns, ae_all_iff.2 hrep, hB.cont] with ω h1 h2 h3
  have h4 := (ElementaryIntegrand.tendsto_itoIntegral_riemann F hg h3 t).comp
    hns_mono.tendsto_atTop
  refine tendsto_nhds_unique h1 ?_
  refine h4.congr fun i ↦ ?_
  simp only [Function.comp_apply]
  exact (h2 (ns i)).symm

/-- **The Ornstein–Uhlenbeck solution in Itô form.** For a Brownian motion `B` adapted to `F`
with increments independent of the past, any initial value `X₀` and any real `θ`, `σ`, the Itô
form `e^{-θt} X₀ + σ e^{-θt} ∫_0^t e^{θs} dB_s = e^{-θt} X₀ + σ ∫_0^t e^{-θ(t-s)} dB_s` of the
solution of `dX = -θ X dt + σ dB` (Karatzas–Shreve 1991, Section 5.6) agrees almost surely with
the pathwise solution `ouPathSolution`, which solves `X t = X₀ - θ ∫_0^t X + σ (B t - B 0)` path
by path (`ProbabilityTheory.ouPathSolution_integral_eq`). -/
theorem ito_ou_solution_eq_ouPathSolution {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) (θ σ : ℝ) (X₀ : Ω → ℝ) (t : ℝ≥0) :
    (fun ω ↦ exp (-θ * t) * X₀ ω +
        σ * exp (-θ * t) * itoIntegral P F B (fun u _ ↦ exp (θ * u)) t ω) =ᵐ[P]
      fun ω ↦ ouPathSolution θ σ (X₀ ω) (fun u ↦ B (Real.toNNReal u) ω) t := by
  have hg : ContDiff ℝ 1 (fun u : ℝ ↦ exp (θ * u)) := by fun_prop
  filter_upwards [itoIntegral_deterministic_eq hB hBF hInd hg t] with ω hω
  rw [hω, ouPathSolution_eq_integration_by_parts, Real.toNNReal_coe, Real.toNNReal_zero]

private theorem integrandDist_mono_time {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ} {s t : ℝ≥0}
    (hst : s ≤ t) : integrandDist P X Y s ≤ integrandDist P X Y t :=
  lintegral_mono fun _ ↦ lintegral_mono_set (Set.Ioc_subset_Ioc_right (by exact_mod_cast hst))

private theorem coe_toL2_ae_eq {P : Measure Ω} {f : Ω → ℝ} (hf : MemLp f 2 P) :
    (toL2 P f : Ω → ℝ) =ᵐ[P] f := by
  simp only [toL2, hf, ↓reduceDIte]
  exact hf.coeFn_toLp

/-- The `L²` Itô integral is (almost surely equal to) an `F t`-measurable function. -/
theorem aestronglyMeasurable_itoIntegralL2 {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) {H : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} (hH : IsItoApproximable P F H t) :
    AEStronglyMeasurable[F t] (itoIntegralL2 P F B H t) P := by
  obtain ⟨hHm, Kn, hK⟩ := hH
  have hlim := tendsto_toL2_itoIntegral hB hBF hInd hHm hK
  refine (isClosed_aestronglyMeasurable (F.le t)).mem_of_tendsto hlim
    (Filter.Eventually.of_forall fun n ↦ ?_)
  have hm := ((Kn n).martingale_itoIntegral hB hBF hInd).1 t
  exact ⟨_, hm, coe_toL2_ae_eq ((Kn n).memLp_itoIntegral hB t)⟩

/-- **Martingale property of the Itô integral.** For a pre-Brownian motion `B` adapted to `F`
with increments independent of the past and an integrand `H` that is Itô-approximable on every
`[0, t]`, the Itô integral `t ↦ ∫_0^t H dB` is an `F`-martingale (Karatzas–Shreve 1991,
Proposition 3.2.10). -/
theorem martingale_itoIntegral {F : Filtration ℝ≥0 mΩ} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) {H : ℝ≥0 → Ω → ℝ} (hH : ∀ t, IsItoApproximable P F H t) :
    Martingale (itoIntegral P F B H) F P := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨fun t ↦ ?_, fun s t hst ↦ ?_⟩
  · have h := aestronglyMeasurable_itoIntegralL2 hB hBF hInd (hH t)
    simp only [itoIntegral, h, ↓reduceDIte]
    exact h.stronglyMeasurable_mk
  -- approximate on `[0, t]`; the same sequence approximates on `[0, s]`
  obtain ⟨hHm, Kn, hK⟩ := hH t
  have hKs : Tendsto (fun n ↦ integrandDist P (Kn n).toProcess H s) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hK (fun _ ↦ bot_le)
      fun _ ↦ integrandDist_mono_time hst
  have hlt := tendsto_toL2_itoIntegral hB hBF hInd hHm hK
  have hls := tendsto_toL2_itoIntegral hB hBF hInd hHm hKs
  set CE := condExpL2 ℝ ℝ (μ := P) (F.le s)
  have hce : Tendsto (fun n ↦ ((CE (toL2 P ((Kn n).itoIntegral B t)) : Lp ℝ 2 P))) atTop
      (𝓝 (CE (itoIntegralL2 P F B H t) : Lp ℝ 2 P)) :=
    (continuous_subtype_val.tendsto _).comp ((CE.continuous.tendsto _).comp hlt)
  have heqn : ∀ n, ((CE (toL2 P ((Kn n).itoIntegral B t)) : Lp ℝ 2 P)) =
      toL2 P ((Kn n).itoIntegral B s) := by
    intro n
    have hmt := (Kn n).memLp_itoIntegral hB t
    have hms := (Kn n).memLp_itoIntegral hB s
    refine Lp.ext ?_
    have h1 : toL2 P ((Kn n).itoIntegral B t) = hmt.toLp _ := by
      simp only [toL2, hmt, ↓reduceDIte]
    rw [h1]
    refine (hmt.condExpL2_ae_eq_condExp (F.le s)).trans ?_
    refine (((Kn n).martingale_itoIntegral hB hBF hInd).2 s t hst).trans ?_
    exact (coe_toL2_ae_eq hms).symm
  simp_rw [heqn] at hce
  have hCE := tendsto_nhds_unique hce hls
  -- conclude
  have hL := Lp.memLp (itoIntegralL2 P F B H t)
  refine (condExp_congr_ae (itoIntegral_ae_eq P F B H t)).trans ?_
  refine (hL.condExpL2_ae_eq_condExp (𝕜 := ℝ) (F.le s)).symm.trans ?_
  rw [Lp.toLp_coeFn _ hL, hCE]
  exact (itoIntegral_ae_eq P F B H s).symm

private theorem integrandDist_eq_eLpNorm_sq {P : Measure Ω} [IsFiniteMeasure P]
    {X Y : ℝ≥0 → Ω → ℝ} (hX : Measurable fun p : ℝ × Ω ↦ X p.1.toNNReal p.2)
    (hY : Measurable fun p : ℝ × Ω ↦ Y p.1.toNNReal p.2) (t : ℝ≥0) :
    integrandDist P X Y t = eLpNorm (fun p : Ω × ℝ ↦ X p.2.toNNReal p.1 - Y p.2.toNNReal p.1) 2
      (P.prod (volume.restrict (Set.Ioc (0 : ℝ) t))) ^ 2 := by
  have hm : Measurable fun p : Ω × ℝ ↦ X p.2.toNNReal p.1 - Y p.2.toNNReal p.1 :=
    (hX.sub hY).comp measurable_swap
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := P.prod (volume.restrict (Set.Ioc (0 : ℝ) t)))
    (p := 2) two_ne_zero hm.aestronglyMeasurable
  simp only [NNReal.coe_ofNat, ENNReal.rpow_two, ENNReal.coe_ofNat] at h
  rw [h, lintegral_prod _ (hm.enorm.pow_const 2).aemeasurable]
  rfl

/-- The empty elementary integrand (no intervals). -/
private def zeroIntegrand (F : Filtration ℝ≥0 mΩ) : ElementaryIntegrand F where
  n := 0
  time := fun _ ↦ 0
  monotone_time := fun _ _ _ ↦ le_rfl
  coeff := fun i ↦ i.elim0
  measurable_coeff := fun i ↦ i.elim0
  bound := 0
  abs_coeff_le := fun i ↦ i.elim0

/-- **Itô isometry** for the `L²` Itô integral, in `ℝ≥0∞` form: for a pre-Brownian motion `B`
adapted to `F` with increments independent of the past and an integrand `H` that is
Itô-approximable on `[0, t]`, `E[(∫_0^t H dB)²] = E ∫_0^t H_u² du` (Karatzas–Shreve 1991,
Section 3.2). -/
theorem lintegral_itoIntegral_sq {F : Filtration ℝ≥0 mΩ} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) {H : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} (hH : IsItoApproximable P F H t) :
    ∫⁻ ω, ‖itoIntegral P F B H t ω‖ₑ ^ 2 ∂P =
      ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) ∂P := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨hHm, Kn, hK⟩ := hH
  set μ' := P.prod (volume.restrict (Set.Ioc (0 : ℝ) t))
  have h0m : Measurable fun p : ℝ × Ω ↦ (fun (_ : ℝ≥0) (_ : Ω) ↦ (0 : ℝ)) p.1.toNNReal p.2 :=
    measurable_const
  have hZ : (zeroIntegrand F).toProcess = fun _ _ ↦ 0 := by
    funext u ω; simp [ElementaryIntegrand.toProcess, zeroIntegrand]
  have hZI : toL2 P ((zeroIntegrand F).itoIntegral B t) = 0 := by
    have : (zeroIntegrand F).itoIntegral B t = 0 := by
      funext ω; simp [ElementaryIntegrand.itoIntegral, zeroIntegrand]
    rw [this]
    simp only [toL2, MemLp.zero, ↓reduceDIte, MemLp.toLp_zero]
  -- norms of the elementary integrals
  have hnormK : ∀ n, ENNReal.ofReal (‖toL2 P ((Kn n).itoIntegral B t)‖ ^ 2) =
      eLpNorm (fun p : Ω × ℝ ↦ (Kn n).toProcess p.2.toNNReal p.1) 2 μ' ^ 2 := by
    intro n
    have h := ElementaryIntegrand.integrandDist_eq_dist_sq (Kn n) (zeroIntegrand F) hB hBF hInd t
    rw [hZI, dist_zero_right, hZ, integrandDist_eq_eLpNorm_sq (Kn n).measurable_toProcess h0m]
      at h
    simpa using h.symm
  have hfin : ∀ n, eLpNorm (fun p : Ω × ℝ ↦ (Kn n).toProcess p.2.toNNReal p.1) 2 μ' ≠ ⊤ := by
    intro n h
    have := hnormK n
    rw [h, ENNReal.top_pow two_ne_zero] at this
    exact ENNReal.ofReal_ne_top this
  -- the approximation in `L²(μ')`
  set e : ℕ → ℝ≥0∞ := fun n ↦ eLpNorm (fun p : Ω × ℝ ↦ (Kn n).toProcess p.2.toNNReal p.1 -
    H p.2.toNNReal p.1) 2 μ'
  have he : Tendsto e atTop (𝓝 0) := by
    have h2 : Tendsto (fun n ↦ e n ^ 2) atTop (𝓝 0) := by
      refine hK.congr fun n ↦ ?_
      exact integrandDist_eq_eLpNorm_sq (Kn n).measurable_toProcess hHm t
    have key : ∀ x : ℝ≥0∞, (x ^ 2) ^ ((2 : ℝ)⁻¹) = x := fun x ↦ by
      simpa using ENNReal.pow_rpow_inv_natCast (n := 2) two_ne_zero x
    have := (ENNReal.continuous_rpow_const (y := (2 : ℝ)⁻¹)).tendsto 0 |>.comp h2
    simpa [Function.comp_def, key, ENNReal.zero_rpow_of_pos] using this
  set NH := eLpNorm (fun p : Ω × ℝ ↦ H p.2.toNNReal p.1) 2 μ'
  have hle1 : ∀ n, NH ≤ eLpNorm (fun p : Ω × ℝ ↦ (Kn n).toProcess p.2.toNNReal p.1) 2 μ' + e n :=
    fun n ↦ by
      have := eLpNorm_sub_le (μ := μ') (p := 2) (f := fun p : Ω × ℝ ↦
        (Kn n).toProcess p.2.toNNReal p.1) (g := fun p : Ω × ℝ ↦
          (Kn n).toProcess p.2.toNNReal p.1 - H p.2.toNNReal p.1) one_le_two
      have heq : ((fun p : Ω × ℝ ↦ (Kn n).toProcess p.2.toNNReal p.1) - fun p : Ω × ℝ ↦
          (Kn n).toProcess p.2.toNNReal p.1 - H p.2.toNNReal p.1) =
          fun p : Ω × ℝ ↦ H p.2.toNNReal p.1 := by
        funext p; simp
      rwa [heq] at this
  have hle2 : ∀ n, eLpNorm (fun p : Ω × ℝ ↦ (Kn n).toProcess p.2.toNNReal p.1) 2 μ' ≤ NH + e n :=
    fun n ↦ by
      have := eLpNorm_add_le (μ := μ') (p := 2) (f := fun p : Ω × ℝ ↦ H p.2.toNNReal p.1)
        (g := fun p : Ω × ℝ ↦ (Kn n).toProcess p.2.toNNReal p.1 - H p.2.toNNReal p.1)
        one_le_two
      have heq : ((fun p : Ω × ℝ ↦ H p.2.toNNReal p.1) + fun p : Ω × ℝ ↦
          (Kn n).toProcess p.2.toNNReal p.1 - H p.2.toNNReal p.1) =
          fun p : Ω × ℝ ↦ (Kn n).toProcess p.2.toNNReal p.1 := by
        funext p; simp
      rwa [heq] at this
  have hNH : NH ≠ ⊤ := by
    obtain ⟨n, hn⟩ := (he.eventually (gt_mem_nhds zero_lt_one)).exists
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hfin n, (hn.trans ENNReal.one_lt_top).ne⟩)
      (hle1 n)
  have hconv : Tendsto (fun n ↦ eLpNorm (fun p : Ω × ℝ ↦ (Kn n).toProcess p.2.toNNReal p.1) 2 μ')
      atTop (𝓝 NH) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n ↦ NH - e n)
      (h := fun n ↦ NH + e n) ?_ ?_ (fun n ↦ tsub_le_iff_right.mpr (hle1 n)) hle2
    · simpa using ENNReal.Tendsto.sub tendsto_const_nhds he (Or.inl hNH)
    · simpa using (tendsto_const_nhds (x := NH)).add he
  -- identify the limit
  have hlim := tendsto_toL2_itoIntegral hB hBF hInd hHm hK
  have hA : Tendsto (fun n ↦ ENNReal.ofReal (‖toL2 P ((Kn n).itoIntegral B t)‖ ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (‖itoIntegralL2 P F B H t‖ ^ 2))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      (((continuous_norm.tendsto _).comp hlim).pow 2)
  simp_rw [hnormK] at hA
  have hEq := tendsto_nhds_unique hA (ENNReal.Tendsto.pow hconv)
  -- the two sides
  have hL := Lp.memLp (itoIntegralL2 P F B H t)
  have hlhs : ∫⁻ ω, ‖itoIntegral P F B H t ω‖ₑ ^ 2 ∂P =
      ENNReal.ofReal (‖itoIntegralL2 P F B H t‖ ^ 2) := by
    rw [← Lp.toLp_coeFn _ hL, norm_toLp_sq hL,
      ofReal_integral_eq_lintegral_ofReal hL.integrable_sq
        (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)]
    refine lintegral_congr_ae ?_
    filter_upwards [itoIntegral_ae_eq P F B H t] with ω hω
    rw [hω, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have hrhs : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) ∂P = NH ^ 2 := by
    have := integrandDist_eq_eLpNorm_sq (P := P) (Y := fun _ _ ↦ 0) hHm h0m t
    simpa [integrandDist, NH, μ'] using this
  rw [hlhs, hrhs, hEq]

end ProbabilityTheory
