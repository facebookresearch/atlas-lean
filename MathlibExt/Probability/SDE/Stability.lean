/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.ItoAdaptedContinuous
public import MathlibExt.Probability.SDE.LipschitzIntegrands
public import MathlibExt.Probability.SDE.TimeIntegrals
import MathlibExt.Analysis.ODE.GronwallIntegral
import Mathlib.Tactic.Finiteness

/-!
# Quantitative stability and uniqueness of scalar Lipschitz SDEs

A solution is adapted, has continuous paths and locally finite integrated second
moments, and satisfies the actual Itô-plus-time-integral equation at every fixed
time almost surely. Fixed-time square integrability is derived from that equation.

The difference isometry, ordinary Cauchy–Schwarz and integral Gronwall give an
explicit mean-square stability estimate. Equal initial values then give
indistinguishability. These results keep the original filtration and only need
pre-Brownian laws and independence of increments from the past; neither complete
filtrations nor continuous integrator paths are required for uniqueness.

This is the standard Lipschitz uniqueness argument of Le Gall, *Brownian Motion,
Martingales, and Stochastic Calculus* (2016), Theorem 8.3, and Karatzas–Shreve,
*Brownian Motion and Stochastic Calculus* (1991), Section 5.2. The factor three
comes from a nonoptimal three-term square estimate. Existence is not asserted.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- A scalar solution of `dX = σ(X) dB + b(X) dt`, using the existing actual
Itô integral: adapted, continuous on every path, with finite integrated energy
on every finite horizon, and satisfying the fixed-time almost-sure equation.
No target moment estimate, convergence or uniqueness is part of this predicate. -/
def IsScalarSDESolution {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ)
    (σ b : ℝ → ℝ) (x : ℝ) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  Adapted F X ∧ (∀ ω, Continuous fun t ↦ X t ω) ∧
    (∀ t, integrandDist P X (fun _ _ ↦ 0) t ≠ ∞) ∧
    ∀ t, ∀ᵐ ω ∂P, X t ω = x + itoIntegral P F B (fun s ω ↦ σ (X s ω)) t ω +
      ∫ s in (0 : ℝ)..t, b (X s.toNNReal ω)

/-- Adaptedness and path continuity of a scalar solution imply progressiveness. -/
theorem IsScalarSDESolution.isProgressive {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B X : ℝ≥0 → Ω → ℝ}
    {σ b : ℝ → ℝ} {x : ℝ} (hX : IsScalarSDESolution P F B σ b x X) :
    IsProgressive F X :=
  (hX.1.stronglyAdapted.isStronglyProgressive_of_continuous hX.2.1).isProgressive

/-- A solution is square integrable at each fixed time when the drift is Lipschitz
and the ambient measure is finite. The stochastic integral already takes values
in `L²`; the drift integral's square integrability follows from input energy. -/
theorem IsScalarSDESolution.memLp {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {B X : ℝ≥0 → Ω → ℝ} {σ b : ℝ → ℝ} {x : ℝ}
    (hX : IsScalarSDESolution P F B σ b x X) {K : ℝ≥0}
    (hb : LipschitzWith K b) (t : ℝ≥0) : MemLp (X t) 2 P := by
  have hbp : IsProgressive F (fun s ω ↦ b (X s ω)) :=
    fun T ↦ hb.continuous.measurable.comp (hX.isProgressive T)
  have hbc : ∀ ω, Continuous (fun s ↦ b (X s ω)) :=
    fun ω ↦ hb.continuous.comp (hX.2.1 ω)
  have hd := memLp_timeIntegral hbp hbc t
    (integrandDist_comp_zero_ne_top hX.isProgressive hb t (hX.2.2.1 t))
  have hi := memLp_itoIntegral P F B (fun s ω ↦ σ (X s ω)) t
  have he : (fun ω ↦ x + itoIntegral P F B (fun s ω ↦ σ (X s ω)) t ω +
      ∫ s in (0 : ℝ)..t, b (X s.toNNReal ω)) =ᵐ[P] X t := by
    filter_upwards [hX.2.2.2 t] with ω hω
    exact hω.symm
  exact ((memLp_const x).add hi |>.add hd).ae_eq he

private theorem finite_difference_energy {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}
    (hX : IsProgressive F X) (hY : IsProgressive F Y) (T : ℝ≥0)
    (hx : integrandDist P X (fun _ _ ↦ 0) T ≠ ∞)
    (hy : integrandDist P Y (fun _ _ ↦ 0) T ≠ ∞) :
    integrandDist P X Y T ≠ ∞ := by
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (by norm_num) hx, ENNReal.mul_ne_top (by norm_num) hy⟩)
    (integrandDist_le (IsProgressive.measurable_toNNReal hX)
      (IsProgressive.measurable_toNNReal hY) measurable_const T)

private theorem finite_sq_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 P) : ∫⁻ ω, ‖f ω‖ₑ^2 ∂P ≠ ∞ := by
  have h := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hf
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using h.ne

private theorem moment_integrable {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X Y : ℝ≥0 → Ω → ℝ} (hX : IsProgressive F X) (hY : IsProgressive F Y)
    (T : ℝ≥0) (hE : integrandDist P X Y T ≠ ∞) :
    IntegrableOn (fun s : ℝ ↦ (∫⁻ ω, ‖X s.toNNReal ω - Y s.toNNReal ω‖ₑ^2 ∂P).toReal)
      (Icc (0 : ℝ) T) := by
  have hm : Measurable fun p : ℝ × Ω ↦ ‖X p.1.toNNReal p.2 - Y p.1.toNNReal p.2‖ₑ^2 :=
    ((IsProgressive.measurable_toNNReal hX).sub
      (IsProgressive.measurable_toNNReal hY)).eNorm.pow_const 2
  rw [integrableOn_Icc_iff_integrableOn_Ioc]
  apply integrable_toReal_of_lintegral_ne_top hm.lintegral_prod_right'.aemeasurable
  rwa [lintegral_lintegral_swap hm.aemeasurable]

private theorem integral_moment_eq_energy {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X Y : ℝ≥0 → Ω → ℝ} (hX : IsProgressive F X) (hY : IsProgressive F Y)
    (hL : ∀ t, MemLp (fun ω ↦ X t ω - Y t ω) 2 P) (t : ℝ≥0) :
    (∫ s in (0 : ℝ)..t,
      (∫⁻ ω, ‖X s.toNNReal ω - Y s.toNNReal ω‖ₑ^2 ∂P).toReal) =
        (integrandDist P X Y t).toReal := by
  have hm : Measurable fun p : ℝ × Ω ↦ ‖X p.1.toNNReal p.2 - Y p.1.toNNReal p.2‖ₑ^2 :=
    ((IsProgressive.measurable_toNNReal hX).sub
      (IsProgressive.measurable_toNNReal hY)).eNorm.pow_const 2
  rw [intervalIntegral.integral_of_le t.coe_nonneg,
    integral_toReal hm.lintegral_prod_right'.aemeasurable
      (Filter.Eventually.of_forall fun s ↦ (finite_sq_moment (hL s.toNNReal)).lt_top),
    lintegral_lintegral_swap hm.aemeasurable]
  rfl

private theorem sq_three_le (a b c : ℝ) :
    ‖a + b + c‖ₑ^2 ≤ 3 * (‖a‖ₑ^2 + ‖b‖ₑ^2 + ‖c‖ₑ^2) := by
  have h : (a + b + c)^2 ≤ 3 * (a^2 + b^2 + c^2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have he := ENNReal.ofReal_le_ofReal h
  simpa only [Real.eNorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs,
    ENNReal.ofReal_mul (by norm_num : 0 ≤ (3 : ℝ)), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_add (add_nonneg (sq_nonneg a) (sq_nonneg b)) (sq_nonneg c),
    ENNReal.ofReal_add (sq_nonneg a) (sq_nonneg b)] using he

private theorem moment_le_add_energy {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B X Y : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {σ b : ℝ → ℝ} {x y : ℝ} {K : ℝ≥0}
    (hX : IsScalarSDESolution P F B σ b x X)
    (hY : IsScalarSDESolution P F B σ b y Y)
    (hσ : LipschitzWith K σ) (hb : LipschitzWith K b) {t T : ℝ≥0} (ht : t ≤ T) :
    ∫⁻ ω, ‖X t ω - Y t ω‖ₑ^2 ∂P ≤
      3 * ‖x - y‖ₑ^2 + (3 * (K : ℝ≥0∞)^2 * (1 + (T : ℝ≥0∞))) * integrandDist P X Y t := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  let A : Ω → ℝ := fun ω ↦ itoIntegral P F B (fun s ω ↦ σ (X s ω)) t ω -
    itoIntegral P F B (fun s ω ↦ σ (Y s ω)) t ω
  let D : Ω → ℝ := fun ω ↦ (∫ s in (0 : ℝ)..t, b (X s.toNNReal ω)) -
    (∫ s in (0 : ℝ)..t, b (Y s.toNNReal ω))
  have hamem : MemLp A 2 P :=
    (memLp_itoIntegral P F B (fun s ω ↦ σ (X s ω)) t).sub
      (memLp_itoIntegral P F B (fun s ω ↦ σ (Y s ω)) t)
  have ha : AEMeasurable (fun ω ↦ ‖A ω‖ₑ^2) P :=
    hamem.aestronglyMeasurable.aemeasurable.eNorm.pow_const 2
  have hA : ∫⁻ ω, ‖A ω‖ₑ^2 ∂P ≤ (K : ℝ≥0∞)^2 * integrandDist P X Y t :=
    lintegral_itoIntegral_sub_comp_lipschitz_le hB hBF hInd
      hX.isProgressive hY.isProgressive hσ t (hX.2.2.1 t) (hY.2.2.1 t)
  have hD : ∫⁻ ω, ‖D ω‖ₑ^2 ∂P ≤
      (t : ℝ≥0∞) * ((K : ℝ≥0∞)^2 * integrandDist P X Y t) := by
    exact (lintegral_timeIntegral_sub_sq_le P
      (fun ω ↦ hb.continuous.comp (hX.2.1 ω))
      (fun ω ↦ hb.continuous.comp (hY.2.1 ω)) t).trans
        (mul_le_mul' le_rfl (integrandDist_comp_lipschitz_le hb P X Y t))
  calc
    _ ≤ ∫⁻ ω, 3 * (‖x - y‖ₑ^2 + ‖A ω‖ₑ^2 + ‖D ω‖ₑ^2) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hX.2.2.2 t, hY.2.2.2 t] with ω hx hy
      have he : X t ω - Y t ω = (x - y) + A ω + D ω := by dsimp [A, D]; rw [hx, hy]; ring
      rw [he]
      exact sq_three_le _ _ _
    _ = 3 * (‖x - y‖ₑ^2 + (∫⁻ ω, ‖A ω‖ₑ^2 ∂P) + (∫⁻ ω, ‖D ω‖ₑ^2 ∂P)) := by
      rw [lintegral_const_mul' _ _ (by norm_num : (3 : ℝ≥0∞) ≠ ∞)]
      rw [lintegral_add_left'
        (show AEMeasurable (fun ω ↦ ‖x - y‖ₑ^2 + ‖A ω‖ₑ^2) P from aemeasurable_const.add ha),
        lintegral_add_left' (f := fun _ : Ω ↦ ‖x - y‖ₑ^2) aemeasurable_const]
      simp
    _ ≤ 3 * (‖x - y‖ₑ^2 + (K : ℝ≥0∞)^2 * integrandDist P X Y t +
        (t : ℝ≥0∞) * ((K : ℝ≥0∞)^2 * integrandDist P X Y t)) :=
      mul_le_mul' le_rfl (add_le_add (add_le_add le_rfl hA) hD)
    _ ≤ 3 * (‖x - y‖ₑ^2 + (K : ℝ≥0∞)^2 * integrandDist P X Y t +
        (T : ℝ≥0∞) * ((K : ℝ≥0∞)^2 * integrandDist P X Y t)) := by
      have htE : (t : ℝ≥0∞) ≤ T := by exact_mod_cast ht
      exact mul_le_mul' le_rfl (add_le_add le_rfl (mul_le_mul' htE le_rfl))
    _ = _ := by ring

/-- Quantitative same-noise stability of scalar globally Lipschitz SDE solutions,
in lower-integral form. On `t ≤ T`, the squared distance is at most
`3 * (x-y)² * exp (3*K²*(1+T)*t)`. No filtration completeness is assumed. -/
theorem IsScalarSDESolution.lintegral_sub_sq_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B X Y : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {σ b : ℝ → ℝ} {x y : ℝ} {K : ℝ≥0}
    (hX : IsScalarSDESolution P F B σ b x X)
    (hY : IsScalarSDESolution P F B σ b y Y)
    (hσ : LipschitzWith K σ) (hb : LipschitzWith K b) {t T : ℝ≥0} (ht : t ≤ T) :
    ∫⁻ ω, ‖X t ω - Y t ω‖ₑ^2 ∂P ≤
      ENNReal.ofReal (3 * (x - y)^2 * Real.exp (3 * (K : ℝ)^2 * (1 + T) * (t : ℝ))) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  let u : ℝ → ℝ := fun s ↦ (∫⁻ ω, ‖X s.toNNReal ω - Y s.toNNReal ω‖ₑ^2 ∂P).toReal
  have hL (s : ℝ≥0) : MemLp (fun ω ↦ X s ω - Y s ω) 2 P :=
    (hX.memLp hb s).sub (hY.memLp hb s)
  have hE (s : ℝ≥0) : integrandDist P X Y s ≠ ∞ :=
    finite_difference_energy hX.isProgressive hY.isProgressive s (hX.2.2.1 s) (hY.2.2.1 s)
  have huInt : IntegrableOn u (Icc (0 : ℝ) T) :=
    moment_integrable hX.isProgressive hY.isProgressive T (hE T)
  have hcomp : ∀ s ∈ Icc (0 : ℝ) T,
      u s ≤ 3 * (x - y)^2 + (3 * (K : ℝ)^2 * (1 + T)) * ∫ v in (0 : ℝ)..s, u v := by
    intro s hs
    have htE : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hs.2
    have hbnd := moment_le_add_energy hB hBF hInd hX hY hσ hb htE
    have hf1 : (3 : ℝ≥0∞) * ‖x - y‖ₑ^2 ≠ ∞ := by finiteness
    have hf2 : (3 * (K : ℝ≥0∞)^2 * (1 + (T : ℝ≥0∞))) * integrandDist P X Y s.toNNReal ≠ ∞ :=
      ENNReal.mul_ne_top (by finiteness) (hE s.toNNReal)
    have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf1, hf2⟩) hbnd
    rw [ENNReal.toReal_add hf1 hf2] at hreal
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
      ENNReal.coe_toReal, Real.eNorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _),
      sq_abs, ENNReal.toReal_add (by simp : (1 : ℝ≥0∞) ≠ ∞)
        (by simp : (T : ℝ≥0∞) ≠ ∞), ENNReal.toReal_one] at hreal
    rw [← integral_moment_eq_energy hX.isProgressive hY.isProgressive hL s.toNNReal] at hreal
    simpa only [u, Real.coe_toNNReal s hs.1, Real.eNorm_eq_ofReal_abs] using hreal
  have hgr := MathlibExt.Analysis.ODE.le_mul_exp_of_le_add_integral
    (by positivity : 0 ≤ 3 * (K : ℝ)^2 * (1 + (T : ℝ))) huInt
    (fun _ _ ↦ ENNReal.toReal_nonneg) hcomp (t : ℝ) ⟨t.coe_nonneg, by exact_mod_cast ht⟩
  have he := ENNReal.ofReal_le_ofReal hgr
  simpa only [u, Real.toNNReal_coe, ENNReal.ofReal_toReal (finite_sq_moment (hL t))] using he

/-- The mean-square same-noise stability estimate as an actual real expectation.
Its integrability follows from the solution equations, rather than being an
additional premise. The constant is deliberately nonoptimal. -/
theorem IsScalarSDESolution.integral_sub_sq_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B X Y : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {σ b : ℝ → ℝ} {x y : ℝ} {K : ℝ≥0}
    (hX : IsScalarSDESolution P F B σ b x X)
    (hY : IsScalarSDESolution P F B σ b y Y)
    (hσ : LipschitzWith K σ) (hb : LipschitzWith K b) {t T : ℝ≥0} (ht : t ≤ T) :
    ∫ ω, (X t ω - Y t ω)^2 ∂P ≤ 3 * (x - y)^2 * Real.exp (3 * (K : ℝ)^2 * (1 + T) * (t : ℝ)) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have h := IsScalarSDESolution.lintegral_sub_sq_le hB hBF hInd hX hY hσ hb ht
  have hf := ((hX.memLp hb t).sub (hY.memLp hb t)).integrable_sq
  have he : ENNReal.ofReal (∫ ω, (X t ω - Y t ω)^2 ∂P) = ∫⁻ ω, ‖X t ω - Y t ω‖ₑ^2 ∂P := by
    simpa only [Pi.sub_apply, Real.eNorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      using ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
  rw [← he] at h
  have hreal := ENNReal.toReal_mono (by simp) h
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ sq_nonneg _),
    ENNReal.toReal_ofReal (by positivity :
      0 ≤ 3 * (x - y)^2 * Real.exp (3 * (K : ℝ)^2 * (1 + T) * (t : ℝ)))]
    using hreal

/-- Pathwise uniqueness for scalar globally Lipschitz SDE solutions driven by the
same process and filtration with the same deterministic initial value. Equality
holds at every nonnegative time outside one common null set. No completeness
or right continuity of the filtration is needed. -/
theorem IsScalarSDESolution.indistinguishable
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B X Y : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {σ b : ℝ → ℝ} {x : ℝ} {K : ℝ≥0}
    (hX : IsScalarSDESolution P F B σ b x X)
    (hY : IsScalarSDESolution P F B σ b x Y)
    (hσ : LipschitzWith K σ) (hb : LipschitzWith K b) : X ≡ᵐ[P] Y := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  apply indistinguishable_of_ae_eq_of_continuous
    (Filter.Eventually.of_forall hX.2.1) (Filter.Eventually.of_forall hY.2.1)
  intro t
  have h := IsScalarSDESolution.lintegral_sub_sq_le hB hBF hInd hX hY hσ hb (t := t) le_rfl
  have hz : ∫⁻ ω, ‖X t ω - Y t ω‖ₑ^2 ∂P = 0 := by simpa using h
  have hm := ((hX.memLp hb t).sub (hY.memLp hb t)).aestronglyMeasurable.aemeasurable
  have ha := (lintegral_eq_zero_iff' (hm.eNorm.pow_const 2)).1 hz
  filter_upwards [ha] with ω hω
  simpa only [Pi.zero_apply, sq_eq_zero_iff, eNorm_eq_zero, Pi.sub_apply, sub_eq_zero] using hω

end ProbabilityTheory
