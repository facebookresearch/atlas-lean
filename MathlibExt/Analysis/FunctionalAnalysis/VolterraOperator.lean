/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The Volterra operator and its spectrum

The Volterra operator `V` on `C([0, 1], ℝ)` (realized as bounded continuous
functions on `[0, 1]`) is the indefinite-integration operator
`(Vf)(x) = ∫₀ˣ f(t) dt`. It is the prototype of a compact quasinilpotent
operator: its powers satisfy the factorial bound `‖Vⁿ‖ ≤ 1 / n!`, so for every
`z ≠ 0` the function-level Neumann series `∑ₙ (z⁻¹)^(n+1) • Vⁿ g` converges and
inverts `z - V`: the operator is bijective, hence a unit. Hence the spectrum
of `V` is exactly `{0}`.

This is a companion to the Green's-operator / Sturm--Liouville material in
the v1 book `IntroductionToFunctionalAnalysis` (the Volterra operator is the
integral operator with kernel `1_{t ≤ x}`; it is not one of the 72 v1
targets, and neither it nor its spectrum is in Mathlib or MathlibExt).

Source: V. Volterra, *Sopra alcune questioni di inversione degli integrali
definiti*, Annali di Matematica Pura ed Applicata 25 (1897), 139--178;
see also F. Riesz and B. Sz.-Nagy, *Functional Analysis*, §88.
-/

namespace MathlibExt.Analysis.FunctionalAnalysis.VolterraOperator

open intervalIntegral
open scoped BoundedContinuousFunction Topology

noncomputable section

/-- The domain of the Volterra operator: bounded continuous real functions on `[0, 1]`. -/
abbrev VolterraSpace := Set.Icc (0 : ℝ) 1 →ᵇ ℝ

/-- Clamp a real number into `[0, 1]`. -/
def clamp01 (t : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨max 0 (min t 1), le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

/-- Extend a function on `[0, 1]` to `ℝ` by clamping the argument; this is the
continuous extension used to write `(Vf)(x)` as an interval integral over `ℝ`. -/
def volterraExtend (f : VolterraSpace) : ℝ → ℝ :=
  fun t => f (clamp01 t)

/-- The clamped extension is continuous. -/
theorem volterraExtend_continuous (f : VolterraSpace) :
    Continuous (volterraExtend f) :=
  f.continuous.comp
    ((continuous_const.max (continuous_id.min continuous_const)).subtype_mk
      (fun _ => ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩))

/-- On `[0, 1]` the clamped extension agrees with the original function. -/
theorem volterraExtend_apply_of_mem {f : VolterraSpace} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    volterraExtend f t = f ⟨t, ht⟩ := by
  have hclamp : max 0 (min t 1) = t := by
    rw [min_eq_left ht.2, max_eq_right ht.1]
  simp [volterraExtend, clamp01, hclamp]

/-- The clamped extension is bounded by the sup norm of the original function. -/
theorem norm_volterraExtend_le (f : VolterraSpace) (t : ℝ) :
    ‖volterraExtend f t‖ ≤ ‖f‖ :=
  f.norm_coe_le_norm _

/-- The primitive of the clamped extension is continuous in the upper endpoint. -/
theorem volterraPrimitive_continuous (f : VolterraSpace) :
    Continuous (fun x : Set.Icc (0 : ℝ) 1 => ∫ t in (0 : ℝ)..(x : ℝ), volterraExtend f t) :=
  (intervalIntegral.continuous_primitive
    (fun a b => (volterraExtend_continuous f).intervalIntegrable a b)
    (0 : ℝ)).comp continuous_subtype_val

/-- The primitive of the clamped extension is bounded by the sup norm. -/
theorem volterraPrimitive_norm_le (f : VolterraSpace) (x : Set.Icc (0 : ℝ) 1) :
    ‖∫ t in (0 : ℝ)..(x : ℝ), volterraExtend f t‖ ≤ ‖f‖ := by
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := x.2.1
  have hx1 : (x : ℝ) ≤ 1 := x.2.2
  calc ‖∫ t in (0 : ℝ)..(x : ℝ), volterraExtend f t‖
      ≤ ∫ t in (0 : ℝ)..(x : ℝ), ‖volterraExtend f t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hx0
    _ ≤ ∫ _t in (0 : ℝ)..(x : ℝ), ‖f‖ := by
        apply intervalIntegral.integral_mono_on hx0
        · exact (volterraExtend_continuous f).norm.intervalIntegrable _ _
        · exact continuous_const.intervalIntegrable _ _
        · intro t _
          exact norm_volterraExtend_le f t
    _ = (x : ℝ) * ‖f‖ := by
        rw [intervalIntegral.integral_const]
        simp [sub_eq_add_neg, smul_eq_mul]
    _ ≤ ‖f‖ := by
        have : (x : ℝ) * ‖f‖ ≤ 1 * ‖f‖ :=
          mul_le_mul_of_nonneg_right hx1 (norm_nonneg _)
        simpa using this

/-- The Volterra operator as a linear map. -/
noncomputable def volterraLinearMap : VolterraSpace →ₗ[ℝ] VolterraSpace where
  toFun f :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x => ∫ t in (0 : ℝ)..(x : ℝ), volterraExtend f t)
      (volterraPrimitive_continuous f) ‖f‖ (volterraPrimitive_norm_le f)
  map_add' f g := by
    apply BoundedContinuousFunction.ext
    intro x
    have hfun : (fun t => volterraExtend (f + g) t)
        = fun t => volterraExtend f t + volterraExtend g t := by
      funext t
      simp [volterraExtend]
    simp only [BoundedContinuousFunction.coe_ofNormedAddCommGroup, hfun,
      BoundedContinuousFunction.add_apply]
    rw [intervalIntegral.integral_add
      ((volterraExtend_continuous f).intervalIntegrable _ _)
      ((volterraExtend_continuous g).intervalIntegrable _ _)]
  map_smul' c f := by
    apply BoundedContinuousFunction.ext
    intro x
    have hfun : (fun t => volterraExtend (c • f) t)
        = fun t => c • volterraExtend f t := by
      funext t
      simp [volterraExtend]
    simp only [BoundedContinuousFunction.coe_ofNormedAddCommGroup, hfun,
      BoundedContinuousFunction.smul_apply]
    rw [intervalIntegral.integral_smul]
    rfl

/-- The Volterra operator is bounded by `1` on the unit ball. -/
theorem volterraLinearMap_norm_le (f : VolterraSpace) :
    ‖volterraLinearMap f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul]
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
    (volterraPrimitive_continuous f) (norm_nonneg f) (volterraPrimitive_norm_le f)

/-- The Volterra operator `(Vf)(x) = ∫₀ˣ f(t) dt` as a bounded operator on `C([0, 1], ℝ)`. -/
noncomputable def volterraOperator : VolterraSpace →L[ℝ] VolterraSpace :=
  volterraLinearMap.mkContinuous 1 volterraLinearMap_norm_le

/-- Evaluation formula for the Volterra operator. -/
theorem volterraOperator_apply (f : VolterraSpace) (x : Set.Icc (0 : ℝ) 1) :
    (volterraOperator f) x = ∫ t in (0 : ℝ)..(x : ℝ), volterraExtend f t :=
  rfl

/-- The Volterra operator vanishes at `0`. -/
theorem volterraOperator_apply_zero (f : VolterraSpace) :
    (volterraOperator f) ⟨0, le_refl 0, zero_le_one⟩ = 0 := by
  rw [volterraOperator_apply]
  simp

/-- Operator-norm bound for the Volterra operator. -/
theorem norm_volterraOperator_le_one : ‖volterraOperator‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one volterraLinearMap_norm_le

/-- The integral of `t ^ n` over `[0, x]`. -/
private theorem integral_pow_Icc_zero (n : ℕ) (x : ℝ) :
    ∫ t in (0 : ℝ)..x, t ^ n = x ^ (n + 1) / (n + 1) := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) x,
      HasDerivAt (fun t => (1 / (n + 1 : ℝ)) * t ^ (n + 1)) (t ^ n) t := by
    intro t _
    have h := (hasDerivAt_pow (n + 1) t).const_mul (1 / (n + 1 : ℝ))
    rw [Nat.add_sub_cancel] at h
    have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hder : (1 / ((n : ℝ) + 1)) * ((((n + 1 : ℕ) : ℝ)) * t ^ n) = t ^ n := by
      rw [Nat.cast_add, Nat.cast_one]
      field_simp
    rw [hder] at h
    exact h
  have hint : IntervalIntegrable (fun t => t ^ n) MeasureTheory.volume (0 : ℝ) x :=
    (continuous_pow n).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  simp only [zero_pow (Nat.succ_ne_zero n), mul_zero, sub_zero]
  rw [one_div, inv_mul_eq_div]

/-- Pointwise factorial bound for the powers of the Volterra operator. -/
theorem pow_volterraOperator_apply_norm_le (n : ℕ) (f : VolterraSpace)
    (x : Set.Icc (0 : ℝ) 1) :
    ‖((volterraOperator ^ n) f) x‖ ≤ ((x : ℝ) ^ n / (Nat.factorial n)) * ‖f‖ := by
  induction n generalizing x with
  | zero =>
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, one_mul]
    exact f.norm_coe_le_norm x
  | succ n ih =>
    have hx0 : (0 : ℝ) ≤ (x : ℝ) := x.2.1
    have hV : (volterraOperator ^ (n + 1)) f = volterraOperator ((volterraOperator ^ n) f) := by
      rw [pow_succ']; rfl
    rw [hV, volterraOperator_apply]
    calc ‖∫ t in (0 : ℝ)..(x : ℝ), volterraExtend ((volterraOperator ^ n) f) t‖
        ≤ ∫ t in (0 : ℝ)..(x : ℝ), ‖volterraExtend ((volterraOperator ^ n) f) t‖ :=
          intervalIntegral.norm_integral_le_integral_norm hx0
      _ ≤ ∫ t in (0 : ℝ)..(x : ℝ), ((t ^ n / (Nat.factorial n)) * ‖f‖) := by
          apply intervalIntegral.integral_mono_on hx0
          · exact (volterraExtend_continuous _).norm.intervalIntegrable _ _
          · exact ((continuous_pow n).div_const _ |>.mul_const _).intervalIntegrable _ _
          · intro t ht
            have htIcc : t ∈ Set.Icc (0 : ℝ) 1 :=
              ⟨ht.1, le_trans ht.2 x.2.2⟩
            rw [volterraExtend_apply_of_mem htIcc]
            exact ih ⟨t, htIcc⟩
      _ = ((x : ℝ) ^ (n + 1) / (Nat.factorial (n + 1))) * ‖f‖ := by
          have hcast : ((Nat.factorial (n + 1) : ℕ) : ℝ)
              = (n + 1 : ℝ) * (Nat.factorial n : ℝ) := by
            rw [Nat.factorial_succ]
            push_cast
            ring
          rw [show (fun t : ℝ => (t ^ n / (Nat.factorial n)) * ‖f‖)
              = fun t => (‖f‖ / (Nat.factorial n)) * t ^ n by
            funext t; ring]
          rw [intervalIntegral.integral_const_mul, integral_pow_Icc_zero n (x : ℝ), hcast]
          field_simp

/-- Factorial bound for the operator norm of the powers of the Volterra operator. -/
theorem norm_volterraOperator_pow_le (n : ℕ) : ‖volterraOperator ^ n‖ ≤ 1 / (Nat.factorial n) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  calc ‖((volterraOperator ^ n) f) x‖
      ≤ ((x : ℝ) ^ n / (Nat.factorial n)) * ‖f‖ := pow_volterraOperator_apply_norm_le n f x
    _ ≤ (1 / (Nat.factorial n)) * ‖f‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact pow_le_one₀ x.2.1 x.2.2

/-- Telescoping series in `VolterraSpace`: if `c n → 0`, then
`∑' (c n - c (n+1)) = c 0`. -/
private theorem tsum_sub_succ_eq {c : ℕ → VolterraSpace} (hc : Summable c)
    (hc0 : Filter.Tendsto c Filter.atTop (𝓝 0)) :
    ∑' n, (c n - c (n + 1)) = c 0 := by
  have hdiff : Summable (fun n => c n - c (n + 1)) := by
    refine Summable.sub hc ?_
    exact (summable_nat_add_iff 1).mpr hc
  have hlim : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, (c n - c (n + 1)))
      Filter.atTop (𝓝 (c 0)) := by
    have heq : (fun N => ∑ n ∈ Finset.range N, (c n - c (n + 1)))
        = fun N => c 0 - c N := by
      funext N
      rw [show (fun n => c n - c (n + 1)) = fun n => -(c (n + 1) - c n) by
        funext n; rw [neg_sub]]
      rw [Finset.sum_neg_distrib, Finset.sum_range_sub, neg_sub]
    rw [heq]
    simpa using Filter.Tendsto.sub tendsto_const_nhds hc0
  exact ((hdiff.hasSum_iff_tendsto_nat).mpr hlim).tsum_eq

/-- Pointwise norm bound for the Neumann-series terms. -/
private theorem norm_neumann_term_le (n : ℕ) (z : ℝ) (g : VolterraSpace) :
    ‖(z⁻¹ : ℝ) ^ n • (volterraOperator ^ n) g‖
      ≤ (|z|⁻¹) ^ n / (Nat.factorial n : ℝ) * ‖g‖ := by
  calc ‖(z⁻¹ : ℝ) ^ n • (volterraOperator ^ n) g‖
      = (|z|⁻¹) ^ n * ‖(volterraOperator ^ n) g‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_inv]
    _ ≤ (|z|⁻¹) ^ n * (‖volterraOperator ^ n‖ * ‖g‖) := by
        apply mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.le_opNorm _ _) (by positivity)
    _ ≤ (|z|⁻¹) ^ n * ((1 / (Nat.factorial n : ℝ)) * ‖g‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (norm_volterraOperator_pow_le n) (norm_nonneg g))
          (by positivity)
    _ = (|z|⁻¹) ^ n / (Nat.factorial n : ℝ) * ‖g‖ := by ring

/-- The Neumann-series terms are summable. -/
private theorem summable_neumann_terms (z : ℝ) (g : VolterraSpace) :
    Summable (fun n => (z⁻¹ : ℝ) ^ n • (volterraOperator ^ n) g) :=
  Summable.of_norm_bounded (E := VolterraSpace)
    (f := fun n => (z⁻¹ : ℝ) ^ n • (volterraOperator ^ n) g)
    (g := fun n => (|z|⁻¹) ^ n / (Nat.factorial n : ℝ) * ‖g‖)
    ((Real.summable_pow_div_factorial |z|⁻¹).mul_right ‖g‖)
    (fun n => norm_neumann_term_le n z g)

/-- The Neumann-series terms tend to `0`. -/
private theorem tendsto_neumann_terms (z : ℝ) (g : VolterraSpace) :
    Filter.Tendsto (fun n => (z⁻¹ : ℝ) ^ n • (volterraOperator ^ n) g)
      Filter.atTop (𝓝 0) :=
  squeeze_zero_norm (f := fun n => (z⁻¹ : ℝ) ^ n • (volterraOperator ^ n) g)
    (fun n => norm_neumann_term_le n z g)
    (by simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop |z|⁻¹).mul_const ‖g‖)

/-- The Neumann series on functions: the candidate inverse of `algebraMap z - V`. -/
private noncomputable def volterraNeumann (z : ℝ) (g : VolterraSpace) : VolterraSpace :=
  ∑' n, (z⁻¹ : ℝ) ^ (n + 1) • (volterraOperator ^ n) g

/-- Pointwise norm bound for the shifted Neumann-series terms. -/
private theorem norm_neumann_term_succ_le (n : ℕ) (z : ℝ) (g : VolterraSpace) :
    ‖(z⁻¹ : ℝ) ^ (n + 1) • (volterraOperator ^ n) g‖
      ≤ (|z|⁻¹) ^ (n + 1) / (Nat.factorial n : ℝ) * ‖g‖ := by
  calc ‖(z⁻¹ : ℝ) ^ (n + 1) • (volterraOperator ^ n) g‖
      = (|z|⁻¹) ^ (n + 1) * ‖(volterraOperator ^ n) g‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_inv]
    _ ≤ (|z|⁻¹) ^ (n + 1) * (‖volterraOperator ^ n‖ * ‖g‖) := by
        apply mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.le_opNorm _ _) (by positivity)
    _ ≤ (|z|⁻¹) ^ (n + 1) * ((1 / (Nat.factorial n : ℝ)) * ‖g‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (norm_volterraOperator_pow_le n) (norm_nonneg g))
          (by positivity)
    _ = (|z|⁻¹) ^ (n + 1) / (Nat.factorial n : ℝ) * ‖g‖ := by ring

/-- The Neumann series is summable. -/
private theorem summable_volterraNeumann (z : ℝ) (g : VolterraSpace) :
    Summable (fun n => (z⁻¹ : ℝ) ^ (n + 1) • (volterraOperator ^ n) g) := by
  refine Summable.of_norm_bounded (E := VolterraSpace)
    (f := fun n => (z⁻¹ : ℝ) ^ (n + 1) • (volterraOperator ^ n) g)
    (g := fun n => (|z|⁻¹) ^ (n + 1) / (Nat.factorial n : ℝ) * ‖g‖) ?_ ?_
  · have h0 := (Real.summable_pow_div_factorial |z|⁻¹).mul_right (|z|⁻¹ * ‖g‖)
    refine h0.congr (fun n => ?_)
    rw [pow_succ]
    ring
  · exact fun n => norm_neumann_term_succ_le n z g

/-- Applying `V` shifts the Neumann series: `V ((V^n) g) = (V^(n+1)) g`. -/
private theorem volterraOperator_apply_pow_succ (n : ℕ) (g : VolterraSpace) :
    volterraOperator ((volterraOperator ^ n) g) = (volterraOperator ^ (n + 1)) g := by
  rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]

/-- Applying `V^n` after `V`: `(V^n) (V g) = (V^(n+1)) g`. -/
private theorem volterraOperator_pow_apply_succ (n : ℕ) (g : VolterraSpace) :
    (volterraOperator ^ n) (volterraOperator g) = (volterraOperator ^ (n + 1)) g := by
  rw [pow_succ, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]

/-- The operator `algebraMap z - V` applied to a Neumann term telescopes. -/
private theorem sub_apply_neumann_term {z : ℝ} (hz : z ≠ 0) (n : ℕ) (g : VolterraSpace) :
    (algebraMap ℝ (VolterraSpace →L[ℝ] VolterraSpace) z - volterraOperator)
        ((z⁻¹ : ℝ) ^ (n + 1) • (volterraOperator ^ n) g)
      = (z⁻¹ : ℝ) ^ n • (volterraOperator ^ n) g
        - (z⁻¹ : ℝ) ^ (n + 1) • (volterraOperator ^ (n + 1)) g := by
  have hzpow : z * (z⁻¹ : ℝ) ^ (n + 1) = (z⁻¹ : ℝ) ^ n := by
    rw [pow_succ', ← mul_assoc, mul_inv_cancel₀ hz, one_mul]
  rw [sub_apply, ContinuousLinearMap.algebraMap_apply, map_smul,
    volterraOperator_apply_pow_succ, smul_smul, hzpow]

/-- One side of the inverse: `(algebraMap z - V) (Sg g) = g`. -/
private theorem volterraOperator_apply_neumann {z : ℝ} (hz : z ≠ 0) (g : VolterraSpace) :
    (algebraMap ℝ (VolterraSpace →L[ℝ] VolterraSpace) z - volterraOperator)
      (volterraNeumann z g) = g := by
  rw [volterraNeumann,
    ContinuousLinearMap.map_tsum _ (summable_volterraNeumann z g)]
  rw [tsum_congr (fun n => sub_apply_neumann_term hz n g)]
  simpa using
    tsum_sub_succ_eq (summable_neumann_terms z g) (tendsto_neumann_terms z g)

/-- The Neumann term of `(algebraMap z - V) g` telescopes. -/
private theorem neumann_term_sub_apply {z : ℝ} (hz : z ≠ 0) (n : ℕ) (g : VolterraSpace) :
    (z⁻¹ : ℝ) ^ (n + 1) • (volterraOperator ^ n)
        ((algebraMap ℝ (VolterraSpace →L[ℝ] VolterraSpace) z - volterraOperator) g)
      = (z⁻¹ : ℝ) ^ n • (volterraOperator ^ n) g
        - (z⁻¹ : ℝ) ^ (n + 1) • (volterraOperator ^ (n + 1)) g := by
  have hzpow : (z⁻¹ : ℝ) ^ (n + 1) * z = (z⁻¹ : ℝ) ^ n := by
    rw [pow_succ, mul_assoc, inv_mul_cancel₀ hz, mul_one]
  have hVn : (volterraOperator ^ n)
      ((algebraMap ℝ (VolterraSpace →L[ℝ] VolterraSpace) z - volterraOperator) g)
      = z • (volterraOperator ^ n) g - (volterraOperator ^ (n + 1)) g := by
    rw [sub_apply, ContinuousLinearMap.algebraMap_apply, map_sub, map_smul,
      volterraOperator_pow_apply_succ]
  rw [hVn, smul_sub, smul_smul, hzpow]

/-- The other side of the inverse: `Sg ((algebraMap z - V) g) = g`. -/
private theorem volterraNeumann_apply {z : ℝ} (hz : z ≠ 0) (g : VolterraSpace) :
    volterraNeumann z
      ((algebraMap ℝ (VolterraSpace →L[ℝ] VolterraSpace) z - volterraOperator) g)
      = g := by
  rw [volterraNeumann, tsum_congr (fun n => neumann_term_sub_apply hz n g)]
  simpa using
    tsum_sub_succ_eq (summable_neumann_terms z g) (tendsto_neumann_terms z g)

/-- Every nonzero real is in the resolvent set of the Volterra operator:
`algebraMap z - V` is a unit because it is bijective, with inverse given by
the function-level Neumann series. -/
theorem volterraOperator_mem_resolventSet_of_ne_zero {z : ℝ} (hz : z ≠ 0) :
    z ∈ resolventSet ℝ volterraOperator := by
  rw [spectrum.mem_resolventSet_iff, ContinuousLinearMap.isUnit_iff_bijective]
  refine ⟨fun u v huv => ?_, fun g => ⟨volterraNeumann z g,
    volterraOperator_apply_neumann hz g⟩⟩
  have h1 := volterraNeumann_apply hz u
  have h2 := volterraNeumann_apply hz v
  rw [huv] at h1
  exact h1.symm.trans h2

/-- The Volterra operator is not a unit: every `Vf` vanishes at `0`. -/
theorem not_isUnit_volterraOperator : ¬ IsUnit volterraOperator := by
  intro h
  have hbij := ContinuousLinearMap.isUnit_iff_bijective.mp h
  obtain ⟨f, hf⟩ := hbij.2 (BoundedContinuousFunction.const (Set.Icc (0 : ℝ) 1) (1 : ℝ))
  have h0 := congrArg (fun g : VolterraSpace => g ⟨0, le_refl 0, zero_le_one⟩) hf
  rw [volterraOperator_apply_zero] at h0
  simp at h0

/-- **The spectrum of the Volterra operator is `{0}`.** -/
theorem volterraOperator_spectrum : spectrum ℝ volterraOperator = {0} := by
  ext z
  simp only [Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hne
    exact absurd (spectrum.mem_resolventSet_iff.mp
      (volterraOperator_mem_resolventSet_of_ne_zero hne)) (spectrum.mem_iff.mp h)
  · intro h
    rw [h, spectrum.zero_mem_iff]
    exact not_isUnit_volterraOperator

/-- The spectral radius of the Volterra operator is `0`: it is quasinilpotent. -/
theorem spectralRadius_volterraOperator : spectralRadius ℝ volterraOperator = 0 := by
  rw [spectralRadius_eq_of_unital (𝕜 := ℝ) volterraOperator, volterraOperator_spectrum]
  simp

end

end MathlibExt.Analysis.FunctionalAnalysis.VolterraOperator
