/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp

/-!
# The latent causal variable model: mixed fourth moments and the genetic causality proportion

O'Connor and Price (2018) model the joint distribution of the marginal effect sizes
`(α₁, α₂)` of a random SNP on two traits as (their Equation 3)

  `(α₁, α₂) = (q₁ π, q₂ π) + (γ₁, γ₂)`,  `π ⊥ (γ₁, γ₂)`,
  `(γ₁, γ₂) ~ (-γ₁, γ₂) ~ (γ₁, -γ₂)`,

where `π` is the effect of the SNP on a latent causal variable `L`, `q₁, q₂` are the normalized
effects of `L` on the two traits, and `α₁, α₂, π` have unit variance and mean zero. The genetic
correlation is `ρ_g = E(α₁ α₂) = q₁ q₂`, and their Equation 2 is the mixed-fourth-moment identity

  `E(α₁³ α₂) = κ_π q₁³ q₂ + 3 ρ_g`,  `κ_π = E(π⁴) - 3` (excess kurtosis of `π`).

The genetic causality proportion (their Equation 4) is
`gcp = (log|q₂| - log|q₁|) / (log|q₂| + log|q₁|)`, which solves `q₂² / q₁² = (ρ_g²)^gcp`
(their Equation 1).

The paper states (after Equation 2) that `|E(α₁³ α₂)| ≥ |E(α₁ α₂³)|` implies `q₁² ≥ q₂²` and
`gcp ≥ 0`. Because of the `3 ρ_g` term this comparison of uncentred moments is correct only when
`κ_π > 0` (`abs_moment_le_iff_of_kurtosis_pos`); for `κ_π < 0` it is reversed
(`abs_moment_le_iff_of_kurtosis_neg`). The comparison of the centred moments
`E(α₁³ α₂) - 3 ρ_g` and `E(α₁ α₂³) - 3 ρ_g`, which is what the paper's estimator uses (Methods,
the quantities `κ_k = E(α_k² α₁ α₂) - 3 ρ_g`), orders `q₁²` and `q₂²` whenever `κ_π ρ_g ≠ 0` (both `κ_π ≠ 0` and `ρ_g = q₁ q₂ ≠ 0` are needed)
(`abs_centredMoment_le_iff`).

## Main results

* `Model`: the LCV model.
* `Model.integral_alpha1_mul_alpha2`: `E(α₁ α₂) = q₁ q₂`.
* `Model.integral_alpha1_pow_three_mul_alpha2`, `Model.integral_alpha1_mul_alpha2_pow_three`:
  the mixed fourth moments (Equation 2 and its mirror image).
* `Model.q1_sq_le_one`, `Model.q2_sq_le_one`, `Model.one_le_integral_pi_pow_four`,
  `Model.neg_two_le_kurtosis`.
* `Model.centred_moment_left`, `Model.centred_moment_right`, `Model.abs_centredMoment_le_iff`:
  the centred moments are `κ_π q₁³ q₂` and `κ_π q₁ q₂³`, and order `q₁²`, `q₂²` when
  `κ_π ρ_g ≠ 0`.
* `Model.abs_moment_le_iff_of_kurtosis_pos`, `Model.abs_moment_le_iff_of_kurtosis_neg`: the
  paper's uncentred comparison holds for `κ_π > 0` and is reversed for `κ_π < 0`.
* `gcp`, `gcp_nonneg_iff`, `rpow_gcp`, `gcp_le_one`, `neg_one_le_gcp`,
  `Model.gcp_nonneg_of_abs_moment_le`.

The centred form of the comparison is derived here; the paper states the uncentred implication
without the sign condition on `κ_π`.

## References

* L. J. O'Connor, A. L. Price, *Distinguishing genetic correlation from causation across 52
  diseases and complex traits*, Nat. Genet. 50 (2018), 1728–1734.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Biology.StatisticalGenetics.LatentCausalVariable

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The latent causal variable model of O'Connor and Price (2018, Equation 3) on a probability
space: `α_k = q_k π + γ_k` with `π` independent of `(γ₁, γ₂)`, the law of `(γ₁, γ₂)` invariant
under each sign flip, `π` of mean zero and unit variance, and both `α_k` of unit second moment.
Fourth moments are assumed finite. -/
structure Model (P : Measure Ω) where
  /-- The normalized effect of the latent variable on trait 1. -/
  q1 : ℝ
  /-- The normalized effect of the latent variable on trait 2. -/
  q2 : ℝ
  /-- The effect of a SNP on the latent causal variable. -/
  pi : Ω → ℝ
  /-- The non-mediated effect of a SNP on trait 1. -/
  g1 : Ω → ℝ
  /-- The non-mediated effect of a SNP on trait 2. -/
  g2 : Ω → ℝ
  memLp_pi : MemLp pi 4 P
  memLp_g1 : MemLp g1 4 P
  memLp_g2 : MemLp g2 4 P
  /-- `π` is independent of `(γ₁, γ₂)`. -/
  indep : IndepFun pi (fun ω => (g1 ω, g2 ω)) P
  /-- `(γ₁, γ₂) ~ (-γ₁, γ₂)`. -/
  symm_left : IdentDistrib (fun ω => (g1 ω, g2 ω)) (fun ω => (-g1 ω, g2 ω)) P P
  /-- `(γ₁, γ₂) ~ (γ₁, -γ₂)`. -/
  symm_right : IdentDistrib (fun ω => (g1 ω, g2 ω)) (fun ω => (g1 ω, -g2 ω)) P P
  integral_pi : ∫ ω, pi ω ∂P = 0
  integral_pi_sq : ∫ ω, pi ω ^ 2 ∂P = 1
  integral_alpha1_sq : ∫ ω, (q1 * pi ω + g1 ω) ^ 2 ∂P = 1
  integral_alpha2_sq : ∫ ω, (q2 * pi ω + g2 ω) ^ 2 ∂P = 1

namespace Model

variable {P : Measure Ω} [IsProbabilityMeasure P] (D : Model P)

/-- The marginal effect `α₁ = q₁ π + γ₁` on trait 1. -/
def alpha1 (ω : Ω) : ℝ := D.q1 * D.pi ω + D.g1 ω

/-- The marginal effect `α₂ = q₂ π + γ₂` on trait 2. -/
def alpha2 (ω : Ω) : ℝ := D.q2 * D.pi ω + D.g2 ω

/-- The excess kurtosis `κ_π = E(π⁴) - 3` of the effect on the latent variable. -/
noncomputable def kurtosis : ℝ := ∫ ω, D.pi ω ^ 4 ∂P - 3

private theorem integral_odd_left
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (D : Model P)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hodd : ∀ x : ℝ × ℝ, f (-x.1, x.2) = -f x) :
    ∫ ω, f (D.g1 ω, D.g2 ω) ∂P = 0 := by
  have h := (D.symm_left.comp hf).integral_eq
  change (∫ ω, f (D.g1 ω, D.g2 ω) ∂P) =
    ∫ ω, f (-D.g1 ω, D.g2 ω) ∂P at h
  have he : (fun ω => f (-D.g1 ω, D.g2 ω)) =
      fun ω => -f (D.g1 ω, D.g2 ω) := funext fun ω => hodd (D.g1 ω, D.g2 ω)
  rw [he] at h
  rw [integral_neg] at h
  linarith

private theorem integral_odd_right
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (D : Model P)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hodd : ∀ x : ℝ × ℝ, f (x.1, -x.2) = -f x) :
    ∫ ω, f (D.g1 ω, D.g2 ω) ∂P = 0 := by
  have h := (D.symm_right.comp hf).integral_eq
  change (∫ ω, f (D.g1 ω, D.g2 ω) ∂P) =
    ∫ ω, f (D.g1 ω, -D.g2 ω) ∂P at h
  have he : (fun ω => f (D.g1 ω, -D.g2 ω)) =
      fun ω => -f (D.g1 ω, D.g2 ω) := funext fun ω => hodd (D.g1 ω, D.g2 ω)
  rw [he] at h
  rw [integral_neg] at h
  linarith

private theorem integral_factor
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : Model P) {f : ℝ → ℝ} {g : ℝ × ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    ∫ ω, f (D.pi ω) * g (D.g1 ω, D.g2 ω) ∂P =
      (∫ ω, f (D.pi ω) ∂P) * ∫ ω, g (D.g1 ω, D.g2 ω) ∂P := by
  exact (D.indep.comp hf hg).integral_fun_mul_eq_mul_integral
    (hf.comp_aemeasurable D.memLp_pi.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    (hg.comp_aemeasurable
      (D.memLp_g1.aestronglyMeasurable.aemeasurable.prodMk
        D.memLp_g2.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable

private theorem integrable_two
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f g : Ω → ℝ} (hf : MemLp f 4 P) (hg : MemLp g 4 P) :
    Integrable (fun ω => f ω * g ω) P := by
  exact (hf.mono_exponent (by norm_num : (2 : ENNReal) ≤ 4)).integrable_mul
    (hg.mono_exponent (by norm_num : (2 : ENNReal) ≤ 4))

private theorem integrable_four
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f g h k : Ω → ℝ} (hf : MemLp f 4 P) (hg : MemLp g 4 P)
    (hh : MemLp h 4 P) (hk : MemLp k 4 P) :
    Integrable (fun ω => (f ω * g ω) * (h ω * k ω)) P := by
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [← two_mul, show (4 : ENNReal) = 2 * 2 by norm_num,
      ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]⟩
  exact (hf.mul hg : MemLp (fun ω => f ω * g ω) 2 P).integrable_mul
    (hh.mul hk : MemLp (fun ω => h ω * k ω) 2 P)

private theorem residual_second_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : Model P) {g : Ω → ℝ} (hg : MemLp g 4 P) (hi : IndepFun D.pi g P)
    (q : ℝ) (hα : ∫ ω, (q * D.pi ω + g ω) ^ 2 ∂P = 1) :
    ∫ ω, g ω ^ 2 ∂P = 1 - q ^ 2 := by
  have hp : Integrable (fun ω => D.pi ω ^ 2) P := by
    simpa [pow_two] using integrable_two D.memLp_pi D.memLp_pi
  have hpg := integrable_two D.memLp_pi hg
  have hgg : Integrable (fun ω => g ω ^ 2) P := by
    simpa [pow_two] using integrable_two hg hg
  have hz : ∫ ω, D.pi ω * g ω ∂P = 0 := by
    rw [hi.integral_fun_mul_eq_mul_integral D.memLp_pi.aestronglyMeasurable
      hg.aestronglyMeasurable, D.integral_pi, zero_mul]
  have he : (fun ω => (q * D.pi ω + g ω) ^ 2) =
      fun ω => q ^ 2 * D.pi ω ^ 2 + (2 * q) * (D.pi ω * g ω) + g ω ^ 2 := by
    funext ω
    ring
  rw [he, integral_add (f := fun ω => q ^ 2 * D.pi ω ^ 2 + (2 * q) * (D.pi ω * g ω))
      ((hp.const_mul _).add (hpg.const_mul _)) hgg,
    integral_add (hp.const_mul _) (hpg.const_mul _), integral_const_mul,
    integral_const_mul, D.integral_pi_sq, hz] at hα
  linarith

private def swap
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (D : Model P) : Model P where
  q1 := D.q2
  q2 := D.q1
  pi := D.pi
  g1 := D.g2
  g2 := D.g1
  memLp_pi := D.memLp_pi
  memLp_g1 := D.memLp_g2
  memLp_g2 := D.memLp_g1
  indep := D.indep.comp measurable_id measurable_swap
  symm_left := D.symm_right.comp measurable_swap
  symm_right := D.symm_left.comp measurable_swap
  integral_pi := D.integral_pi
  integral_pi_sq := D.integral_pi_sq
  integral_alpha1_sq := D.integral_alpha2_sq
  integral_alpha2_sq := D.integral_alpha1_sq

/-- The genetic correlation is `E(α₁ α₂) = q₁ q₂` (O'Connor and Price 2018, after Equation 1). -/
theorem integral_alpha1_mul_alpha2 : ∫ ω, D.alpha1 ω * D.alpha2 ω ∂P = D.q1 * D.q2 := by
  have hp : Integrable (fun ω => D.pi ω ^ 2) P := by
    simpa [pow_two] using integrable_two D.memLp_pi D.memLp_pi
  have h1 := integrable_two D.memLp_pi D.memLp_g1
  have h2 := integrable_two D.memLp_pi D.memLp_g2
  have hg := integrable_two D.memLp_g1 D.memLp_g2
  have hz1 : ∫ ω, D.pi ω * D.g1 ω ∂P = 0 := by
    simpa only [id_eq, D.integral_pi, zero_mul] using
      integral_factor D measurable_id measurable_fst
  have hz2 : ∫ ω, D.pi ω * D.g2 ω ∂P = 0 := by
    simpa only [id_eq, D.integral_pi, zero_mul] using
      integral_factor D measurable_id measurable_snd
  have hzg : ∫ ω, D.g1 ω * D.g2 ω ∂P = 0 :=
    integral_odd_left D (measurable_fst.mul measurable_snd) (fun x => by simp)
  have he : (fun ω => D.alpha1 ω * D.alpha2 ω) = fun ω =>
      (D.q1 * D.q2) * D.pi ω ^ 2 + D.q2 * (D.pi ω * D.g1 ω) +
        D.q1 * (D.pi ω * D.g2 ω) + D.g1 ω * D.g2 ω := by
    funext ω
    simp only [alpha1, alpha2]
    ring
  have hs := integral_add
    (((hp.const_mul (D.q1 * D.q2)).add (h1.const_mul D.q2)).add (h2.const_mul D.q1)) hg
  simp only [Pi.add_apply] at hs
  rw [he, hs, integral_add (f := fun ω =>
      (D.q1 * D.q2) * D.pi ω ^ 2 + D.q2 * (D.pi ω * D.g1 ω))
      ((hp.const_mul _).add (h1.const_mul _)) (h2.const_mul _),
    integral_add (hp.const_mul _) (h1.const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul, D.integral_pi_sq, hz1, hz2, hzg]
  ring


/-- **Mixed fourth moment** (O'Connor and Price 2018, Equation 2):
`E(α₁³ α₂) = κ_π q₁³ q₂ + 3 q₁ q₂`. -/
theorem integral_alpha1_pow_three_mul_alpha2 :
    ∫ ω, D.alpha1 ω ^ 3 * D.alpha2 ω ∂P = D.kurtosis * D.q1 ^ 3 * D.q2 + 3 * (D.q1 * D.q2) := by
  have hp := D.memLp_pi
  have hg := D.memLp_g1
  have hh := D.memLp_g2
  have h0 : Integrable (fun ω => D.pi ω ^ 4) P :=
    (integrable_four hp hp hp hp).congr (Filter.Eventually.of_forall fun ω => by ring)
  have h1 : Integrable (fun ω => D.pi ω ^ 3 * D.g2 ω) P :=
    (integrable_four hp hp hp hh).congr (Filter.Eventually.of_forall fun ω => by ring)
  have h2 : Integrable (fun ω => D.pi ω ^ 3 * D.g1 ω) P :=
    (integrable_four hp hp hp hg).congr (Filter.Eventually.of_forall fun ω => by ring)
  have h3 : Integrable (fun ω => D.pi ω ^ 2 * (D.g1 ω * D.g2 ω)) P :=
    (integrable_four hp hp hg hh).congr (Filter.Eventually.of_forall fun ω => by ring)
  have h4 : Integrable (fun ω => D.pi ω ^ 2 * D.g1 ω ^ 2) P :=
    (integrable_four hp hp hg hg).congr (Filter.Eventually.of_forall fun ω => by ring)
  have h5 : Integrable (fun ω => D.pi ω * (D.g1 ω ^ 2 * D.g2 ω)) P :=
    (integrable_four hp hg hg hh).congr (Filter.Eventually.of_forall fun ω => by ring)
  have h6 : Integrable (fun ω => D.pi ω * D.g1 ω ^ 3) P :=
    (integrable_four hp hg hg hg).congr (Filter.Eventually.of_forall fun ω => by ring)
  have h7 : Integrable (fun ω => D.g1 ω ^ 3 * D.g2 ω) P :=
    (integrable_four hg hg hg hh).congr (Filter.Eventually.of_forall fun ω => by ring)
  have zg1 : ∫ ω, D.g1 ω ∂P = 0 :=
    integral_odd_left D measurable_fst (fun x => rfl)
  have zg2 : ∫ ω, D.g2 ω ∂P = 0 :=
    integral_odd_right D measurable_snd (fun x => rfl)
  have zgg : ∫ ω, D.g1 ω * D.g2 ω ∂P = 0 :=
    integral_odd_left D (measurable_fst.mul measurable_snd) (fun x => by simp)
  have z7 : ∫ ω, D.g1 ω ^ 3 * D.g2 ω ∂P = 0 :=
    integral_odd_right D ((measurable_fst.pow_const 3).mul measurable_snd)
      (fun x => by simp)
  have z1 : ∫ ω, D.pi ω ^ 3 * D.g2 ω ∂P = 0 := by
    simpa only [id_eq, zg2, mul_zero] using
      integral_factor D (measurable_id.pow_const 3) measurable_snd
  have z2 : ∫ ω, D.pi ω ^ 3 * D.g1 ω ∂P = 0 := by
    simpa only [id_eq, zg1, mul_zero] using
      integral_factor D (measurable_id.pow_const 3) measurable_fst
  have z3 : ∫ ω, D.pi ω ^ 2 * (D.g1 ω * D.g2 ω) ∂P = 0 := by
    simpa only [id_eq, Pi.mul_apply, zgg, mul_zero] using
      integral_factor D (measurable_id.pow_const 2) (measurable_fst.mul measurable_snd)
  have z5 : ∫ ω, D.pi ω * (D.g1 ω ^ 2 * D.g2 ω) ∂P = 0 := by
    simpa only [id_eq, Pi.mul_apply, D.integral_pi, zero_mul] using integral_factor D measurable_id
      ((measurable_fst.pow_const 2).mul measurable_snd)
  have z6 : ∫ ω, D.pi ω * D.g1 ω ^ 3 ∂P = 0 := by
    simpa only [id_eq, D.integral_pi, zero_mul] using
      integral_factor D measurable_id (measurable_fst.pow_const 3)
  have m4 : ∫ ω, D.pi ω ^ 2 * D.g1 ω ^ 2 ∂P = 1 - D.q1 ^ 2 := by
    have hs := residual_second_moment D hg
      (D.indep.comp measurable_id measurable_fst) D.q1 D.integral_alpha1_sq
    have hf := integral_factor D (measurable_id.pow_const 2) (measurable_fst.pow_const 2)
    simp only [id_eq] at hf
    rw [D.integral_pi_sq, hs, one_mul] at hf
    exact hf
  have he : (fun ω => D.alpha1 ω ^ 3 * D.alpha2 ω) = fun ω =>
      (D.q1 ^ 3 * D.q2) * D.pi ω ^ 4 +
      D.q1 ^ 3 * (D.pi ω ^ 3 * D.g2 ω) +
      (3 * D.q1 ^ 2 * D.q2) * (D.pi ω ^ 3 * D.g1 ω) +
      (3 * D.q1 ^ 2) * (D.pi ω ^ 2 * (D.g1 ω * D.g2 ω)) +
      (3 * D.q1 * D.q2) * (D.pi ω ^ 2 * D.g1 ω ^ 2) +
      (3 * D.q1) * (D.pi ω * (D.g1 ω ^ 2 * D.g2 ω)) +
      D.q2 * (D.pi ω * D.g1 ω ^ 3) + D.g1 ω ^ 3 * D.g2 ω := by
    funext ω
    simp only [alpha1, alpha2]
    ring
  rw [he]
  simp (disch := fun_prop) only [integral_add, integral_const_mul,
    z1, z2, z3, m4, z5, z6, z7, kurtosis]
  ring


/-- The mirror image of Equation 2: `E(α₁ α₂³) = κ_π q₁ q₂³ + 3 q₁ q₂`. -/
theorem integral_alpha1_mul_alpha2_pow_three :
    ∫ ω, D.alpha1 ω * D.alpha2 ω ^ 3 ∂P = D.kurtosis * D.q1 * D.q2 ^ 3 + 3 * (D.q1 * D.q2) := by
  have h := integral_alpha1_pow_three_mul_alpha2 (swap D)
  change (∫ ω, D.alpha2 ω ^ 3 * D.alpha1 ω ∂P) =
    D.kurtosis * D.q2 ^ 3 * D.q1 + 3 * (D.q2 * D.q1) at h
  calc
    (∫ ω, D.alpha1 ω * D.alpha2 ω ^ 3 ∂P) =
        ∫ ω, D.alpha2 ω ^ 3 * D.alpha1 ω ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
    _ = D.kurtosis * D.q1 * D.q2 ^ 3 + 3 * (D.q1 * D.q2) := h.trans (by ring)


/-- Unit variance of `α₁` forces `q₁² ≤ 1` (the non-mediated part has variance `1 - q₁²`). -/
theorem q1_sq_le_one : D.q1 ^ 2 ≤ 1 := by
  have h := residual_second_moment D D.memLp_g1
    (D.indep.comp measurable_id measurable_fst) D.q1 D.integral_alpha1_sq
  have hn : 0 ≤ ∫ ω, D.g1 ω ^ 2 ∂P := integral_nonneg (fun ω => sq_nonneg _)
  linarith


/-- Unit variance of `α₂` forces `q₂² ≤ 1`. -/
theorem q2_sq_le_one : D.q2 ^ 2 ≤ 1 := by
  have h := residual_second_moment D D.memLp_g2
    (D.indep.comp measurable_id measurable_snd) D.q2 D.integral_alpha2_sq
  have hn : 0 ≤ ∫ ω, D.g2 ω ^ 2 ∂P := integral_nonneg (fun ω => sq_nonneg _)
  linarith


/-- `E(π⁴) ≥ (E π²)² = 1`, so the excess kurtosis is at least `-2`. -/
theorem one_le_integral_pi_pow_four : 1 ≤ ∫ ω, D.pi ω ^ 4 ∂P := by
  have hp : Integrable (fun ω => D.pi ω ^ 2) P := by
    simpa [pow_two] using integrable_two D.memLp_pi D.memLp_pi
  have h4 : Integrable (fun ω => D.pi ω ^ 4) P :=
    (integrable_four D.memLp_pi D.memLp_pi D.memLp_pi D.memLp_pi).congr
      (Filter.Eventually.of_forall fun ω => by ring)
  have hn : 0 ≤ ∫ ω, (D.pi ω ^ 2 - 1) ^ 2 ∂P :=
    integral_nonneg (fun ω => sq_nonneg _)
  have he : (fun ω => (D.pi ω ^ 2 - 1) ^ 2) =
      fun ω => D.pi ω ^ 4 - 2 * D.pi ω ^ 2 + 1 := by
    funext ω
    ring
  have hs := integral_add (h4.sub (hp.const_mul 2)) (integrable_const (1 : ℝ))
  simp only [Pi.sub_apply] at hs
  rw [he, hs, integral_sub h4 (hp.const_mul 2), integral_const_mul,
    D.integral_pi_sq] at hn
  have hn' : 0 ≤ (∫ ω, D.pi ω ^ 4 ∂P) - 2 + 1 := by simpa using hn
  linarith


/-- The centred mixed fourth moment: `E(α₁³ α₂) - 3 ρ_g = κ_π q₁³ q₂`. -/
theorem centred_moment_left :
    ∫ ω, D.alpha1 ω ^ 3 * D.alpha2 ω ∂P - 3 * (D.q1 * D.q2) = D.kurtosis * D.q1 ^ 3 * D.q2 := by
  rw [D.integral_alpha1_pow_three_mul_alpha2]
  ring

/-- The centred mixed fourth moment: `E(α₁ α₂³) - 3 ρ_g = κ_π q₁ q₂³`. -/
theorem centred_moment_right :
    ∫ ω, D.alpha1 ω * D.alpha2 ω ^ 3 ∂P - 3 * (D.q1 * D.q2) = D.kurtosis * D.q1 * D.q2 ^ 3 := by
  rw [D.integral_alpha1_mul_alpha2_pow_three]
  ring

/-- **The centred moments order `q₁²` and `q₂²`**: if `κ_π ≠ 0` and `ρ_g = q₁ q₂ ≠ 0`, then
`|E(α₁ α₂³) - 3 ρ_g| ≤ |E(α₁³ α₂) - 3 ρ_g|` iff `q₂² ≤ q₁²`. -/
theorem abs_centredMoment_le_iff (hκ : D.kurtosis ≠ 0) (hρ : D.q1 * D.q2 ≠ 0) :
    |∫ ω, D.alpha1 ω * D.alpha2 ω ^ 3 ∂P - 3 * (D.q1 * D.q2)| ≤
        |∫ ω, D.alpha1 ω ^ 3 * D.alpha2 ω ∂P - 3 * (D.q1 * D.q2)| ↔ D.q2 ^ 2 ≤ D.q1 ^ 2 := by
  rw [D.centred_moment_left, D.centred_moment_right]
  have hc : 0 < |D.kurtosis * (D.q1 * D.q2)| := abs_pos.mpr (mul_ne_zero hκ hρ)
  have e1 : D.kurtosis * D.q1 ^ 3 * D.q2 = D.kurtosis * (D.q1 * D.q2) * D.q1 ^ 2 := by ring
  have e2 : D.kurtosis * D.q1 * D.q2 ^ 3 = D.kurtosis * (D.q1 * D.q2) * D.q2 ^ 2 := by ring
  rw [e1, e2, abs_mul (D.kurtosis * (D.q1 * D.q2)) (D.q1 ^ 2),
    abs_mul (D.kurtosis * (D.q1 * D.q2)) (D.q2 ^ 2), abs_of_nonneg (sq_nonneg D.q1),
    abs_of_nonneg (sq_nonneg D.q2), mul_le_mul_iff_right₀ hc]

private theorem abs_moment_eq (hκ : -2 ≤ D.kurtosis) :
    |∫ ω, D.alpha1 ω ^ 3 * D.alpha2 ω ∂P| = |D.q1 * D.q2| * (D.kurtosis * D.q1 ^ 2 + 3) ∧
      |∫ ω, D.alpha1 ω * D.alpha2 ω ^ 3 ∂P| = |D.q1 * D.q2| * (D.kurtosis * D.q2 ^ 2 + 3) := by
  have h1 := D.q1_sq_le_one
  have h2 := D.q2_sq_le_one
  have p1 : 0 ≤ D.kurtosis * D.q1 ^ 2 + 3 := by nlinarith [sq_nonneg D.q1]
  have p2 : 0 ≤ D.kurtosis * D.q2 ^ 2 + 3 := by nlinarith [sq_nonneg D.q2]
  rw [D.integral_alpha1_pow_three_mul_alpha2, D.integral_alpha1_mul_alpha2_pow_three]
  constructor
  · rw [show D.kurtosis * D.q1 ^ 3 * D.q2 + 3 * (D.q1 * D.q2) =
      D.q1 * D.q2 * (D.kurtosis * D.q1 ^ 2 + 3) by ring, abs_mul, abs_of_nonneg p1]
  · rw [show D.kurtosis * D.q1 * D.q2 ^ 3 + 3 * (D.q1 * D.q2) =
      D.q1 * D.q2 * (D.kurtosis * D.q2 ^ 2 + 3) by ring, abs_mul, abs_of_nonneg p2]

/-- `κ_π ≥ -2`. -/
theorem neg_two_le_kurtosis : -2 ≤ D.kurtosis := by
  have := D.one_le_integral_pi_pow_four
  unfold kurtosis
  linarith

/-- **The paper's uncentred comparison, under its sign condition**: if `κ_π > 0` and
`ρ_g ≠ 0`, then `|E(α₁ α₂³)| ≤ |E(α₁³ α₂)|` iff `q₂² ≤ q₁²` (O'Connor and Price 2018, after
Equation 2, which states the forward implication). -/
theorem abs_moment_le_iff_of_kurtosis_pos (hκ : 0 < D.kurtosis) (hρ : D.q1 * D.q2 ≠ 0) :
    |∫ ω, D.alpha1 ω * D.alpha2 ω ^ 3 ∂P| ≤ |∫ ω, D.alpha1 ω ^ 3 * D.alpha2 ω ∂P| ↔
      D.q2 ^ 2 ≤ D.q1 ^ 2 := by
  obtain ⟨e1, e2⟩ := D.abs_moment_eq D.neg_two_le_kurtosis
  rw [e1, e2, mul_le_mul_iff_right₀ (abs_pos.mpr hρ), add_le_add_iff_right,
    mul_le_mul_iff_right₀ hκ]

/-- **The uncentred comparison is reversed when `κ_π < 0`**: if `κ_π < 0` and `ρ_g ≠ 0`, then
`|E(α₁ α₂³)| ≤ |E(α₁³ α₂)|` iff `q₁² ≤ q₂²`. So the paper's uncentred criterion needs
`κ_π > 0`; the centred criterion `abs_centredMoment_le_iff` does not. -/
theorem abs_moment_le_iff_of_kurtosis_neg (hκ : D.kurtosis < 0) (hρ : D.q1 * D.q2 ≠ 0) :
    |∫ ω, D.alpha1 ω * D.alpha2 ω ^ 3 ∂P| ≤ |∫ ω, D.alpha1 ω ^ 3 * D.alpha2 ω ∂P| ↔
      D.q1 ^ 2 ≤ D.q2 ^ 2 := by
  obtain ⟨e1, e2⟩ := D.abs_moment_eq D.neg_two_le_kurtosis
  rw [e1, e2, mul_le_mul_iff_right₀ (abs_pos.mpr hρ), add_le_add_iff_right,
    mul_le_mul_left_of_neg hκ]

end Model

/-! ### The genetic causality proportion -/

/-- The genetic causality proportion `gcp = (log|q₂| - log|q₁|) / (log|q₂| + log|q₁|)`
(O'Connor and Price 2018, Equation 4). Meaningful for `0 < |q₁|, |q₂| ≤ 1` and `ρ_g² < 1`; for
`|q₁| = |q₂| = 1` the denominator vanishes and the value is `0` by the convention `x / 0 = 0`. -/
noncomputable def gcp (q1 q2 : ℝ) : ℝ :=
  (Real.log |q2| - Real.log |q1|) / (Real.log |q2| + Real.log |q1|)

private theorem log_add_neg {q1 q2 : ℝ} (h1 : q1 ≠ 0) (h2 : q2 ≠ 0) (hρ : (q1 * q2) ^ 2 < 1) :
    Real.log |q2| + Real.log |q1| < 0 := by
  rw [← Real.log_mul (abs_ne_zero.mpr h2) (abs_ne_zero.mpr h1), ← abs_mul]
  apply Real.log_neg (abs_pos.mpr (mul_ne_zero h2 h1))
  have : |q2 * q1| ^ 2 < 1 := by rw [sq_abs, mul_comm]; exact hρ
  nlinarith [abs_nonneg (q2 * q1)]

/-- `gcp ≥ 0` iff `q₂² ≤ q₁²`, for nonzero `q₁, q₂` with `ρ_g² = (q₁ q₂)² < 1`. -/
theorem gcp_nonneg_iff {q1 q2 : ℝ} (h1 : q1 ≠ 0) (h2 : q2 ≠ 0) (hρ : (q1 * q2) ^ 2 < 1) :
    0 ≤ gcp q1 q2 ↔ q2 ^ 2 ≤ q1 ^ 2 := by
  have hd := log_add_neg h1 h2 hρ
  have key : 0 ≤ gcp q1 q2 ↔ Real.log |q2| - Real.log |q1| ≤ 0 := by
    rw [gcp]
    constructor
    · intro h
      by_contra hc
      have := div_neg_of_pos_of_neg (not_le.mp hc) hd
      linarith
    · intro h
      exact div_nonneg_of_nonpos h hd.le
  rw [key, sub_nonpos, Real.log_le_log_iff (abs_pos.mpr h2) (abs_pos.mpr h1), sq_le_sq]

/-- The genetic causality proportion solves the paper's Equation 1:
`q₂² / q₁² = (ρ_g²) ^ gcp` with `ρ_g = q₁ q₂`, for nonzero `q₁, q₂` with `ρ_g² < 1`. -/
theorem rpow_gcp {q1 q2 : ℝ} (h1 : q1 ≠ 0) (h2 : q2 ≠ 0) (hρ : (q1 * q2) ^ 2 < 1) :
    ((q1 * q2) ^ 2) ^ gcp q1 q2 = q2 ^ 2 / q1 ^ 2 := by
  have hd := log_add_neg h1 h2 hρ
  have hpos : 0 < (q1 * q2) ^ 2 := by positivity
  have hlog : Real.log ((q1 * q2) ^ 2) = 2 * (Real.log |q2| + Real.log |q1|) := by
    rw [← sq_abs, abs_mul, Real.log_pow, Real.log_mul (abs_ne_zero.mpr h1)
      (abs_ne_zero.mpr h2)]
    push_cast
    ring
  have hexp (q : ℝ) (hq : q ≠ 0) : Real.exp (2 * Real.log |q|) = q ^ 2 := by
    rw [show (2 : ℝ) * Real.log |q| = Real.log (|q| ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity), sq_abs]
  have harg : Real.log ((q1 * q2) ^ 2) * gcp q1 q2 =
      2 * Real.log |q2| - 2 * Real.log |q1| := by
    have hd' : Real.log |q2| + Real.log |q1| ≠ 0 := hd.ne
    rw [hlog, gcp]
    field_simp
  rw [Real.rpow_def_of_pos hpos, harg, Real.exp_sub, hexp q1 h1, hexp q2 h2]

/-- `gcp ≤ 1` when `q₁² ≤ 1` (for nonzero `q₁, q₂` with `ρ_g² < 1`). -/
theorem gcp_le_one {q1 q2 : ℝ} (h1 : q1 ≠ 0) (h2 : q2 ≠ 0) (hρ : (q1 * q2) ^ 2 < 1)
    (hq1 : q1 ^ 2 ≤ 1) : gcp q1 q2 ≤ 1 := by
  have hd := log_add_neg h1 h2 hρ
  have hl : Real.log |q1| ≤ 0 :=
    Real.log_nonpos (abs_nonneg q1) ((sq_le_one_iff_abs_le_one q1).mp hq1)
  rw [gcp, div_le_one_of_neg hd]
  linarith

/-- `-1 ≤ gcp` when `q₂² ≤ 1` (for nonzero `q₁, q₂` with `ρ_g² < 1`). -/
theorem neg_one_le_gcp {q1 q2 : ℝ} (h1 : q1 ≠ 0) (h2 : q2 ≠ 0) (hρ : (q1 * q2) ^ 2 < 1)
    (hq2 : q2 ^ 2 ≤ 1) : -1 ≤ gcp q1 q2 := by
  have hd := log_add_neg h1 h2 hρ
  have hl : Real.log |q2| ≤ 0 :=
    Real.log_nonpos (abs_nonneg q2) ((sq_le_one_iff_abs_le_one q2).mp hq2)
  rw [gcp, le_div_iff_of_neg hd]
  linarith

/-- **The paper's criterion for `gcp ≥ 0`** (O'Connor and Price 2018, after Equation 2), under
the sign condition `κ_π > 0` that it needs: if `ρ_g ≠ 0`, `ρ_g² < 1` and
`|E(α₁ α₂³)| ≤ |E(α₁³ α₂)|`, then `gcp ≥ 0`. -/
theorem Model.gcp_nonneg_of_abs_moment_le {P : Measure Ω} [IsProbabilityMeasure P] (D : Model P)
    (hκ : 0 < D.kurtosis) (hρ : D.q1 * D.q2 ≠ 0) (hρ1 : (D.q1 * D.q2) ^ 2 < 1)
    (h : |∫ ω, D.alpha1 ω * D.alpha2 ω ^ 3 ∂P| ≤ |∫ ω, D.alpha1 ω ^ 3 * D.alpha2 ω ∂P|) :
    0 ≤ gcp D.q1 D.q2 :=
  (gcp_nonneg_iff (left_ne_zero_of_mul hρ) (right_ne_zero_of_mul hρ) hρ1).mpr
    ((D.abs_moment_le_iff_of_kurtosis_pos hκ hρ).mp h)

end MathlibExt.Biology.StatisticalGenetics.LatentCausalVariable
