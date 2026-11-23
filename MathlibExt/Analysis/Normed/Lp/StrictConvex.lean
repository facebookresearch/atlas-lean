/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Convex.StrictConvexSpace

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Strict convexity of `L^p` spaces for `1 < p < ∞`

For `1 < p < ∞` the norm of the `L^p` space `Lp 𝕜 p μ` (over `𝕜 = ℝ` or `ℂ`)
is strictly convex: a nontrivial convex combination of two distinct vectors in
the closed unit ball has norm `< 1`. The proof is pointwise: for scalars
`a ≠ b` the strict convexity of `t ↦ t ^ q` on `[0, ∞)` and the strict
triangle inequality in `𝕜` give
`‖(1 - t) • a + t • b‖ ^ q < (1 - t) * ‖a‖ ^ q + t * ‖b‖ ^ q`, and the
integral of the left side is strictly smaller than the integral of the right
side because the two sides differ on the positive-measure set where the
representatives differ (`lintegral_strict_mono_of_ae_le_of_frequently_ae_lt`).

Two classical consequences follow from the same estimate:

* the equality case of Minkowski's inequality (the triangle inequality) in
  `L^p`: if `‖f + g‖ = ‖f‖ + ‖g‖` with `f, g ≠ 0`, then `g = c • f` for
  some `c ≥ 0`;
* uniqueness of a best approximation: a convex subset of `L^p` contains at
  most one point nearest to a given point (existence is not claimed).

This is a companion to the `L^p`-norm material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/LpSpaces.lean` (Hölder's and
Minkowski's inequalities), not one of the book's 72 numbered targets. It
generalizes batch 69 (`LpGeometry.lean`), which proved strict convexity only
for the two-dimensional real space `PiLp p (Fin 2 → ℝ)`, to arbitrary measure
spaces and to `𝕜 = ℂ`, and for arbitrary convex combinations, not just
midpoints. Batch 42 (`ConvexProjection.lean`) proves uniqueness of the nearest
point in an inner-product space via the parallelogram law; the proof here uses
strict convexity instead and applies to `L^p` for `p ≠ 2`, where no inner
product induces the norm.

Classical references: Rudin, *Functional Analysis*, 2nd edition; Brezis,
*Functional Analysis, Sobolev Spaces and Partial Differential Equations*
(the `L^p` spaces and their geometry).

## Main declarations

* `norm_convex_comb_rpow_le` / `norm_convex_comb_rpow_lt` : the pointwise
  scalar (non-strict / strict) convexity estimate for `‖·‖ ^ q` in `𝕜`.
* `enorm_convex_comb_rpow_le` / `enorm_convex_comb_rpow_lt` : the same
  estimates in `ℝ≥0∞` form, for integration.
* `norm_convex_comb_lt_of_norm_eq_one` /
  `norm_convex_comb_lt_of_norm_le_one` : strict convexity of the unit ball
  of `Lp 𝕜 p μ` for `1 < p < ∞`.
* `norm_midpoint_lt_of_norm_eq_one` : the midpoint form.
* `exists_nonneg_smul_eq_of_norm_add_eq` : the equality case of Minkowski's
  inequality in `L^p`.
* `eq_of_forall_norm_sub_le_of_convex` : uniqueness of a best approximation
  in `L^p` from a convex set.
* `StrictConvexSpace ℝ (Lp ℝ p μ)` : the instance form of the midpoint estimate
  for real `L^p` spaces.
-/

@[expose] public section

namespace MathlibExt.Analysis.Normed.Lp.StrictConvex

open MeasureTheory

open scoped ENNReal

theorem norm_convex_comb_rpow_le {𝕜 : Type*} [RCLike 𝕜] {a b : 𝕜} {t q : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hq : 1 ≤ q) :
    ‖(1 - t) • a + t • b‖ ^ q ≤ (1 - t) * ‖a‖ ^ q + t * ‖b‖ ^ q := by
  have h1t : 0 ≤ 1 - t := by linarith
  have htri : ‖(1 - t) • a + t • b‖ ≤ (1 - t) * ‖a‖ + t * ‖b‖ := by
    calc ‖(1 - t) • a + t • b‖ ≤ ‖(1 - t) • a‖ + ‖t • b‖ := norm_add_le _ _
      _ = (1 - t) * ‖a‖ + t * ‖b‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg h1t, Real.norm_of_nonneg ht0]
  calc ‖(1 - t) • a + t • b‖ ^ q
      ≤ ((1 - t) * ‖a‖ + t * ‖b‖) ^ q :=
        Real.rpow_le_rpow (norm_nonneg _) htri (by linarith : (0:ℝ) ≤ q)
    _ ≤ (1 - t) * ‖a‖ ^ q + t * ‖b‖ ^ q := by
        have hconv := (convexOn_rpow hq).2 (Set.mem_Ici.mpr (norm_nonneg a))
          (Set.mem_Ici.mpr (norm_nonneg b)) h1t ht0 (by linarith : (1 - t) + t = 1)
        simpa [smul_eq_mul] using hconv

theorem norm_convex_comb_rpow_lt {𝕜 : Type*} [RCLike 𝕜] {a b : 𝕜} (hab : a ≠ b) {t q : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hq : 1 < q) :
    ‖(1 - t) • a + t • b‖ ^ q < (1 - t) * ‖a‖ ^ q + t * ‖b‖ ^ q := by
  have h1t : 0 < 1 - t := by linarith
  have htri : ‖(1 - t) • a + t • b‖ ≤ (1 - t) * ‖a‖ + t * ‖b‖ := by
    calc ‖(1 - t) • a + t • b‖ ≤ ‖(1 - t) • a‖ + ‖t • b‖ := norm_add_le _ _
      _ = (1 - t) * ‖a‖ + t * ‖b‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg h1t.le, Real.norm_of_nonneg ht0.le]
  by_cases hnorm : ‖a‖ = ‖b‖
  · by_cases hr : ‖a‖ = 0
    · have ha : a = 0 := norm_eq_zero.mp hr
      have hb : b = 0 := norm_eq_zero.mp (by rw [← hnorm]; exact hr)
      exact absurd (ha.trans hb.symm) hab
    · have hlt_tri : ‖(1 - t) • a + t • b‖ < (1 - t) * ‖a‖ + t * ‖b‖ := by
        by_contra hcon
        rw [not_lt] at hcon
        have heq : ‖(1 - t) • a + t • b‖ = (1 - t) * ‖a‖ + t * ‖b‖ :=
          le_antisymm htri hcon
        have heq' : ‖(1 - t) • a + t • b‖ = ‖(1 - t) • a‖ + ‖t • b‖ := by
          rw [heq, norm_smul, norm_smul, Real.norm_of_nonneg h1t.le,
            Real.norm_of_nonneg ht0.le]
        have hsm : ‖t • b‖ • ((1 - t) • a) = ‖(1 - t) • a‖ • (t • b) :=
          norm_add_eq_iff_real.mp heq'
        rw [norm_smul, norm_smul, Real.norm_of_nonneg h1t.le,
          Real.norm_of_nonneg ht0.le, hnorm] at hsm
        simp only [smul_smul] at hsm
        have hb0 : ‖b‖ ≠ 0 := by rw [hnorm] at hr; exact hr
        have hcoef : (1 - t) * ‖b‖ * t ≠ 0 :=
          mul_ne_zero (mul_ne_zero h1t.ne' hb0) ht0.ne'
        have hcoef_eq : t * ‖b‖ * (1 - t) = (1 - t) * ‖b‖ * t := by ring
        rw [hcoef_eq] at hsm
        have hab2 : a = b := by
          have h2 := congrArg (((1 - t) * ‖b‖ * t)⁻¹ • ·) hsm
          rw [smul_smul, smul_smul, inv_mul_cancel₀ hcoef, one_smul, one_smul] at h2
          exact h2
        exact hab hab2
      have hrpow : ‖(1 - t) • a + t • b‖ ^ q < ((1 - t) * ‖a‖ + t * ‖b‖) ^ q :=
        Real.rpow_lt_rpow (norm_nonneg _) hlt_tri (by linarith : (0:ℝ) < q)
      have e1 : (1 - t) * ‖a‖ + t * ‖b‖ = ‖a‖ := by rw [hnorm]; ring
      have e2 : (1 - t) * ‖a‖ ^ q + t * ‖b‖ ^ q = ‖a‖ ^ q := by rw [hnorm]; ring
      rw [e1] at hrpow
      rw [e2]
      exact hrpow
  · have hconv := (strictConvexOn_rpow hq).2 (Set.mem_Ici.mpr (norm_nonneg a))
      (Set.mem_Ici.mpr (norm_nonneg b)) hnorm h1t ht0 (by ring : (1 - t) + t = 1)
    have h1 : ‖(1 - t) • a + t • b‖ ^ q ≤ ((1 - t) * ‖a‖ + t * ‖b‖) ^ q :=
      Real.rpow_le_rpow (norm_nonneg _) htri (by linarith : (0:ℝ) ≤ q)
    calc ‖(1 - t) • a + t • b‖ ^ q
        ≤ ((1 - t) * ‖a‖ + t * ‖b‖) ^ q := h1
      _ < (1 - t) * ‖a‖ ^ q + t * ‖b‖ ^ q := by simpa [smul_eq_mul] using hconv

theorem enorm_convex_comb_rpow_le {𝕜 : Type*} [RCLike 𝕜] {a b : 𝕜} {t q : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hq : 1 ≤ q) :
    ‖(1 - t) • a + t • b‖ₑ ^ q ≤
      ENNReal.ofReal (1 - t) * ‖a‖ₑ ^ q + ENNReal.ofReal t * ‖b‖ₑ ^ q := by
  have hq0 : (0:ℝ) ≤ q := by linarith
  have h1t : 0 ≤ 1 - t := by linarith
  calc ‖(1 - t) • a + t • b‖ₑ ^ q
      = ENNReal.ofReal (‖(1 - t) • a + t • b‖ ^ q) := by
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0]
    _ ≤ ENNReal.ofReal ((1 - t) * ‖a‖ ^ q + t * ‖b‖ ^ q) :=
        ENNReal.ofReal_le_ofReal (norm_convex_comb_rpow_le ht0 ht1 hq)
    _ = ENNReal.ofReal (1 - t) * ‖a‖ₑ ^ q + ENNReal.ofReal t * ‖b‖ₑ ^ q := by
        rw [ENNReal.ofReal_add (mul_nonneg h1t (Real.rpow_nonneg (norm_nonneg _) _))
          (mul_nonneg ht0 (Real.rpow_nonneg (norm_nonneg _) _)),
          ENNReal.ofReal_mul h1t, ENNReal.ofReal_mul ht0,
          ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0,
          ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0, ofReal_norm, ofReal_norm]

theorem enorm_convex_comb_rpow_lt {𝕜 : Type*} [RCLike 𝕜] {a b : 𝕜} (hab : a ≠ b) {t q : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hq : 1 < q) :
    ‖(1 - t) • a + t • b‖ₑ ^ q <
      ENNReal.ofReal (1 - t) * ‖a‖ₑ ^ q + ENNReal.ofReal t * ‖b‖ₑ ^ q := by
  have hq0 : (0:ℝ) ≤ q := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hRHS_pos : (0:ℝ) < (1 - t) * ‖a‖ ^ q + t * ‖b‖ ^ q := by
    by_cases ha : a = 0
    · subst ha
      have hb : b ≠ 0 := by rintro rfl; exact hab rfl
      have hbp : 0 < ‖b‖ ^ q := Real.rpow_pos_of_pos (norm_pos_iff.mpr hb) _
      nlinarith [mul_pos ht0 hbp, Real.rpow_nonneg (norm_nonneg (0 : 𝕜)) q]
    · have hap : 0 < ‖a‖ ^ q := Real.rpow_pos_of_pos (norm_pos_iff.mpr ha) _
      nlinarith [mul_pos h1t hap, Real.rpow_nonneg (norm_nonneg b) q]
  calc ‖(1 - t) • a + t • b‖ₑ ^ q
      = ENNReal.ofReal (‖(1 - t) • a + t • b‖ ^ q) := by
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0]
    _ < ENNReal.ofReal ((1 - t) * ‖a‖ ^ q + t * ‖b‖ ^ q) :=
        (ENNReal.ofReal_lt_ofReal_iff hRHS_pos).mpr
          (norm_convex_comb_rpow_lt hab ht0 ht1 hq)
    _ = ENNReal.ofReal (1 - t) * ‖a‖ₑ ^ q + ENNReal.ofReal t * ‖b‖ₑ ^ q := by
        rw [ENNReal.ofReal_add (mul_nonneg h1t.le (Real.rpow_nonneg (norm_nonneg _) _))
          (mul_nonneg ht0.le (Real.rpow_nonneg (norm_nonneg _) _)),
          ENNReal.ofReal_mul h1t.le, ENNReal.ofReal_mul ht0.le,
          ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0,
          ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0, ofReal_norm, ofReal_norm]


theorem ne_zero_of_one_lt_toReal {p : ℝ≥0∞} (hp : 1 < p.toReal) : p ≠ 0 := by
  rintro rfl
  rw [ENNReal.toReal_zero] at hp
  exact (by norm_num : ¬ (1:ℝ) < (0:ℝ)) hp

theorem ne_top_of_one_lt_toReal {p : ℝ≥0∞} (hp : 1 < p.toReal) : p ≠ ⊤ := by
  rintro rfl
  rw [ENNReal.toReal_top] at hp
  exact (by norm_num : ¬ (1:ℝ) < (0:ℝ)) hp

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {𝕜 : Type*} [RCLike 𝕜]

omit [Fact (1 ≤ p)] in
theorem lintegral_enorm_rpow_ne_top {f : Lp 𝕜 p μ} (hp : 1 < p.toReal) :
    ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ ≠ ⊤ := by
  have hp0 : p ≠ 0 := ne_zero_of_one_lt_toReal hp
  have hptop : p ≠ ⊤ := ne_top_of_one_lt_toReal hp
  have hfq : (0:ℝ) < p.toReal := by linarith
  intro htop
  have h := (Lp.memLp f).eLpNorm_lt_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop (Lp.aestronglyMeasurable f), htop,
    ENNReal.top_rpow_of_pos (by positivity : (0:ℝ) < 1 / p.toReal)] at h
  exact (lt_irrefl _ h).elim

theorem lintegral_enorm_rpow_eq_one {f : Lp 𝕜 p μ} (hf : ‖f‖ = 1) (hp : 1 < p.toReal) :
    ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ = 1 := by
  have hp0 : p ≠ 0 := ne_zero_of_one_lt_toReal hp
  have hptop : p ≠ ⊤ := ne_top_of_one_lt_toReal hp
  have hfq : (0:ℝ) < p.toReal := by linarith
  have henorm : eLpNorm (⇑f) p μ = 1 := by
    have h1 : ‖f‖ₑ = 1 := by rw [← ofReal_norm, hf]; norm_num
    rwa [Lp.enorm_def] at h1
  have hI : (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) = 1 := by
    rw [← eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop (Lp.aestronglyMeasurable f)]
    exact henorm
  have h := congrArg (· ^ p.toReal) hI
  rw [← ENNReal.rpow_mul, div_mul_cancel₀ (1:ℝ) hfq.ne', ENNReal.rpow_one,
    ENNReal.one_rpow] at h
  exact h

theorem norm_convex_comb_lt_of_norm_eq_one {f g : Lp 𝕜 p μ} (hfg : f ≠ g)
    (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hp : 1 < p.toReal) :
    ‖(1 - t) • f + t • g‖ < 1 := by
  have hp0 : p ≠ 0 := ne_zero_of_one_lt_toReal hp
  have hptop : p ≠ ⊤ := ne_top_of_one_lt_toReal hp
  have hfq : (0:ℝ) < p.toReal := by linarith
  have hcombo : ⇑((1 - t) • f + t • g) =ᵐ[μ] fun x => (1 - t) • f x + t • g x := by
    have h1 : ⇑((1 - t) • f + t • g) =ᵐ[μ] ⇑((1 - t) • f) + ⇑(t • g) := Lp.coeFn_add _ _
    have h2 : ⇑((1 - t) • f) =ᵐ[μ] fun x => (1 - t) • f x := Lp.coeFn_smul _ _
    have h3 : ⇑(t • g) =ᵐ[μ] fun x => t • g x := Lp.coeFn_smul _ _
    exact h1.trans (h2.add h3)
  have hle : (fun x => ‖((1 - t) • f + t • g) x‖ₑ ^ p.toReal) ≤ᵐ[μ]
      (fun x => ENNReal.ofReal (1 - t) * ‖f x‖ₑ ^ p.toReal +
        ENNReal.ofReal t * ‖g x‖ₑ ^ p.toReal) := by
    filter_upwards [hcombo] with x hx
    rw [hx]
    exact enorm_convex_comb_rpow_le ht0.le ht1.le hp.le
  have hfreq : ∃ᵐ x ∂μ,
      ‖((1 - t) • f + t • g) x‖ₑ ^ p.toReal ≠
        ENNReal.ofReal (1 - t) * ‖f x‖ₑ ^ p.toReal +
          ENNReal.ofReal t * ‖g x‖ₑ ^ p.toReal := by
    have hne : ∃ᵐ x ∂μ, f x ≠ g x := by
      by_contra hcon
      rw [Filter.not_frequently] at hcon
      exact hfg (Lp.ext_iff.mpr (hcon.mono fun x hx => not_not.mp hx))
    exact (hne.and_eventually hcombo).mono fun x ⟨hxne, hxcombo⟩ => by
      rw [hxcombo]
      exact ne_of_lt (enorm_convex_comb_rpow_lt hxne ht0 ht1 hp)
  have hf' : AEMeasurable (fun x => ‖f x‖ₑ ^ p.toReal) μ :=
    (ENNReal.continuous_rpow_const.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable f).enorm.aestronglyMeasurable).aemeasurable
  have hg' : AEMeasurable (fun x => ‖g x‖ₑ ^ p.toReal) μ :=
    (ENNReal.continuous_rpow_const.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable g).enorm.aestronglyMeasurable).aemeasurable
  have hG_aemeas : AEMeasurable
      (fun x => ENNReal.ofReal (1 - t) * ‖f x‖ₑ ^ p.toReal +
        ENNReal.ofReal t * ‖g x‖ₑ ^ p.toReal) μ := by
    exact (hf'.const_mul _).add (hg'.const_mul _)
  have hF_ne_top : ∫⁻ x, ‖((1 - t) • f + t • g) x‖ₑ ^ p.toReal ∂μ ≠ ⊤ :=
    lintegral_enorm_rpow_ne_top hp
  have hlt : ∫⁻ x, ‖((1 - t) • f + t • g) x‖ₑ ^ p.toReal ∂μ <
      ∫⁻ x, (ENNReal.ofReal (1 - t) * ‖f x‖ₑ ^ p.toReal +
        ENNReal.ofReal t * ‖g x‖ₑ ^ p.toReal) ∂μ :=
    lintegral_strict_mono_of_ae_le_of_frequently_ae_lt hG_aemeas hF_ne_top hle hfreq
  have hG_eq : ∫⁻ x, (ENNReal.ofReal (1 - t) * ‖f x‖ₑ ^ p.toReal +
        ENNReal.ofReal t * ‖g x‖ₑ ^ p.toReal) ∂μ = 1 := by
    rw [lintegral_add_left' (hf'.const_mul _) _
      , lintegral_const_mul'' _ hf', lintegral_const_mul'' _ hg',
      lintegral_enorm_rpow_eq_one hf hp, lintegral_enorm_rpow_eq_one hg hp,
      mul_one, mul_one,
      ← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ 1 - t) ht0.le, sub_add_cancel,
      ENNReal.ofReal_one]
  have hF_lt_one : ∫⁻ x, ‖((1 - t) • f + t • g) x‖ₑ ^ p.toReal ∂μ < 1 :=
    hlt.trans_eq hG_eq
  have h1 : (∫⁻ x, ‖((1 - t) • f + t • g) x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) < 1 := by
    have hr := ENNReal.rpow_lt_rpow hF_lt_one (by positivity : (0:ℝ) < 1 / p.toReal)
    rwa [ENNReal.one_rpow] at hr
  rw [Lp.norm_def,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop (Lp.aestronglyMeasurable _)]
  have hne_top : (∫⁻ x, ‖((1 - t) • f + t • g) x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) ≠ ⊤ :=
    ne_top_of_lt h1
  simpa using (ENNReal.toReal_lt_toReal hne_top ENNReal.one_ne_top).mpr h1

theorem norm_convex_comb_lt_of_norm_le_one {f g : Lp 𝕜 p μ} (hfg : f ≠ g)
    (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hp : 1 < p.toReal) :
    ‖(1 - t) • f + t • g‖ < 1 := by
  by_cases h1 : ‖f‖ = 1 ∧ ‖g‖ = 1
  · exact norm_convex_comb_lt_of_norm_eq_one hfg h1.1 h1.2 ht0 ht1 hp
  · have hlt : (1 - t) * ‖f‖ + t * ‖g‖ < 1 := by
      have h1t : (0:ℝ) < 1 - t := by linarith
      rcases not_and_or.mp h1 with hne1 | hne2
      · have hltf : ‖f‖ < 1 := lt_of_le_of_ne hf hne1
        have h2 : (1 - t) * ‖f‖ < (1 - t) * 1 :=
          mul_lt_mul_of_pos_left hltf h1t
        have h3 : t * ‖g‖ ≤ t * 1 := mul_le_mul_of_nonneg_left hg ht0.le
        linarith
      · have hltg : ‖g‖ < 1 := lt_of_le_of_ne hg hne2
        have h2 : (1 - t) * ‖f‖ ≤ (1 - t) * 1 :=
          mul_le_mul_of_nonneg_left hf h1t.le
        have h3 : t * ‖g‖ < t * 1 := mul_lt_mul_of_pos_left hltg ht0
        linarith
    calc ‖(1 - t) • f + t • g‖ ≤ ‖(1 - t) • f‖ + ‖t • g‖ := norm_add_le _ _
      _ = (1 - t) * ‖f‖ + t * ‖g‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t),
          Real.norm_of_nonneg ht0.le]
      _ < 1 := hlt

theorem norm_midpoint_lt_of_norm_eq_one {f g : Lp 𝕜 p μ} (hfg : f ≠ g)
    (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) (hp : 1 < p.toReal) :
    ‖(1 / 2 : ℝ) • f + (1 / 2 : ℝ) • g‖ < 1 := by
  have h := norm_convex_comb_lt_of_norm_eq_one (t := 1 / 2) hfg hf hg
    (by norm_num) (by norm_num) hp
  have h2 : (1:ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rwa [h2] at h

/-- The real `L^p` space is strictly convex for `1 < p < ∞`: the instance form
of `norm_midpoint_lt_of_norm_eq_one`, via Mathlib's
`StrictConvexSpace.of_norm_combo_lt_one` constructor. -/
instance {p : ℝ≥0∞} [Fact (1 ≤ p)] [hp : Fact (1 < p.toReal)] :
    StrictConvexSpace ℝ (Lp ℝ p μ) := by
  apply StrictConvexSpace.of_norm_combo_lt_one
  intro x y hx hy hne
  exact ⟨1 / 2, 1 / 2, by norm_num,
    norm_midpoint_lt_of_norm_eq_one hne hx hy hp.out⟩

theorem exists_nonneg_smul_eq_of_norm_add_eq {f g : Lp 𝕜 p μ} (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (h : ‖f + g‖ = ‖f‖ + ‖g‖) (hp : 1 < p.toReal) :
    ∃ c : ℝ, 0 ≤ c ∧ g = c • f := by
  have hfa : 0 < ‖f‖ := norm_pos_iff.mpr hf0
  have hgb : 0 < ‖g‖ := norm_pos_iff.mpr hg0
  have hsum : 0 < ‖f‖ + ‖g‖ := add_pos hfa hgb
  -- unit vectors
  set u : Lp 𝕜 p μ := (‖f‖⁻¹) • f with hu
  set v : Lp 𝕜 p μ := (‖g‖⁻¹) • g with hv
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hfa.le), inv_mul_cancel₀ hfa.ne']
  have hv1 : ‖v‖ = 1 := by
    rw [hv, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hgb.le), inv_mul_cancel₀ hgb.ne']
  have huv : u = v := by
    by_contra hne
    -- the convex combination with weights ‖f‖/(‖f‖+‖g‖), ‖g‖/(‖f‖+‖g‖)
    set s : ℝ := ‖f‖ + ‖g‖ with hs
    have ht : (0:ℝ) < ‖g‖ / s := div_pos hgb hsum
    have ht1 : ‖g‖ / s < 1 := by
      rw [div_lt_one hsum]; linarith
    have hw : 1 - ‖g‖ / s = ‖f‖ / s := by
      have hself : s / s = 1 := div_self hsum.ne'
      have h1 : (s - ‖g‖) / s = ‖f‖ / s := by
        congr 1
        rw [hs]
        ring
      rw [← h1, ← div_sub_div_same, hself]
    have hcomb : (1 - ‖g‖ / s) • u + (‖g‖ / s) • v = (1 / s) • (f + g) := by
      have e1 : (1 - ‖g‖ / s) • u = (1 / s) • f := by
        rw [hu, smul_smul]
        congr 1
        rw [hw, div_mul_eq_mul_div, mul_inv_cancel₀ hfa.ne', one_div]
      have e2 : (‖g‖ / s) • v = (1 / s) • g := by
        rw [hv, smul_smul]
        congr 1
        rw [div_mul_eq_mul_div, mul_inv_cancel₀ hgb.ne', one_div]
      rw [e1, e2, smul_add]
    have hnorm : ‖(1 - ‖g‖ / s) • u + (‖g‖ / s) • v‖ < 1 :=
      norm_convex_comb_lt_of_norm_eq_one hne hu1 hv1 ht ht1 hp
    rw [hcomb, norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 / s), h] at hnorm
    rw [div_mul_cancel₀ _ hsum.ne'] at hnorm
    exact (lt_irrefl _ hnorm).elim
  -- g = (‖g‖ / ‖f‖) • f
  refine ⟨‖g‖ / ‖f‖, div_nonneg hgb.le hfa.le, ?_⟩
  have h1 : g = ‖g‖ • v := by
    rw [hv, smul_smul, mul_inv_cancel₀ hgb.ne', one_smul]
  have h2 : v = ‖f‖⁻¹ • f := huv.symm.trans hu
  have hsc : ‖g‖ * ‖f‖⁻¹ = ‖g‖ / ‖f‖ := by rw [div_eq_mul_inv]
  calc g = ‖g‖ • v := h1
    _ = ‖g‖ • (‖f‖⁻¹ • f) := by rw [h2]
    _ = (‖g‖ * ‖f‖⁻¹) • f := by rw [smul_smul]
    _ = (‖g‖ / ‖f‖) • f := by rw [hsc]

theorem eq_of_forall_norm_sub_le_of_convex {K : Set (Lp 𝕜 p μ)} (hK : Convex ℝ K)
    {x p₀ q₀ : Lp 𝕜 p μ} (hp₀ : p₀ ∈ K) (hq₀ : q₀ ∈ K)
    (hpmin : ∀ y ∈ K, ‖p₀ - x‖ ≤ ‖y - x‖) (hqmin : ∀ y ∈ K, ‖q₀ - x‖ ≤ ‖y - x‖)
    (hp : 1 < p.toReal) :
    p₀ = q₀ := by
  by_contra hne
  have hd : ‖p₀ - x‖ = ‖q₀ - x‖ :=
    le_antisymm (hpmin q₀ hq₀) (hqmin p₀ hp₀)
  by_cases hd0 : ‖p₀ - x‖ = 0
  · have hx1 : p₀ = x := by
      have := norm_eq_zero.mp hd0
      exact sub_eq_zero.mp this
    have hx2 : q₀ = x := by
      have h2 : ‖q₀ - x‖ = 0 := by rw [← hd]; exact hd0
      exact sub_eq_zero.mp (norm_eq_zero.mp h2)
    exact hne (hx1.trans hx2.symm)
  · have hdpos : 0 < ‖p₀ - x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd0)
    -- midpoint of p₀ and q₀ lies in K and is strictly closer to x
    have hmid : (1 / 2 : ℝ) • p₀ + (1 / 2 : ℝ) • q₀ ∈ K :=
      hK hp₀ hq₀ (by norm_num) (by norm_num) (by norm_num)
    have hdne : ‖p₀ - x‖ ≠ 0 := hdpos.ne'
    have hdne2 : ‖q₀ - x‖ ≠ 0 := by rw [← hd]; exact hdne
    have hscale : ∀ y : Lp 𝕜 p μ, (1 / 2 : ℝ) • y =
        ‖p₀ - x‖ • ((1 / 2 : ℝ) • ((‖p₀ - x‖⁻¹) • y)) := by
      intro y
      rw [smul_comm, smul_smul, smul_smul, mul_assoc, mul_inv_cancel₀ hdne, mul_one]
    have hA : (1 / 2 : ℝ) • p₀ + (1 / 2 : ℝ) • q₀ - x =
        (1 / 2 : ℝ) • (p₀ - x) + (1 / 2 : ℝ) • (q₀ - x) := by module
    have hB : (1 / 2 : ℝ) • (p₀ - x) + (1 / 2 : ℝ) • (q₀ - x) =
        ‖p₀ - x‖ • ((1 / 2 : ℝ) • ((‖p₀ - x‖⁻¹) • (p₀ - x)) +
          (1 / 2 : ℝ) • ((‖p₀ - x‖⁻¹) • (q₀ - x))) := by
      rw [smul_add, ← hscale, ← hscale]
    have hu1 : ‖(‖p₀ - x‖⁻¹) • (p₀ - x)‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hdpos.le),
        inv_mul_cancel₀ hdne]
    have hv1 : ‖(‖p₀ - x‖⁻¹) • (q₀ - x)‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hdpos.le), hd,
        inv_mul_cancel₀ hdne2]
    have huv : (‖p₀ - x‖⁻¹) • (p₀ - x) ≠ (‖p₀ - x‖⁻¹) • (q₀ - x) := by
      intro hcon
      apply hne
      have h2 := congrArg ((‖p₀ - x‖) • ·) hcon
      rw [smul_smul, smul_smul, mul_inv_cancel₀ hdne, one_smul, one_smul] at h2
      exact sub_left_injective h2
    have hlt := norm_midpoint_lt_of_norm_eq_one huv hu1 hv1 hp
    have hnorm : ‖(1 / 2 : ℝ) • p₀ + (1 / 2 : ℝ) • q₀ - x‖ < ‖p₀ - x‖ := by
      rw [hA, hB, norm_smul, Real.norm_of_nonneg hdpos.le]
      have hlt' := mul_lt_mul_of_pos_left hlt hdpos
      rwa [mul_one] at hlt'
    have hle := hpmin _ hmid
    linarith

end MathlibExt.Analysis.Normed.Lp.StrictConvex
