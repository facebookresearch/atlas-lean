/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import MathlibExt.Probability.Distributions.GaussianDensity
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import MathlibExt.MeasureTheory.Integral.PrekopaLeindler

/-!
# Gross' logarithmic Sobolev inequality for the Gaussian measure

Let `γ` be the standard Gaussian measure on a finite-dimensional real inner product space `E`.
For every smooth positive `f : E → ℝ` with `∫ f dγ = 1`,

`KL(f γ ‖ γ) = ∫ f log f dγ ≤ ½ ∫ ‖Df‖² / f dγ`

(L. Gross, 1975; M. Ledoux, ICM 2014, Theorem 2.1). Both sides are taken in `[0, ∞]`: when the
right-hand side is finite, so is the relative entropy.

## Proof outline

The proof is the argument of S. G. Bobkov and M. Ledoux (2000, Proposition 3.1, whose
convexity condition (3.1) holds with `c = 1` for the Gaussian potential
`V(x) = ‖x‖² / 2 + (n / 2) log (2π)`), which derives the inequality from the Prékopa–Leindler
inequality, completed by an approximation step for functions that are not constant outside a
compact set.

1. *Prékopa–Leindler for `γ`.* Multiplying by the Gaussian density turns the Prékopa–Leindler
   inequality for Lebesgue measure (`MathlibExt.MeasureTheory.Integral.PrekopaLeindler`) into:
   if `u(x)^(1-t) v(y)^t exp (-t (1-t) ‖x - y‖² / 2) ≤ w((1-t) x + t y)` for all `x, y`, then
   `(∫ u dγ)^(1-t) (∫ v dγ)^t ≤ ∫ w dγ`. An orthonormal basis reduces `E` to `ℝⁿ`.
2. *Functions that are constant outside a compact set.* Let `F ≥ δ > 0` be `C²` with `F = δ`
   outside a compact set. Then `g = log F` satisfies
   `g(y) ≤ g(z) + ‖Dg(z)‖ ‖y - z‖ + M ‖y - z‖²`. For small `ε > 0`, step 1 with `t = 1 / (1 + ε)`,
   `u = 1`, `v = F^(1+ε)` and `w = F exp (ε ‖Dg‖² / (2 (1 - 2εM)))` gives
   `(∫ F^(1+ε) dγ)^(1/(1+ε)) ≤ ∫ w dγ`. The bounds `F^(1+ε) ≥ F + ε F log F` and
   `e^s ≤ 1 + s e^s` expand both sides to first order in `ε`, and letting `ε → 0` gives
   `∫ F log F dγ - (∫ F dγ) log (∫ F dγ) ≤ ½ ∫ ‖DF‖² / F dγ`.
3. *Cutoff.* For a general `f`, step 2 applies to `F_n = s_n + χ_n² f` with `s_n = 1 / (n + 1)`
   and `χ_n(x) = ψ(s_n x)`, where `ψ` is a smooth bump equal to `1` on the unit ball. The
   pointwise bound `‖DF_n‖² / F_n ≤ (1 + s_n) ‖Df‖² / f + 4 c² (s_n² + s_n) f`, where `c`
   bounds `‖Dψ‖`, controls the right-hand side; `∫ F_n dγ → 1` by dominated convergence; and
   Fatou's lemma for `klFun (F_n) → klFun f`, with `klFun x = x log x + 1 - x`, gives
   `∫ klFun f dγ ≤ ½ ∫ ‖Df‖² / f dγ` in `[0, ∞]`.
4. Mathlib's `klDiv_eq_lintegral_klFun_of_ac` identifies `KL(f γ ‖ γ)` with `∫ klFun f dγ`.

## Main results

* `klDiv_withDensity_stdGaussian_le`: Gross' inequality `KL(f γ ‖ γ) ≤ ½ ∫ ‖Df‖² / f dγ`.

## Implementation notes

The theorem keeps the full name it had in the former wanted module, so its namespace still reads
`GaussianLogSobolevWanted`. The norm of `fderiv ℝ f x` is the operator norm of the derivative,
which equals the norm of the gradient of `f` at `x`.

## References

* L. Gross, Logarithmic Sobolev inequalities, *Amer. J. Math.* 97 (1975), 1061–1083.
* M. Ledoux, Heat flows, geometric and functional inequalities, *Proceedings of the
  International Congress of Mathematicians, Seoul 2014*, Theorem 2.1.
* S. G. Bobkov and M. Ledoux, From Brunn–Minkowski to Brascamp–Lieb and to logarithmic Sobolev
  inequalities, *Geom. Funct. Anal.* 10 (2000), 1028–1052, Proposition 3.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology
open scoped ENNReal ContDiff

namespace MathlibExt.Probability.GaussianLogSobolevWanted

section Auxiliary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Prékopa–Leindler for the standard Gaussian measure -/

/-- **Squared norm of an affine combination.** In a real inner product space, for any real $t$,
$$(1-t)\|x\|^2 + t\|y\|^2 = \|(1-t)x+ty\|^2 + t(1-t)\|x-y\|^2.$$

Source: The real inner product expansions `norm_add_sq_real` and `norm_sub_sq_real`. -/
lemma convex_comb_norm_sq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (t : ℝ) (x y : F) :
    (1 - t) * ‖x‖ ^ 2 + t * ‖y‖ ^ 2 =
      ‖(1 - t) • x + t • y‖ ^ 2 + t * (1 - t) * ‖x - y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  ring

/-- **Interpolation identity for the standard Gaussian density.** For the standard Gaussian
density $p$ on $\mathbb R^n$, all $x,y\in\mathbb R^n$ and every real $t$,
$$p(x)^{1-t}p(y)^t = p((1-t)x+ty)\exp(-t(1-t)\|x-y\|^2/2).$$

Source: The formula for `stdGaussianPDFReal` and the squared norm of an affine combination. -/
lemma stdGaussianPDFReal_rpow_mul_rpow {n : ℕ} (t : ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    MetaMathlibExt.stdGaussianPDFReal x ^ (1 - t) * MetaMathlibExt.stdGaussianPDFReal y ^ t =
      MetaMathlibExt.stdGaussianPDFReal ((1 - t) • x + t • y) *
        Real.exp (-(t * (1 - t) * ‖x - y‖ ^ 2 / 2)) := by
  simp only [MetaMathlibExt.stdGaussianPDFReal]
  set c : ℝ := ((√(2 * Real.pi)) ^ Fintype.card (Fin n))⁻¹
  have hc : 0 < c := by positivity
  rw [Real.mul_rpow hc.le (Real.exp_pos _).le, Real.mul_rpow hc.le (Real.exp_pos _).le,
    ← Real.exp_mul, ← Real.exp_mul]
  have hcc : c ^ (1 - t) * c ^ t = c := by
    rw [← Real.rpow_add hc, sub_add_cancel, Real.rpow_one]
  have key := convex_comb_norm_sq t x y
  calc c ^ (1 - t) * Real.exp (-‖x‖ ^ 2 / 2 * (1 - t)) * (c ^ t * Real.exp (-‖y‖ ^ 2 / 2 * t))
      = (c ^ (1 - t) * c ^ t) * Real.exp (-‖x‖ ^ 2 / 2 * (1 - t) + -‖y‖ ^ 2 / 2 * t) := by
        rw [Real.exp_add]; ring
    _ = c * Real.exp (-‖(1 - t) • x + t • y‖ ^ 2 / 2 + -(t * (1 - t) * ‖x - y‖ ^ 2 / 2)) := by
        rw [hcc]; congr 2; linear_combination (-1 / 2 : ℝ) * key
    _ = _ := by rw [Real.exp_add]; ring

/-- **Prékopa–Leindler inequality for the standard Gaussian on Euclidean space.** Let $\gamma$
be the standard Gaussian on $\mathbb R^n$, let $0<t<1$, and let $u,v,w$ be Borel measurable
functions with values in $[0,\infty]$. If for all $x,y$,
$$u(x)^{1-t}v(y)^t\exp(-t(1-t)\|x-y\|^2/2)\le w((1-t)x+ty),$$
then $(\int u\,d\gamma)^{1-t}(\int v\,d\gamma)^t\le \int w\,d\gamma$.

Source: The Lebesgue Prékopa–Leindler inequality (`prekopa_leindler`) applied after
multiplication by the standard Gaussian density. -/
lemma lintegral_rpow_mul_le_stdGaussian_euclidean {n : ℕ} {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) {u v w : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hu : Measurable u)
    (hv : Measurable v) (hw : Measurable w)
    (huvw : ∀ x y, u x ^ (1 - t) * v y ^ t *
      ENNReal.ofReal (Real.exp (-(t * (1 - t) * ‖x - y‖ ^ 2 / 2))) ≤ w ((1 - t) • x + t • y)) :
    (∫⁻ x, u x ∂stdGaussian _) ^ (1 - t) * (∫⁻ x, v x ∂stdGaussian _) ^ t ≤
      ∫⁻ x, w x ∂stdGaussian _ := by
  set p : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (MetaMathlibExt.stdGaussianPDFReal x) with hp_def
  have hp : Measurable p := ENNReal.measurable_ofReal.comp
    MetaMathlibExt.measurable_stdGaussianPDFReal
  rw [MetaMathlibExt.stdGaussian_eq_withDensity, lintegral_withDensity_eq_lintegral_mul _ hp hu,
    lintegral_withDensity_eq_lintegral_mul _ hp hv, lintegral_withDensity_eq_lintegral_mul _ hp hw]
  refine MathlibExt.MeasureTheory.Integral.PrekopaLeindlerWanted.prekopa_leindler ht0 ht1
    (hp.mul hu) (hp.mul hv) (hp.mul hw) fun x y => ?_
  have h1t : 0 ≤ 1 - t := by linarith
  have hpp : p x ^ (1 - t) * p y ^ t = p ((1 - t) • x + t • y) *
      ENNReal.ofReal (Real.exp (-(t * (1 - t) * ‖x - y‖ ^ 2 / 2))) := by
    simp only [hp_def]
    rw [ENNReal.ofReal_rpow_of_nonneg (MetaMathlibExt.stdGaussianPDFReal_nonneg _) h1t,
      ENNReal.ofReal_rpow_of_nonneg (MetaMathlibExt.stdGaussianPDFReal_nonneg _) ht0.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (MetaMathlibExt.stdGaussianPDFReal_nonneg _) _),
      ← ENNReal.ofReal_mul (MetaMathlibExt.stdGaussianPDFReal_nonneg _),
      stdGaussianPDFReal_rpow_mul_rpow]
  change (p x * u x) ^ (1 - t) * (p y * v y) ^ t ≤ p ((1 - t) • x + t • y) * w ((1 - t) • x + t • y)
  rw [ENNReal.mul_rpow_of_nonneg _ _ h1t, ENNReal.mul_rpow_of_nonneg _ _ ht0.le]
  calc p x ^ (1 - t) * u x ^ (1 - t) * (p y ^ t * v y ^ t)
      = (p x ^ (1 - t) * p y ^ t) * (u x ^ (1 - t) * v y ^ t) := by ring
    _ = p ((1 - t) • x + t • y) * (u x ^ (1 - t) * v y ^ t *
          ENNReal.ofReal (Real.exp (-(t * (1 - t) * ‖x - y‖ ^ 2 / 2)))) := by
        rw [hpp]; ring
    _ ≤ _ := by gcongr; exact huvw x y

/-! ### A second-order Taylor bound -/

/-- A `C²` function with compact support satisfies
`G y ≤ G z + DG(z) (y - z) + M ‖y - z‖²` for some `M ≥ 0` and all `y, z`. -/
private lemma exists_le_add_fderiv_add_mul_norm_sq {G : E → ℝ} (hG : ContDiff ℝ 2 G)
    (hGc : HasCompactSupport G) :
    ∃ M, 0 ≤ M ∧ ∀ y z, G y ≤ G z + fderiv ℝ G z (y - z) + M * ‖y - z‖ ^ 2 := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hGc.fderiv ℝ)
    (hG.fderiv_right (m := 1) (by norm_num)) (by norm_num)
  refine ⟨K, K.2, fun y z => ?_⟩
  have hdiff : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hb := (convex_closedBall z ‖y - z‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun w => G w - fderiv ℝ G z w) (f' := fun w => fderiv ℝ G w - fderiv ℝ G z)
    (C := K * ‖y - z‖) (x := z) (y := y)
    (fun w _ => ((hdiff w).hasFDerivAt.sub (fderiv ℝ G z).hasFDerivAt).hasFDerivWithinAt)
    (fun w hw => (hK.norm_sub_le w z).trans (by
      gcongr
      simpa [dist_eq_norm] using hw))
    (Metric.mem_closedBall_self (norm_nonneg _)) (by simp [dist_eq_norm])
  have h2 := (le_abs_self _).trans (Real.norm_eq_abs _ ▸ hb)
  have hsq : ‖y - z‖ ^ 2 = ‖y - z‖ * ‖y - z‖ := sq _
  rw [map_sub, hsq]
  linarith

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Prékopa–Leindler inequality for the standard Gaussian measure.** Let $\gamma$ be the
standard Gaussian on a finite-dimensional real inner product space, let $0<t<1$, and let $u,v,w$
be Borel measurable functions with values in $[0,\infty]$. If for all $x,y$,
$$u(x)^{1-t}v(y)^t\exp(-t(1-t)\|x-y\|^2/2)\le w((1-t)x+ty),$$
then $(\int u\,d\gamma)^{1-t}(\int v\,d\gamma)^t\le \int w\,d\gamma$.

Source: The Euclidean Gaussian Prékopa–Leindler inequality in orthonormal coordinates, using
invariance of the standard Gaussian under linear isometries (`stdGaussian_map`). -/
lemma lintegral_rpow_mul_le_stdGaussian {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {u v w : E → ℝ≥0∞} (hu : Measurable u) (hv : Measurable v) (hw : Measurable w)
    (huvw : ∀ x y, u x ^ (1 - t) * v y ^ t *
      ENNReal.ofReal (Real.exp (-(t * (1 - t) * ‖x - y‖ ^ 2 / 2))) ≤ w ((1 - t) • x + t • y)) :
    (∫⁻ x, u x ∂stdGaussian E) ^ (1 - t) * (∫⁻ x, v x ∂stdGaussian E) ^ t ≤
      ∫⁻ x, w x ∂stdGaussian E := by
  let T := (stdOrthonormalBasis ℝ E).repr
  have hT : MeasurePreserving T (stdGaussian E)
      (stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) :=
    ⟨T.continuous.measurable, stdGaussian_map T⟩
  have hTs : Measurable T.symm := T.symm.continuous.measurable
  have key : ∀ g : E → ℝ≥0∞, Measurable g →
      ∫⁻ x, g x ∂stdGaussian E = ∫⁻ y, g (T.symm y) ∂stdGaussian _ := by
    intro g hg
    rw [← hT.lintegral_comp (f := fun y => g (T.symm y)) (hg.comp hTs)]
    simp only [LinearIsometryEquiv.symm_apply_apply]
  rw [key u hu, key v hv, key w hw]
  refine lintegral_rpow_mul_le_stdGaussian_euclidean ht0 ht1 (hu.comp hTs) (hv.comp hTs)
    (hw.comp hTs) fun x y => ?_
  have e1 : T.symm ((1 - t) • x + t • y) = (1 - t) • T.symm x + t • T.symm y := by
    rw [map_add, map_smul, map_smul]
  have e2 : ‖T.symm x - T.symm y‖ = ‖x - y‖ := by
    rw [← map_sub, LinearIsometryEquiv.norm_map]
  have h := huvw (T.symm x) (T.symm y)
  rw [e2, ← e1] at h
  simpa only [Function.comp_apply] using h

/-! ### Elementary inequalities -/

/-- `a r + M r² - r² / (2ε) ≤ ε a² / (2 (1 - 2εM))` when `0 < ε` and `2εM < 1`. -/
private lemma mul_add_mul_sq_sub_div_le {ε M a r : ℝ} (hε : 0 < ε) (hεM : 2 * ε * M < 1) :
    a * r + M * r ^ 2 - r ^ 2 / (2 * ε) ≤ ε * a ^ 2 / (2 * (1 - 2 * ε * M)) := by
  set d := 1 - 2 * ε * M with hd
  have h1 : 0 < d := by linarith
  have key : ε * a ^ 2 / (2 * d) - (a * r + M * r ^ 2 - r ^ 2 / (2 * ε)) =
      (d * r - ε * a) ^ 2 / (2 * ε * d) := by
    field_simp
    rw [hd]
    ring
  have : 0 ≤ (d * r - ε * a) ^ 2 / (2 * ε * d) := by positivity
  linarith

/-- `exp s ≤ 1 + s exp s`. -/
private lemma exp_le_one_add_mul_exp (s : ℝ) : Real.exp s ≤ 1 + s * Real.exp s := by
  have h := Real.add_one_le_exp (-s)
  have h2 : Real.exp (-s) * Real.exp s = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  nlinarith [Real.exp_pos s]

/-! ### The inequality for functions that are constant outside a compact set -/

/-- A continuous bounded function is integrable for the standard Gaussian. -/
private lemma integrable_stdGaussian_of_abs_le {φ : E → ℝ} (hφ : Continuous φ) (C : ℝ)
    (hC : ∀ x, |φ x| ≤ C) : Integrable φ (stdGaussian E) :=
  Integrable.of_bound hφ.aestronglyMeasurable C
    (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (hC x))

/-- **The Prékopa–Leindler step.** Let `F ≥ δ > 0` be continuous and bounded by `K`, with
`|log F| ≤ L`, and let `0 ≤ a ≤ A` be continuous with
`log F(y) ≤ log F(z) + a(z) ‖y - z‖ + M ‖y - z‖²` for all `y, z`. Write `Z = ∫ F dγ`,
`W = ∫ F log F dγ` and `B = ½ ∫ F a² dγ`. For `0 < ε` with `2εM < 1` and `εL < 1`,
Prékopa–Leindler with weights `ε / (1 + ε)` and `1 / (1 + ε)`, applied to `1`, `F^(1+ε)` and
`F exp (ε a² / (2 (1 - 2εM)))`, gives
`W / (Z + εW) ≤ log Z + (1 + ε) exp (εA² / (2 (1 - 2εM))) / (1 - 2εM) · B / Z`. -/
private lemma div_add_mul_le_log_add_of_prekopaLeindler {F a : E → ℝ} {δ K L A M ε : ℝ}
    (hFc : Continuous F) (hac : Continuous a) (hδ : 0 < δ) (hFδ : ∀ x, δ ≤ F x)
    (hFle : ∀ x, F x ≤ K) (hlog : ∀ x, |Real.log (F x)| ≤ L) (ha0 : ∀ x, 0 ≤ a x)
    (haA : ∀ x, a x ≤ A)
    (htay : ∀ y z, Real.log (F y) ≤ Real.log (F z) + a z * ‖y - z‖ + M * ‖y - z‖ ^ 2)
    (hε : 0 < ε) (h2εM : 2 * ε * M < 1) (hεL : ε * L < 1) :
    (∫ x, F x * Real.log (F x) ∂stdGaussian E) /
        (∫ x, F x ∂stdGaussian E + ε * ∫ x, F x * Real.log (F x) ∂stdGaussian E) ≤
      Real.log (∫ x, F x ∂stdGaussian E) +
        (1 + ε) * (Real.exp (ε * A ^ 2 / (2 * (1 - 2 * ε * M))) / (1 - 2 * ε * M)) *
          (1 / 2 * ∫ x, F x * a x ^ 2 ∂stdGaussian E) / ∫ x, F x ∂stdGaussian E := by
  have hFpos : ∀ x, 0 < F x := fun x => hδ.trans_le (hFδ x)
  have hK : 0 ≤ K := (hFpos 0).le.trans (hFle 0)
  have hcl : Continuous fun x => Real.log (F x) := hFc.log fun x => (hFpos x).ne'
  have hiF : Integrable F (stdGaussian E) :=
    integrable_stdGaussian_of_abs_le hFc K fun x => by
      rw [abs_of_pos (hFpos x)]; exact hFle x
  have hiFl : Integrable (fun x => F x * Real.log (F x)) (stdGaussian E) :=
    integrable_stdGaussian_of_abs_le (hFc.mul hcl) (K * L) fun x => by
      rw [abs_mul, abs_of_pos (hFpos x)]
      exact mul_le_mul (hFle x) (hlog x) (abs_nonneg _) hK
  have hiFa : Integrable (fun x => F x * a x ^ 2) (stdGaussian E) :=
    integrable_stdGaussian_of_abs_le (hFc.mul (hac.pow 2)) (K * A ^ 2) fun x => by
      rw [abs_mul, abs_of_pos (hFpos x), abs_of_nonneg (by positivity)]
      exact mul_le_mul (hFle x) (pow_le_pow_left₀ (ha0 x) (haA x) 2) (by positivity) hK
  set Z := ∫ x, F x ∂stdGaussian E with hZ
  set W := ∫ x, F x * Real.log (F x) ∂stdGaussian E with hW
  set B := 1 / 2 * ∫ x, F x * a x ^ 2 ∂stdGaussian E with hB
  have hZpos : 0 < Z := by
    have := integral_mono (integrable_const δ) hiF hFδ
    rw [integral_const, probReal_univ, one_smul] at this
    exact hδ.trans_le this
  have hWlow : -L * Z ≤ W := by
    rw [hZ, hW, ← integral_const_mul]
    refine integral_mono (hiF.const_mul _) hiFl fun x => ?_
    have := (abs_le.mp (hlog x)).1
    nlinarith [hFpos x]
  have hB0 : 0 ≤ B :=
    mul_nonneg (by norm_num) (integral_nonneg fun x => mul_nonneg (hFpos x).le (by positivity))
  have hden : 0 < 1 - 2 * ε * M := by linarith
  set t := 1 / (1 + ε) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := by rw [ht, div_lt_one (by linarith)]; linarith
  have htε : (1 + ε) * t = 1 := by rw [ht]; field_simp
  have h1t : 1 - t = ε * t := by rw [ht]; field_simp; ring
  set S := ε * A ^ 2 / (2 * (1 - 2 * ε * M)) with hS
  set c := Real.exp S / (1 - 2 * ε * M) with hc
  have hc0 : 0 < c := by positivity
  have hcv : Continuous fun y => Real.exp ((1 + ε) * Real.log (F y)) :=
    Real.continuous_exp.comp (continuous_const.mul hcl)
  have hcw : Continuous fun z =>
      F z * Real.exp (ε * a z ^ 2 / (2 * (1 - 2 * ε * M))) :=
    hFc.mul (Real.continuous_exp.comp ((continuous_const.mul (hac.pow 2)).div_const _))
  have hiv : Integrable (fun y => Real.exp ((1 + ε) * Real.log (F y))) (stdGaussian E) :=
    integrable_stdGaussian_of_abs_le hcv (Real.exp ((1 + ε) * L)) fun y => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (by nlinarith [(abs_le.mp (hlog y)).2])
  have hsS : ∀ z, ε * a z ^ 2 / (2 * (1 - 2 * ε * M)) ≤ S := fun z => by
    rw [hS]
    gcongr
    · exact ha0 z
    · exact haA z
  have hiw : Integrable (fun z =>
      F z * Real.exp (ε * a z ^ 2 / (2 * (1 - 2 * ε * M)))) (stdGaussian E) :=
    integrable_stdGaussian_of_abs_le hcw (K * Real.exp S) fun z => by
      rw [abs_of_pos (mul_pos (hFpos z) (Real.exp_pos _))]
      exact mul_le_mul (hFle z) (Real.exp_le_exp.mpr (hsS z)) (Real.exp_pos _).le hK
  -- The hypothesis of Prékopa–Leindler.
  have hyp : ∀ x y : E, (fun _ : E => (1 : ℝ≥0∞)) x ^ (1 - t) *
      (fun y => ENNReal.ofReal (Real.exp ((1 + ε) * Real.log (F y)))) y ^ t *
      ENNReal.ofReal (Real.exp (-(t * (1 - t) * ‖x - y‖ ^ 2 / 2))) ≤
      (fun z => ENNReal.ofReal
        (F z * Real.exp (ε * a z ^ 2 / (2 * (1 - 2 * ε * M))))) ((1 - t) • x + t • y) := by
    intro x y
    set z := (1 - t) • x + t • y with hz
    simp only [ENNReal.one_rpow, one_mul]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le ht0.le, ← Real.exp_mul,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.exp_add, ← Real.exp_log (hFpos z), ← Real.exp_add, Real.exp_le_exp]
    have hyz : y - z = (1 - t) • (y - x) := by rw [hz]; module
    have hr : ‖y - z‖ = ε * t * ‖x - y‖ := by
      rw [hyz, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), h1t, norm_sub_rev]
    have hq := mul_add_mul_sq_sub_div_le (a := a z) (r := ‖y - z‖) hε h2εM
    have e1 : (1 + ε) * Real.log (F y) * t = Real.log (F y) := by
      rw [mul_right_comm, htε, one_mul]
    have e2 : ‖y - z‖ ^ 2 / (2 * ε) = t * (1 - t) * ‖x - y‖ ^ 2 / 2 := by
      rw [hr, h1t]; field_simp
    rw [e1]
    linarith [htay y z]
  have hpl := lintegral_rpow_mul_le_stdGaussian ht0 ht1 measurable_const
    (ENNReal.measurable_ofReal.comp hcv.measurable)
    (ENNReal.measurable_ofReal.comp hcw.measurable) hyp
  simp only [lintegral_const, measure_univ, one_mul, ENNReal.one_rpow, Function.comp_apply] at hpl
  rw [← ofReal_integral_eq_lintegral_ofReal hiv (ae_of_all _ fun _ => (Real.exp_pos _).le),
    ← ofReal_integral_eq_lintegral_ofReal hiw
      (ae_of_all _ fun z => (mul_pos (hFpos z) (Real.exp_pos _)).le),
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun _ => (Real.exp_pos _).le) ht0.le,
    ENNReal.ofReal_le_ofReal_iff
      (integral_nonneg fun z => (mul_pos (hFpos z) (Real.exp_pos _)).le)] at hpl
  -- Lower bound: `exp ((1 + ε) log F) ≥ F (1 + ε log F)`.
  have hlow : Z + ε * W ≤ ∫ y, Real.exp ((1 + ε) * Real.log (F y)) ∂stdGaussian E := by
    rw [hZ, hW, ← integral_const_mul, ← integral_add hiF (hiFl.const_mul ε)]
    refine integral_mono (hiF.add (hiFl.const_mul ε)) hiv fun y => ?_
    have h1 := Real.add_one_le_exp (ε * Real.log (F y))
    have e : Real.exp ((1 + ε) * Real.log (F y)) = F y * Real.exp (ε * Real.log (F y)) := by
      rw [add_mul, one_mul, Real.exp_add, Real.exp_log (hFpos y)]
    simp only
    rw [e]
    nlinarith [hFpos y]
  -- Upper bound: `F exp s ≤ F (1 + s exp S)`.
  have hup : ∫ z, F z * Real.exp (ε * a z ^ 2 / (2 * (1 - 2 * ε * M)))
      ∂stdGaussian E ≤ Z + ε * c * B := by
    have e : Z + ε * c * B = ∫ z, (F z + ε * Real.exp S / (2 * (1 - 2 * ε * M)) *
        (F z * a z ^ 2)) ∂stdGaussian E := by
      rw [integral_add hiF (hiFa.const_mul _), integral_const_mul, hB, hc, hZ]
      field_simp
    rw [e]
    refine integral_mono hiw (hiF.add (hiFa.const_mul _)) fun z => ?_
    simp only
    have hs0 : 0 ≤ ε * a z ^ 2 / (2 * (1 - 2 * ε * M)) := by positivity
    have h1 := exp_le_one_add_mul_exp (ε * a z ^ 2 / (2 * (1 - 2 * ε * M)))
    have h2 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hsS z)) hs0
    have e3 : ε * a z ^ 2 / (2 * (1 - 2 * ε * M)) * Real.exp S * F z =
        ε * Real.exp S / (2 * (1 - 2 * ε * M)) * (F z * a z ^ 2) := by
      field_simp
    nlinarith [hFpos z]
  -- Combine and take logarithms.
  have hZεW : 0 < Z + ε * W := by nlinarith
  have hpos : 0 < Z + ε * c * B := by
    have : 0 ≤ ε * c * B := mul_nonneg (mul_nonneg hε.le hc0.le) hB0
    linarith
  have hchain : (Z + ε * W) ^ t ≤ Z + ε * c * B :=
    (Real.rpow_le_rpow hZεW.le hlow ht0.le).trans (hpl.trans hup)
  have hlog1 : t * Real.log (Z + ε * W) ≤ Real.log Z + ε * c * B / Z := by
    rw [← Real.log_rpow hZεW]
    refine (Real.log_le_log (Real.rpow_pos_of_pos hZεW _) hchain).trans ?_
    have h1 := Real.log_le_sub_one_of_pos (div_pos hpos hZpos)
    rw [Real.log_div hpos.ne' hZpos.ne'] at h1
    have e : (Z + ε * c * B) / Z - 1 = ε * c * B / Z := by field_simp; ring
    linarith
  have hlog2 : Real.log Z + ε * W / (Z + ε * W) ≤ Real.log (Z + ε * W) := by
    have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hZεW hZpos)
    rw [Real.log_div hZεW.ne' hZpos.ne', inv_div] at h1
    have e : 1 - Z / (Z + ε * W) = ε * W / (Z + ε * W) := by field_simp; ring
    linarith
  have h3 : t * (Real.log Z + ε * W / (Z + ε * W)) ≤ Real.log Z + ε * c * B / Z :=
    (mul_le_mul_of_nonneg_left hlog2 ht0.le).trans hlog1
  have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 1 + ε)
  rw [← mul_assoc, htε, one_mul] at h4
  have h5 : ε * (W / (Z + ε * W)) ≤ ε * (Real.log Z + (1 + ε) * c * B / Z) := by
    have e1 : ε * W / (Z + ε * W) = ε * (W / (Z + ε * W)) := by ring
    have e2 : (1 + ε) * (Real.log Z + ε * c * B / Z) =
        Real.log Z + ε * (Real.log Z + (1 + ε) * c * B / Z) := by ring
    linarith
  exact le_of_mul_le_mul_left h5 hε

/-- The Bobkov–Ledoux argument: Gross' inequality, in the form
`∫ klFun F dγ ≤ klFun (∫ F dγ) + ½ ∫ ‖DF‖² / F dγ`, for a `C²` function `F ≥ δ > 0` that equals
`δ` outside a compact set. -/
private lemma lintegral_klFun_le_of_hasCompactSupport_sub {F : E → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hF : ContDiff ℝ 2 F) (hFδ : ∀ x, δ ≤ F x) (hFc : HasCompactSupport fun x => F x - δ) :
    ∫⁻ x, ENNReal.ofReal (klFun (F x)) ∂stdGaussian E ≤
      ENNReal.ofReal (klFun (∫ x, F x ∂stdGaussian E) +
        1 / 2 * ∫ x, ‖fderiv ℝ F x‖ ^ 2 / F x ∂stdGaussian E) := by
  have hFpos : ∀ x, 0 < F x := fun x => hδ.trans_le (hFδ x)
  have hFne : ∀ x, F x ≠ 0 := fun x => (hFpos x).ne'
  have hFcont : Continuous F := hF.continuous
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  -- `G = log F - log δ` is `C²` with compact support, and `DG = DF / F`.
  set G : E → ℝ := fun x => Real.log (F x) - Real.log δ with hG_def
  have hGx : ∀ x, G x = Real.log (F x) - Real.log δ := fun x => rfl
  have hG : ContDiff ℝ 2 G := (hF.log hFne).sub contDiff_const
  have hGc : HasCompactSupport G := hFc.mono fun x hx h => hx (by
    have : F x = δ := by linarith [sub_eq_zero.mp h]
    simp [hGx, this])
  have hDG : ∀ x, fderiv ℝ G x = (F x)⁻¹ • fderiv ℝ F x := fun x =>
    (((hFd x).hasFDerivAt.log (hFne x)).sub_const _).fderiv
  -- Bounds.
  obtain ⟨K₀, hK₀⟩ := (hFcont.sub continuous_const).bounded_above_of_compact_support hFc
  have hFle : ∀ x, F x ≤ δ + K₀ := fun x => by
    have : |F x - δ| ≤ K₀ := by rw [← Real.norm_eq_abs]; exact hK₀ x
    linarith [le_abs_self (F x - δ)]
  have hK : 0 ≤ δ + K₀ := (hFpos 0).le.trans (hFle 0)
  obtain ⟨L₀, hL₀⟩ := hG.continuous.bounded_above_of_compact_support hGc
  have hlog : ∀ x, |Real.log (F x)| ≤ L₀ + |Real.log δ| := fun x => by
    have h1 : |G x| ≤ L₀ := by rw [← Real.norm_eq_abs]; exact hL₀ x
    have : Real.log (F x) = G x + Real.log δ := by rw [hGx]; ring
    rw [this]
    exact (abs_add_le _ _).trans (by linarith)
  set L := L₀ + |Real.log δ| with hL_def
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hlog 0)
  have hcDG : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by norm_num)
  obtain ⟨A, hA⟩ := hcDG.bounded_above_of_compact_support (hGc.fderiv ℝ)
  obtain ⟨M, hM0, hM⟩ := exists_le_add_fderiv_add_mul_norm_sq hG hGc
  have htay : ∀ y z, Real.log (F y) ≤
      Real.log (F z) + ‖fderiv ℝ G z‖ * ‖y - z‖ + M * ‖y - z‖ ^ 2 := by
    intro y z
    have h1 := hM y z
    have h2 : fderiv ℝ G z (y - z) ≤ ‖fderiv ℝ G z‖ * ‖y - z‖ :=
      (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact (fderiv ℝ G z).le_opNorm _)
    linarith [hGx y, hGx z]
  -- Integrability.
  have hcl : Continuous fun x => Real.log (F x) := hFcont.log hFne
  have hiF : Integrable F (stdGaussian E) :=
    integrable_stdGaussian_of_abs_le hFcont (δ + K₀) fun x => by
      rw [abs_of_pos (hFpos x)]; exact hFle x
  have hiFl : Integrable (fun x => F x * Real.log (F x)) (stdGaussian E) :=
    integrable_stdGaussian_of_abs_le (hFcont.mul hcl) ((δ + K₀) * L) fun x => by
      rw [abs_mul, abs_of_pos (hFpos x)]
      exact mul_le_mul (hFle x) (hlog x) (abs_nonneg _) hK
  set Z := ∫ x, F x ∂stdGaussian E with hZ
  set W := ∫ x, F x * Real.log (F x) ∂stdGaussian E with hW
  set B := 1 / 2 * ∫ x, F x * ‖fderiv ℝ G x‖ ^ 2 ∂stdGaussian E with hB
  have hZδ : δ ≤ Z := by
    have := integral_mono (integrable_const δ) hiF hFδ
    rwa [integral_const, probReal_univ, one_smul] at this
  have hZpos : 0 < Z := hδ.trans_le hZδ
  -- The inequality from Prékopa–Leindler, for small `ε > 0`.
  set ε₀ := 1 / (2 * M + L + 1) with hε₀_def
  have hε₀ : 0 < ε₀ := by positivity
  have key : ∀ ε, 0 < ε → ε < ε₀ → W / (Z + ε * W) ≤ Real.log Z +
      (1 + ε) * (Real.exp (ε * A ^ 2 / (2 * (1 - 2 * ε * M))) / (1 - 2 * ε * M)) * B / Z := by
    intro ε hε hεε₀
    have hε1 : ε * (2 * M + L + 1) < 1 := by
      rwa [hε₀_def, lt_div_iff₀ (by positivity)] at hεε₀
    exact div_add_mul_le_log_add_of_prekopaLeindler hFcont hcDG.norm hδ hFδ hFle hlog
      (fun _ => norm_nonneg _) hA htay hε (by nlinarith) (by nlinarith)
  -- Let `ε → 0`.
  have hlim : W / Z ≤ Real.log Z + B / Z := by
    have hf1 : Tendsto (fun ε => W / (Z + ε * W)) (𝓝[>] 0) (𝓝 (W / Z)) := by
      have : ContinuousAt (fun ε : ℝ => W / (Z + ε * W)) 0 :=
        continuousAt_const.div (by fun_prop) (by simp [hZpos.ne'])
      simpa using this.tendsto.mono_left nhdsWithin_le_nhds
    have hf2 : Tendsto (fun ε => Real.log Z + (1 + ε) *
        (Real.exp (ε * A ^ 2 / (2 * (1 - 2 * ε * M))) / (1 - 2 * ε * M)) * B / Z) (𝓝[>] 0)
        (𝓝 (Real.log Z + B / Z)) := by
      have : ContinuousAt (fun ε : ℝ => Real.log Z + (1 + ε) *
          (Real.exp (ε * A ^ 2 / (2 * (1 - 2 * ε * M))) / (1 - 2 * ε * M)) * B / Z) 0 := by
        fun_prop (disch := norm_num)
      simpa using this.tendsto.mono_left nhdsWithin_le_nhds
    exact le_of_tendsto_of_tendsto hf1 hf2
      (by filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε using key ε hε.1 hε.2)
  have hWle : W ≤ Z * Real.log Z + B := by
    rw [div_le_iff₀ hZpos, add_mul, div_mul_cancel₀ _ hZpos.ne'] at hlim
    linarith
  -- Back to `klFun`.
  have hik : Integrable (fun x => klFun (F x)) (stdGaussian E) :=
    ((hiFl.add (integrable_const 1)).sub hiF).congr (ae_of_all _ fun x => by simp [klFun_apply])
  rw [← ofReal_integral_eq_lintegral_ofReal hik (ae_of_all _ fun x => klFun_nonneg (hFpos x).le)]
  apply ENNReal.ofReal_le_ofReal
  have hk : ∫ x, klFun (F x) ∂stdGaussian E = W + 1 - Z := by
    simp only [klFun_apply]
    rw [integral_sub (f := fun x => F x * Real.log (F x) + 1) (hiFl.add (integrable_const 1)) hiF,
      integral_add hiFl (integrable_const 1), integral_const, probReal_univ, one_smul]
  have hrhs : ∫ x, ‖fderiv ℝ F x‖ ^ 2 / F x ∂stdGaussian E =
      ∫ x, F x * ‖fderiv ℝ G x‖ ^ 2 ∂stdGaussian E := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [hDG x, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hFpos x)]
    field_simp [(hFpos x).ne']
  rw [hk, hrhs, klFun_apply]
  linarith

/-! ### Removing the compact support by a cutoff -/

/-- The pointwise estimate behind the cutoff. If `0 ≤ φ ≤ 1`, `0 < f`, `0 < s`, `0 ≤ D' ≤ c s`
and `0 ≤ N ≤ φ² D + f (2 φ D')`, then
`N² / (s + φ² f) ≤ (1 + s) D² / f + 4 c² (s² + s) f`. -/
private lemma sq_div_add_le {φ f s D D' N c : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hf : 0 < f)
    (hs : 0 < s) (hD'0 : 0 ≤ D') (hD' : D' ≤ c * s) (hN0 : 0 ≤ N)
    (hN : N ≤ φ ^ 2 * D + f * (2 * φ * D')) :
    N ^ 2 / (s + φ ^ 2 * f) ≤ (1 + s) * (D ^ 2 / f) + 4 * c ^ 2 * (s ^ 2 + s) * f := by
  have hP : 0 < s + φ ^ 2 * f := by positivity
  set β := φ ^ 2 * D with hβ
  set α := f * (2 * φ * D') with hα
  have hφ2 : φ ^ 2 ≤ 1 := pow_le_one₀ hφ0 hφ1
  have hb : β ^ 2 / (s + φ ^ 2 * f) ≤ D ^ 2 / f := by
    rw [div_le_div_iff₀ hP hf, hβ]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg D) hf.le)
      (mul_nonneg (sq_nonneg φ) (sub_nonneg.mpr hφ2)), mul_nonneg (sq_nonneg D) hs.le]
  have ha : α ^ 2 / (s + φ ^ 2 * f) ≤ 4 * f * D' ^ 2 := by
    rw [div_le_iff₀ hP, hα]
    nlinarith [mul_nonneg (mul_nonneg hf.le (sq_nonneg D')) hs.le]
  have hsq : N ^ 2 ≤ (1 + s) * β ^ 2 + (α ^ 2 + α ^ 2 / s) := by
    have h1 : N ^ 2 ≤ (β + α) ^ 2 := pow_le_pow_left₀ hN0 hN 2
    have h2 : 0 ≤ (s * β - α) ^ 2 / s := by positivity
    have e : (s * β - α) ^ 2 / s = s * β ^ 2 + α ^ 2 / s - 2 * α * β := by
      field_simp
      ring
    nlinarith
  have hD'2 : D' ^ 2 ≤ c ^ 2 * s ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hD'0 hD' 2
  have e2 : (α ^ 2 + α ^ 2 / s) / (s + φ ^ 2 * f) = (1 + 1 / s) * (α ^ 2 / (s + φ ^ 2 * f)) := by
    field_simp
  calc N ^ 2 / (s + φ ^ 2 * f)
      ≤ ((1 + s) * β ^ 2 + (α ^ 2 + α ^ 2 / s)) / (s + φ ^ 2 * f) := by gcongr
    _ = (1 + s) * (β ^ 2 / (s + φ ^ 2 * f)) + (1 + 1 / s) * (α ^ 2 / (s + φ ^ 2 * f)) := by
        rw [add_div, e2, mul_div_assoc]
    _ ≤ (1 + s) * (D ^ 2 / f) + (1 + 1 / s) * (4 * f * (c ^ 2 * s ^ 2)) := by
        gcongr
        exact ha.trans (by gcongr)
    _ = (1 + s) * (D ^ 2 / f) + 4 * c ^ 2 * (s ^ 2 + s) * f := by
        field_simp

/-- Gross' inequality in the form `∫ klFun f dγ ≤ ½ ∫ ‖Df‖² / f dγ` for a smooth positive `f`
with `∫ f dγ = 1`, from the compactly supported case by a cutoff and Fatou's lemma. -/
private lemma lintegral_klFun_le {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfpos : ∀ x, 0 < f x)
    (hfi : Integrable f (stdGaussian E)) (hfint : ∫ x, f x ∂stdGaussian E = 1) :
    ∫⁻ x, ENNReal.ofReal (klFun (f x)) ∂stdGaussian E ≤
      (1 / 2 : ℝ≥0∞) * ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 / ENNReal.ofReal (f x) ∂stdGaussian E := by
  by_cases hI : ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 / ENNReal.ofReal (f x) ∂stdGaussian E = (∞ : ℝ≥0∞)
  · rw [hI, ENNReal.mul_top (by norm_num)]
    exact le_top
  have hfc : Continuous f := hf.continuous
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hcDf : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  set g : E → ℝ := fun x => ‖fderiv ℝ f x‖ ^ 2 / f x with hg_def
  have hgc : Continuous g := (hcDf.norm.pow 2).div hfc fun x => (hfpos x).ne'
  have hg0 : ∀ x, 0 ≤ g x := fun x => div_nonneg (by positivity) (hfpos x).le
  have hge : ∀ x, ‖fderiv ℝ f x‖ₑ ^ 2 / ENNReal.ofReal (f x) = ENNReal.ofReal (g x) := fun x => by
    rw [hg_def, ENNReal.ofReal_div_of_pos (hfpos x), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm]
  simp only [hge] at hI ⊢
  have hgi : Integrable g (stdGaussian E) :=
    (lintegral_ofReal_ne_top_iff_integrable hgc.aestronglyMeasurable (ae_of_all _ hg0)).mp hI
  have hhalf : (1 / 2 : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (g x) ∂stdGaussian E =
      ENNReal.ofReal (1 / 2 * ∫ x, g x ∂stdGaussian E) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hg0),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat]
  rw [hhalf]
  set I := ∫ x, g x ∂stdGaussian E with hI_def
  -- The cutoffs `χ n x = ψ (s n • x)`, with `ψ = 1` on the unit ball and `s n = 1 / (n + 1)`.
  let ψ : ContDiffBump (0 : E) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have hψd : Differentiable ℝ ψ := (ψ.contDiff (n := 1)).differentiable (by simp)
  obtain ⟨c, hc⟩ := ((ψ.contDiff (n := 1)).continuous_fderiv
    (by simp)).bounded_above_of_compact_support (ψ.hasCompactSupport.fderiv ℝ)
  set s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hs_def
  have hs0 : ∀ n, 0 < s n := fun n => by positivity
  have hs1 : ∀ n, s n ≤ 1 := fun n => by
    rw [hs_def, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hs : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set F : ℕ → E → ℝ := fun n x => s n + ψ (s n • x) ^ 2 * f x with hF_def
  have hFcont : ∀ n, Continuous (F n) := fun n =>
    continuous_const.add (((ψ.continuous.comp (continuous_const_smul _)).pow 2).mul hfc)
  -- The derivative of `F n`.
  have hDF : ∀ n x, ‖fderiv ℝ (F n) x‖ ≤ ψ (s n • x) ^ 2 * ‖fderiv ℝ f x‖ +
      f x * (2 * ψ (s n • x) * (c * s n)) := by
    intro n x
    have hχ : HasFDerivAt (fun y => ψ (s n • y))
        ((fderiv ℝ ψ (s n • x)).comp (s n • ContinuousLinearMap.id ℝ E)) x :=
      (hψd _).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul (s n))
    have hχn : ‖(fderiv ℝ ψ (s n • x)).comp (s n • ContinuousLinearMap.id ℝ E)‖ ≤ c * s n := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hc _) ?_ (norm_nonneg _)
        ((norm_nonneg _).trans (hc 0)))
      refine (norm_smul_le (s n) (ContinuousLinearMap.id ℝ E)).trans ?_
      rw [Real.norm_eq_abs, abs_of_pos (hs0 n)]
      exact mul_le_of_le_one_right (hs0 n).le ContinuousLinearMap.norm_id_le
    have hFd := (hasFDerivAt_const (s n) x).add ((hχ.pow 2).mul (hfd x).hasFDerivAt)
    rw [show F n = (fun _ => s n) + (fun y => ψ (s n • y) ^ 2) * f from rfl, hFd.fderiv, zero_add]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), abs_of_pos (hfpos x), nsmul_eq_mul, pow_one,
      abs_of_nonneg (by have := ψ.nonneg (x := s n • x); positivity)]
    push_cast
    have h2ψ : 0 ≤ 2 * ψ (s n • x) := by have := ψ.nonneg (x := s n • x); positivity
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hχn h2ψ)
      (hfpos x).le)
  -- The bound on the Fisher information of `F n`.
  have hfish : ∀ n, ∫ x, ‖fderiv ℝ (F n) x‖ ^ 2 / F n x ∂stdGaussian E ≤
      (1 + s n) * I + 4 * c ^ 2 * (s n ^ 2 + s n) := by
    intro n
    have hb : ∀ x, ‖fderiv ℝ (F n) x‖ ^ 2 / F n x ≤
        (1 + s n) * g x + 4 * c ^ 2 * (s n ^ 2 + s n) * f x := fun x =>
      sq_div_add_le ψ.nonneg ψ.le_one (hfpos x) (hs0 n)
        (mul_nonneg ((norm_nonneg _).trans (hc 0)) (hs0 n).le) le_rfl (norm_nonneg _) (hDF n x)
    calc ∫ x, ‖fderiv ℝ (F n) x‖ ^ 2 / F n x ∂stdGaussian E
        ≤ ∫ x, ((1 + s n) * g x + 4 * c ^ 2 * (s n ^ 2 + s n) * f x) ∂stdGaussian E :=
          integral_mono_of_nonneg (ae_of_all _ fun x => div_nonneg (by positivity)
            (by have := ψ.nonneg (x := s n • x); have := hfpos x; have := hs0 n; positivity))
            ((hgi.const_mul _).add (hfi.const_mul _)) (ae_of_all _ hb)
      _ = (1 + s n) * I + 4 * c ^ 2 * (s n ^ 2 + s n) := by
          rw [integral_add (hgi.const_mul _) (hfi.const_mul _), integral_const_mul,
            integral_const_mul, hfint, mul_one]
  -- The compactly supported case, applied to `F n`.
  have hcore : ∀ n, ∫⁻ x, ENNReal.ofReal (klFun (F n x)) ∂stdGaussian E ≤
      ENNReal.ofReal (klFun (∫ x, F n x ∂stdGaussian E) +
        1 / 2 * ((1 + s n) * I + 4 * c ^ 2 * (s n ^ 2 + s n))) := by
    intro n
    have hF2 : ContDiff ℝ 2 (F n) := contDiff_const.add
      (((ψ.contDiff (n := ⊤)).comp (contDiff_id.const_smul _)).pow 2 |>.mul hf |>.of_le (by simp))
    have hFδ : ∀ x, s n ≤ F n x := fun x => by
      have := hfpos x
      simp only [hF_def]
      nlinarith [sq_nonneg (ψ (s n • x))]
    have hFc : HasCompactSupport fun x => F n x - s n :=
      (ψ.hasCompactSupport.comp_smul (hs0 n).ne').mono fun x hx h => hx (by
        simp only [hF_def, h]; ring)
    refine (lintegral_klFun_le_of_hasCompactSupport_sub (hs0 n) hF2 hFδ hFc).trans ?_
    gcongr
    exact hfish n
  -- Limits.
  have hpt : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
    intro x
    have h1 : Tendsto (fun n => s n + f x) atTop (𝓝 (f x)) := by
      simpa using hs.add_const (f x)
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with n hn
    have hx : s n • x ∈ Metric.closedBall (0 : E) ψ.rIn := by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (hs0 n)]
      change 1 / ((n : ℝ) + 1) * ‖x‖ ≤ 1
      have : ‖x‖ ≤ n + 1 := (Nat.le_ceil _).trans (by exact_mod_cast hn.trans (Nat.le_succ n))
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      exact this
    simp only [hF_def, ψ.one_of_mem_closedBall hx, one_pow, one_mul]
  have hFlim : Tendsto (fun n => ∫ x, F n x ∂stdGaussian E) atTop (𝓝 1) := by
    rw [← hfint]
    refine tendsto_integral_of_dominated_convergence (fun x => 1 + f x)
      (fun n => (hFcont n).aestronglyMeasurable) ((integrable_const _).add hfi)
      (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ hpt)
    have h1 := ψ.le_one (x := s n • x)
    have h0 := ψ.nonneg (x := s n • x)
    have := hfpos x
    rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [hF_def]; have := hs0 n; positivity)]
    simp only [hF_def]
    nlinarith [hs1 n, pow_le_one₀ h0 h1 (n := 2)]
  have hlim : Tendsto (fun n => klFun (∫ x, F n x ∂stdGaussian E) +
      1 / 2 * ((1 + s n) * I + 4 * c ^ 2 * (s n ^ 2 + s n))) atTop (𝓝 (1 / 2 * I)) := by
    have h1 := (continuous_klFun.tendsto 1).comp hFlim
    have h2 := (((tendsto_const_nhds (x := (1 : ℝ))).add hs).mul (tendsto_const_nhds (x := I))).add
      ((tendsto_const_nhds (x := 4 * c ^ 2)).mul ((hs.pow 2).add hs))
    have h3 := h1.add (h2.const_mul (1 / 2 : ℝ))
    simpa [klFun_one, Function.comp_def] using h3
  have hmeas : ∀ n, Measurable fun x => ENNReal.ofReal (klFun (F n x)) := fun n =>
    ENNReal.measurable_ofReal.comp (measurable_klFun.comp (hFcont n).measurable)
  calc ∫⁻ x, ENNReal.ofReal (klFun (f x)) ∂stdGaussian E
      = ∫⁻ x, liminf (fun n => ENNReal.ofReal (klFun (F n x))) atTop ∂stdGaussian E :=
        lintegral_congr fun x => (((ENNReal.continuous_ofReal.tendsto _).comp
          ((continuous_klFun.tendsto _).comp (hpt x))).liminf_eq).symm
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (klFun (F n x)) ∂stdGaussian E) atTop :=
        lintegral_liminf_le hmeas
    _ ≤ liminf (fun n => ENNReal.ofReal (klFun (∫ x, F n x ∂stdGaussian E) +
          1 / 2 * ((1 + s n) * I + 4 * c ^ 2 * (s n ^ 2 + s n)))) atTop :=
        liminf_le_liminf (Eventually.of_forall hcore)
    _ = ENNReal.ofReal (1 / 2 * I) :=
        ((ENNReal.continuous_ofReal.tendsto _).comp hlim).liminf_eq

end Auxiliary

/-! ### Gross' inequality -/

/-- **Gross' logarithmic Sobolev inequality.** Let `γ` be the standard Gaussian measure on a
finite-dimensional real inner product space `E`. For every smooth (`C^∞`) positive `f` with
`∫ f dγ = 1`,
`∫ f log f dγ ≤ ½ ∫ |∇f|² / f dγ`,
where the left side is the relative entropy `KL(f γ ‖ γ)` (M. Ledoux, *Heat flows, geometric
and functional inequalities*, Proceedings of the ICM, Seoul 2014, Theorem 2.1; originally
L. Gross, Amer. J. Math. 97 (1975)). The constant does not depend on the dimension. -/
theorem klDiv_withDensity_stdGaussian_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfpos : ∀ x, 0 < f x)
    (hfint : ∫ x, f x ∂(stdGaussian E) = 1) :
    klDiv ((stdGaussian E).withDensity fun x => ENNReal.ofReal (f x)) (stdGaussian E) ≤
      (1 / 2 : ℝ≥0∞) * ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 / ENNReal.ofReal (f x) ∂(stdGaussian E) := by
  have hfi : Integrable f (stdGaussian E) := by
    by_contra h
    rw [integral_undef h] at hfint
    exact zero_ne_one hfint
  have hfm : Measurable f := hf.continuous.measurable
  have : IsFiniteMeasure ((stdGaussian E).withDensity fun x => ENNReal.ofReal (f x)) :=
    isFiniteMeasure_withDensity_ofReal hfi.hasFiniteIntegral
  rw [klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous _ _)]
  have hrn := Measure.rnDeriv_withDensity (stdGaussian E) (f := fun x => ENNReal.ofReal (f x))
    (ENNReal.measurable_ofReal.comp hfm)
  calc ∫⁻ x, ENNReal.ofReal (klFun (((stdGaussian E).withDensity fun x =>
        ENNReal.ofReal (f x)).rnDeriv (stdGaussian E) x).toReal) ∂stdGaussian E
      = ∫⁻ x, ENNReal.ofReal (klFun (f x)) ∂stdGaussian E := by
        refine lintegral_congr_ae ?_
        filter_upwards [hrn] with x hx
        rw [hx, ENNReal.toReal_ofReal (hfpos x).le]
    _ ≤ _ := lintegral_klFun_le hf hfpos hfi hfint

end MathlibExt.Probability.GaussianLogSobolevWanted
