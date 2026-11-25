/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_87.lean` (openbmb/ma-proofbench at commit
31bab4c78fd1b0c464e767d62e9202163d1e9029):
Copyright (c) 2026 OpenBMB
Licensed under the MIT License.
Authors (MA-ProofBench): Lushi Pu, Weiming Zhang, Xinheng Xie, Zixuan Fu, Bingxiang He, Hongya Lyu,
Xin Li, Jie Zhou, Yudong Wang.
The adaptation covers the statement of the integral operator theorem.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Integral operators with an `L^p` kernel

An `L^p` kernel on the unit square defines a bounded linear map from the conjugate
`L^q` space to `L^p`, given almost everywhere by the integral of the kernel against the input.
-/

public section

open MeasureTheory Filter
open scoped ENNReal

namespace MathlibExt.Analysis.OperatorTheory.LpKernelIntegralOperatorBoundedWanted

/-- **Integral operators with an $L^p$ kernel map $L^q$ to $L^p$.** Let $1 < p < \infty$ and let
$q \ge 1$ be the dual exponent, $p^{-1} + q^{-1} = 1$. Let $K : \mathbb{R}^2 \to \mathbb{R}$ lie
in $L^p((0,1)^2)$, where $L^p((0,1)^2)$, $L^p(0,1)$ and $L^q(0,1)$ are spaces of real functions
for Lebesgue measure. Then for every $f \in L^q(0,1)$ the function $y \mapsto K(x,y)f(y)$ is
integrable on $(0,1)$ for almost every $x \in (0,1)$, and there is a bounded linear operator
$A : L^q(0,1) \to L^p(0,1)$ such that for every $f \in L^q(0,1)$,
$$(Af)(x) = \int_0^1 K(x,y) f(y)\,dy \quad \text{for almost every } x \in (0,1).$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; Integral,
integro-differential, and pseudodifferential operators),
`benchmark/level2/ma_proofbench_l2_87.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem integrable_kernel_mul_and_exists_clm_integral_operator
  (p q : ENNReal)
  [Fact (1 ≤ p)]
  [Fact (1 ≤ q)]
  (hp_ne_top : p ≠ ⊤)
  (hp_gt_one : 1 < p)
  (hq : 1 / p + 1 / q = 1)
  (K : ℝ × ℝ → ℝ)
  (hK : MemLp K p
    ((Measure.restrict volume (Set.Ioo (0 : ℝ) 1)).prod
      (Measure.restrict volume (Set.Ioo (0 : ℝ) 1)))) :
  (∀ f : Lp ℝ q (Measure.restrict volume (Set.Ioo (0 : ℝ) 1)),
      ∀ᵐ x ∂(Measure.restrict volume (Set.Ioo (0 : ℝ) 1)),
        Integrable (fun y => K (x, y) * f y) (Measure.restrict volume (Set.Ioo (0 : ℝ) 1))) ∧
    (∃ A :
      Lp ℝ q (Measure.restrict volume (Set.Ioo (0 : ℝ) 1)) →L[ℝ]
        Lp ℝ p (Measure.restrict volume (Set.Ioo (0 : ℝ) 1)),
      ∀ f : Lp ℝ q (Measure.restrict volume (Set.Ioo (0 : ℝ) 1)),
        ∀ᵐ x ∂(Measure.restrict volume (Set.Ioo (0 : ℝ) 1)),
          A f x = ∫ y, K (x, y) * f y ∂(Measure.restrict volume (Set.Ioo (0 : ℝ) 1))) := by
  let μ := Measure.restrict volume (Set.Ioo (0 : ℝ) 1)
  change MemLp K p (μ.prod μ) at hK
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp_gt_one).ne'
  have hpReal : p.toReal ≠ 0 := (ENNReal.toReal_pos hp0 hp_ne_top).ne'
  let _ : ENNReal.HolderConjugate p q := ENNReal.holderConjugate_iff.mpr (by
    simpa only [one_div] using hq)
  -- Tonelli identifies the outer norm of the section norms with the kernel norm.
  let sectionPower (x : ℝ) := ∫⁻ y, ‖K (x, y)‖ₑ ^ p.toReal ∂μ
  let sectionBound (x : ℝ) := sectionPower x ^ (1 / p.toReal)
  have hPowerMeas : AEMeasurable (fun z => ‖K z‖ₑ ^ p.toReal) (μ.prod μ) :=
    hK.aemeasurable.eNorm.pow_const _
  have hSectionPowerMeas : AEMeasurable sectionPower μ := hPowerMeas.lintegral_prod_right'
  have hPowerIntegral : ∫⁻ x, sectionPower x ∂μ = ∫⁻ z, ‖K z‖ₑ ^ p.toReal ∂μ.prod μ :=
    (lintegral_prod _ hPowerMeas).symm
  have hPowerFinite : ∫⁻ x, sectionPower x ∂μ < ∞ := by
    rw [hPowerIntegral]
    exact lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hp0 hp_ne_top hK.eLpNorm_lt_top
  have hSection : ∀ᵐ x ∂μ, MemLp (fun y => K (x, y)) p μ ∧
      eLpNorm (fun y => K (x, y)) p μ = sectionBound x := by
    filter_upwards [hK.aestronglyMeasurable.prodMk_left,
      ae_lt_top' hSectionPowerMeas hPowerFinite.ne] with x hx hfin
    have heq : eLpNorm (fun y => K (x, y)) p μ = sectionBound x :=
      eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_ne_top hx
    exact ⟨memLp_iff.mpr (heq.trans_lt (ENNReal.rpow_lt_top_of_nonneg (by positivity) hfin.ne)),
      heq⟩
  have hBoundMeas : AEStronglyMeasurable sectionBound μ :=
    (hSectionPowerMeas.pow_const _).aestronglyMeasurable
  have hBound : eLpNorm sectionBound p μ = eLpNorm K p (μ.prod μ) := by
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_ne_top hBoundMeas,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_ne_top hK.aestronglyMeasurable]
    simp only [eNorm_eq_self, sectionBound, one_div, ENNReal.rpow_inv_rpow hpReal,
      hPowerIntegral]
  -- Apply Hölder on each section before taking the outer norm.
  have hIntegrable (f : Lp ℝ q μ) :
      ∀ᵐ x ∂μ, Integrable (fun y => K (x, y) * f y) μ := by
    filter_upwards [hSection] with x hx
    exact memLp_one_iff_integrable.mp (hx.1.fun_mul (Lp.memLp f))
  let T (f : Lp ℝ q μ) (x : ℝ) := ∫ y, K (x, y) * f y ∂μ
  have hEstimate (f : Lp ℝ q μ) :
      eLpNorm (T f) p μ ≤ eLpNorm K p (μ.prod μ) * eLpNorm f q μ := by
    have hMeas : AEStronglyMeasurable (T f) μ :=
      (hK.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f).comp_snd).integral_prod_right'
    calc
      eLpNorm (T f) p μ ≤ eLpNorm (fun x => eLpNorm f q μ * sectionBound x) p μ := by
        apply eLpNorm_mono_eNorm_ae hMeas
        filter_upwards [hSection] with x hx
        rw [eNorm_eq_self, mul_comm, ← hx.2]
        have hMul := hx.1.fun_mul (r := 1) (Lp.memLp f)
        calc
          ‖T f x‖ₑ ≤ ∫⁻ y, ‖K (x, y) * f y‖ₑ ∂μ := eNorm_integral_le_lintegral_eNorm _
          _ = eLpNorm (fun y => K (x, y) * f y) 1 μ :=
            (eLpNorm_one_eq_lintegral_eNorm hMul.aestronglyMeasurable).symm
          _ ≤ eLpNorm (fun y => K (x, y)) p μ * eLpNorm f q μ :=
            eLpNorm_smul_le_mul_eLpNorm hx.1.aestronglyMeasurable (Lp.aestronglyMeasurable f)
      _ = eLpNorm K p (μ.prod μ) * eLpNorm f q μ := by
        rw [eLpNorm_const_mul_ennreal hBoundMeas, hBound, mul_comm]
  have hLp (f : Lp ℝ q μ) : MemLp (T f) p μ :=
    memLp_iff.mpr ((hEstimate f).trans_lt
      (ENNReal.mul_lt_top hK.eLpNorm_lt_top (Lp.eLpNorm_lt_top f)))
  let A : Lp ℝ q μ →ₗ[ℝ] Lp ℝ p μ :=
    { toFun := fun f => (hLp f).toLp (T f)
      map_add' := by
        intro f g
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        filter_upwards [hIntegrable f, hIntegrable g] with x hfx hgx
        change T (f + g) x = T f x + T g x
        dsimp only [T]
        rw [← integral_add hfx hgx]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add f g] with y hy
        simp only [Pi.add_apply] at hy ⊢
        rw [hy, mul_add]
      map_smul' := by
        intro c f
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        refine Eventually.of_forall fun x => ?_
        change T (c • f) x = c * T f x
        dsimp only [T]
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with y hy
        simp only [Pi.smul_apply, smul_eq_mul] at hy
        rw [hy, mul_left_comm] }
  have hNorm (f : Lp ℝ q μ) : ‖A f‖ ≤ (eLpNorm K p (μ.prod μ)).toReal * ‖f‖ := by
    change ‖(hLp f).toLp (T f)‖ ≤ _
    rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hK.eLpNorm_lt_top.ne
      (Lp.eLpNorm_lt_top f).ne) (hEstimate f)
  exact ⟨hIntegrable, A.mkContinuous _ hNorm, fun f => (hLp f).coeFn_toLp⟩

end MathlibExt.Analysis.OperatorTheory.LpKernelIntegralOperatorBoundedWanted
