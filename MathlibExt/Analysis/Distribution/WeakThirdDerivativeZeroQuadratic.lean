/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
MA-ProofBench attribution for the adapted statement

Copyright (c) 2026 OpenBMB

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

Attribution and modification notice: adapted from the statement
`ma_proofbench_l2_66` in `benchmark/level2/ma_proofbench_l2_66.lean`,
openbmb/ma-proofbench at commit 31bab4c78fd1b0c464e767d62e9202163d1e9029
(MA-ProofBench, L. Pu et al., arXiv:2606.13782), under the MIT License above.
The ATLAS wanted declaration renamed the statement and supplied an audited docstring.
This revision preserves that name, proposition and docstring and supplies a new proof.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Vanishing weak third derivative and quadratic representatives -/

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Interval Topology

namespace MathlibExt.Analysis.Distribution.WeakThirdDerivativeZeroQuadraticWanted

private theorem compact_support_in_unit_interval {g : ℝ → ℝ}
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ioo (0 : ℝ) 1) :
    ∃ a b : ℝ, 0 < a ∧ b < 1 ∧ Function.support g ⊆ Icc a b := by
  by_cases he : (tsupport g).Nonempty
  · obtain ⟨a, ha⟩ := hc.exists_isLeast he
    obtain ⟨b, hb⟩ := hc.exists_isGreatest he
    refine ⟨a, b, (hs ha.1).1, (hs hb.1).2, ?_⟩
    intro x hx
    have hxt := subset_tsupport g hx
    exact ⟨ha.2 hxt, hb.2 hxt⟩
  · have hzero : tsupport g = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, ?_⟩
    intro x hx
    have hxt := subset_tsupport g hx
    rw [hzero] at hxt
    exact hxt.elim

private noncomputable def primitiveMoment (g : ℝ → ℝ) (i : ℕ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..t, x ^ i * g x

private theorem hasDerivAt_primitiveMoment {g : ℝ → ℝ} (hg : Continuous g) (i : ℕ) (t : ℝ) :
    HasDerivAt (primitiveMoment g i) (t ^ i * g t) t :=
  ((continuous_id.pow i |>.mul hg).integral_hasStrictDerivAt 0 t).hasDerivAt

private theorem contDiff_primitiveMoment {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (i : ℕ) :
    ContDiff ℝ ∞ (primitiveMoment g i) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (hasDerivAt_primitiveMoment hg.continuous i t).differentiableAt, ?_⟩
  rw [show deriv (primitiveMoment g i) = fun t => t ^ i * g t from
    funext fun t => (hasDerivAt_primitiveMoment hg.continuous i t).deriv]
  exact (contDiff_id.pow i).mul hg

private theorem primitiveMoment_eq_zero_below {g : ℝ → ℝ} {a b t : ℝ}
    (ha : 0 < a) (hs : Function.support g ⊆ Icc a b) (ht : t < a) (i : ℕ) :
    primitiveMoment g i t = 0 := by
  unfold primitiveMoment
  calc
    _ = ∫ x in (0 : ℝ)..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxa : x < a := (show x ≤ max 0 t from hx.2).trans_lt (max_lt ha ht)
      have hzero : g x = 0 := by
        by_contra hn
        exact (not_le_of_gt hxa) (hs (Function.mem_support.mpr hn)).1
      change x ^ i * g x = 0
      rw [hzero, mul_zero]
    _ = 0 := by simp

private theorem primitiveMoment_eq_zero_above {g : ℝ → ℝ} {a b t : ℝ}
    (ha : 0 < a) (hs : Function.support g ⊆ Icc a b) (ht : b < t) (i : ℕ)
    (hm : ∫ x : ℝ, x ^ i * g x = 0) : primitiveMoment g i t = 0 := by
  by_cases ht0 : 0 ≤ t
  · rw [primitiveMoment, intervalIntegral.integral_of_le ht0,
      setIntegral_eq_integral_of_forall_compl_eq_zero, hm]
    intro x hx
    by_cases h : g x = 0
    · simp [h]
    · exact (hx ⟨ha.trans_le (hs (Function.mem_support.mpr h)).1,
        (hs (Function.mem_support.mpr h)).2.trans ht.le⟩).elim
  · exact primitiveMoment_eq_zero_below ha hs (lt_trans (lt_of_not_ge ht0) ha) i

/-- A test function whose first three moments vanish has a compactly supported third primitive. -/
private theorem exists_compact_third_primitive {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    {a b : ℝ} (ha : 0 < a) (hs : Function.support g ⊆ Icc a b)
    (hm : ∀ i : Fin 3, ∫ x : ℝ, x ^ (i : ℕ) * g x = 0) :
    ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ Function.support G ⊆ Icc a b ∧
      deriv (deriv (deriv G)) = g := by
  let P := primitiveMoment g
  let G (t : ℝ) := (t ^ 2 * P 0 t - 2 * t * P 1 t + P 2 t) / 2
  have hP (i : ℕ) := contDiff_primitiveMoment hg i
  have hG : ContDiff ℝ ∞ G := by
    dsimp only [G]
    have h1 : ContDiff ℝ ∞ (fun t : ℝ => t ^ 2 * P 0 t) := (contDiff_id.pow 2).mul (hP 0)
    have h2 : ContDiff ℝ ∞ (fun t : ℝ => 2 * t * P 1 t) :=
      (contDiff_const.mul contDiff_id).mul (hP 1)
    exact ((h1.sub h2).add (hP 2)).div_const 2
  have hG' (t : ℝ) : HasDerivAt G (t * P 0 t - P 1 t) t := by
    have ht := hasDerivAt_id t
    have h0 := hasDerivAt_primitiveMoment hg.continuous 0 t
    have h1 := hasDerivAt_primitiveMoment hg.continuous 1 t
    have h2 := hasDerivAt_primitiveMoment hg.continuous 2 t
    convert (((ht.pow 2).mul h0).sub ((ht.const_mul 2).mul h1) |>.add h2).div_const 2 using 1
    · rfl
    · change t * P 0 t - P 1 t =
        ((2 : ℝ) * t ^ (2 - 1 : ℕ) * 1 * P 0 t + t ^ 2 * (t ^ (0 : ℕ) * g t) -
          (2 * 1 * P 1 t + 2 * t * (t ^ (1 : ℕ) * g t)) + t ^ 2 * g t) / 2
      ring
  have hG'' (t : ℝ) : HasDerivAt (fun u => u * P 0 u - P 1 u) (P 0 t) t := by
    have h0 := hasDerivAt_primitiveMoment hg.continuous 0 t
    have h1 := hasDerivAt_primitiveMoment hg.continuous 1 t
    convert (((hasDerivAt_id t).mul h0).sub h1) using 1
    · rfl
    · change P 0 t = 1 * P 0 t + t * (t ^ (0 : ℕ) * g t) - t ^ (1 : ℕ) * g t
      ring
  refine ⟨G, hG, ?_, ?_⟩
  · intro t ht
    by_contra htb
    have hzero (i : Fin 3) : P i t = 0 := by
      by_cases hta : t < a
      · exact primitiveMoment_eq_zero_below ha hs hta i
      · have hbt : b < t := lt_of_not_ge fun h => htb ⟨le_of_not_gt hta, h⟩
        exact primitiveMoment_eq_zero_above ha hs hbt i (hm i)
    exact (Function.mem_support.mp ht) (by simp [G, show P 0 t = 0 from hzero 0,
      show P 1 t = 0 from hzero 1, show P 2 t = 0 from hzero 2])
  · rw [show deriv G = (fun t => t * P 0 t - P 1 t) from funext fun t => (hG' t).deriv,
      show deriv (fun t => t * P 0 t - P 1 t) = P 0 from funext fun t => (hG'' t).deriv]
    exact funext fun t => by simpa only [pow_zero, one_mul] using
      (hasDerivAt_primitiveMoment hg.continuous 0 t).deriv

private def openUnit : Opens ℝ := ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩
private abbrev UnitTest := 𝓓(openUnit, ℝ)

private noncomputable def integralWeight (μ : Measure ℝ) (w : ℝ → ℝ) : UnitTest →ₗ[ℝ] ℝ :=
  (TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ).flip μ w :
    UnitTest →L[ℝ] ℝ).toLinearMap

private theorem integralWeight_apply {μ : Measure ℝ} {w : ℝ → ℝ}
    (hw : LocallyIntegrableOn w openUnit μ) (g : UnitTest) :
    integralWeight μ w g = ∫ x, w x * g x ∂μ :=
  TestFunction.integralAgainstBilinCLM_eq_integral hw

private theorem monomial_locallyIntegrable (i : ℕ) :
    LocallyIntegrableOn (fun x : ℝ => x ^ i) openUnit volume :=
  (continuous_id.pow i).locallyIntegrable.locallyIntegrableOn _

private noncomputable def testMoments : UnitTest →ₗ[ℝ] (Fin 3 → ℝ) :=
  LinearMap.pi fun i => integralWeight volume (fun x => x ^ (i : ℕ))

private theorem testMoments_apply (g : UnitTest) (i : Fin 3) :
    testMoments g i = ∫ x, x ^ (i : ℕ) * g x :=
  integralWeight_apply (monomial_locallyIntegrable i) g

private theorem linear_on_three_coordinates (A : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) :
    ∃ a b c : ℝ, ∀ v : Fin 3 → ℝ, A v = a * v 0 + b * v 1 + c * v 2 := by
  let B := Pi.basisFun ℝ (Fin 3)
  refine ⟨A (B 0), A (B 1), A (B 2), fun v => ?_⟩
  have he := congrArg A (B.sum_repr v)
  simp only [B, Pi.basisFun_repr, Fin.sum_univ_three] at he
  rw [map_add, map_add, map_smul, map_smul, map_smul] at he
  rw [← he]
  simp only [smul_eq_mul]
  ring

/-- **A function with vanishing weak third derivative on $(0,1)$ is a.e. a polynomial of
degree at most $2$ on $[0,1]$.** Let $f:\mathbb{R}\to\mathbb{R}$ be integrable on $[0,1]$, and
suppose that $\int_{0}^{1} f(x)\,g'''(x)\,dx=0$ for every smooth function
$g:\mathbb{R}\to\mathbb{R}$ whose support is contained in some closed interval
$[s,t] \subseteq (0,1)$. Then there are real numbers $a$, $b$, $c$ such that $f(x)=a+bx+cx^2$
for almost every $x\in[0,1]$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis;
Distributions, generalized functions, distribution spaces),
`benchmark/level2/ma_proofbench_l2_66.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem ae_eq_quadratic_of_integral_mul_iteratedDeriv_three_eq_zero
  (f : ℝ → ℝ)
  (hf : MeasureTheory.MemLp f 1 (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 1)))
  (hweak : ∀ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
    (∃ a b : ℝ, Function.support g ⊆ Set.Icc a b ∧
      Set.Icc a b ⊆ Set.Ioo (0 : ℝ) 1) →
      ∫ x in Set.Icc 0 1, f x * deriv (deriv (deriv g)) x = 0) :
  ∃ a b c : ℝ, ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 1)),
    f x = a + b * x + c * x ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Icc 0 1)
  have hfint : Integrable f μ := hf.integrable le_rfl
  have hfLoc : LocallyIntegrableOn f openUnit μ := hfint.locallyIntegrable.locallyIntegrableOn _
  let L := integralWeight μ f
  have hL (g : UnitTest) : L g = ∫ x, f x * g x ∂μ := integralWeight_apply hfLoc g
  have hker : testMoments.ker ≤ L.ker := by
    intro g hg
    have hM : testMoments g = 0 := LinearMap.mem_ker.mp hg
    have hm (i : Fin 3) : ∫ x, x ^ (i : ℕ) * g x = 0 :=
      (testMoments_apply g i).symm.trans (congrFun hM i)
    obtain ⟨a, b, ha, hb, hs⟩ := compact_support_in_unit_interval g.hasCompactSupport
      g.tsupport_subset
    obtain ⟨G, hG, hGsup, hderiv⟩ := exists_compact_third_primitive g.contDiff ha hs hm
    have hw := hweak G hG ⟨a, b, hGsup,
      fun _ hx => ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩⟩
    rw [hderiv] at hw
    exact LinearMap.mem_ker.mpr ((hL g).trans hw)
  have hdual : L ∈ LinearMap.range testMoments.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    exact (Submodule.mem_dualAnnihilator L).mpr fun g hg => LinearMap.mem_ker.mp (hker hg)
  obtain ⟨A, hA⟩ := LinearMap.mem_range.mp hdual
  have hfactor (g : UnitTest) : L g = A (testMoments g) := (DFunLike.congr_fun hA g).symm
  obtain ⟨a, b, c, hcoeff⟩ := linear_on_three_coordinates A
  let q (x : ℝ) := a + b * x + c * x ^ 2
  have hq : Continuous q := by
    dsimp only [q]
    fun_prop
  have hqint : Integrable q μ :=
    ContinuousOn.integrableOn_compact isCompact_Icc hq.continuousOn
  have hmon (g : UnitTest) (i : ℕ) :
      (∫ x, x ^ i * g x ∂μ) = ∫ x, x ^ i * g x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hg0 : g x = 0 := image_eq_zero_of_notMem_tsupport fun h =>
      hx (Ioo_subset_Icc_self (g.tsupport_subset h))
    rw [hg0, mul_zero]
  have hqeval (g : UnitTest) : ∫ x, q x * g x ∂μ = L g := by
    rw [hfactor g, hcoeff]
    simp only [testMoments_apply]
    have hi (n : ℕ) : Integrable (fun x => x ^ n * g x) μ :=
      (g.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ).flip
        (monomial_locallyIntegrable n)).restrict
    calc
      _ = ∫ x, a * (x ^ (0 : ℕ) * g x) + b * (x ^ (1 : ℕ) * g x) +
            c * (x ^ (2 : ℕ) * g x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp only [q]
        ring
      _ = (∫ x, a * (x ^ (0 : ℕ) * g x) + b * (x ^ (1 : ℕ) * g x) ∂μ) +
          (∫ x, c * (x ^ (2 : ℕ) * g x) ∂μ) :=
        integral_add (((hi 0).const_mul a).add ((hi 1).const_mul b)) ((hi 2).const_mul c)
      _ = _ := by
        rw [integral_add ((hi 0).const_mul a) ((hi 1).const_mul b), integral_const_mul,
          integral_const_mul, integral_const_mul, hmon g 0, hmon g 1, hmon g 2]
        rfl
  have hloc : LocallyIntegrableOn (f - q) (Ioo (0 : ℝ) 1) μ :=
    (hfint.sub hqint).locallyIntegrable.locallyIntegrableOn _
  have hzero : ∀ᵐ x ∂μ, x ∈ Ioo (0 : ℝ) 1 → (f - q) x = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    intro g hg hc hs
    let t : UnitTest := ⟨g, hg, hc, hs⟩
    calc
      _ = ∫ x, f x * t x - q x * t x ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        change g x * (f x - q x) = f x * g x - q x * g x
        ring
      _ = L t - ∫ x, q x * t x ∂μ :=
        (integral_sub (t.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ).flip hfLoc)
        (t.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ).flip
          (hqint.locallyIntegrable.locallyIntegrableOn openUnit))).trans
        (congrArg (fun y => y - ∫ x, q x * t x ∂μ) (hL t).symm)
      _ = 0 := by rw [hqeval, sub_self]
  have hsame : μ.restrict (Ioo (0 : ℝ) 1) = μ := by
    change (volume.restrict (Icc (0 : ℝ) 1)).restrict (Ioo (0 : ℝ) 1) = _
    rw [Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr Ioo_subset_Icc_self]
    exact Measure.restrict_congr_set Ioo_ae_eq_Icc
  have hz : ∀ᵐ x ∂μ.restrict (Ioo (0 : ℝ) 1), (f - q) x = 0 :=
    (ae_restrict_iff' measurableSet_Ioo).mpr hzero
  rw [hsame] at hz
  exact ⟨a, b, c, hz.mono fun x hx => sub_eq_zero.mp hx⟩

end MathlibExt.Analysis.Distribution.WeakThirdDerivativeZeroQuadraticWanted
