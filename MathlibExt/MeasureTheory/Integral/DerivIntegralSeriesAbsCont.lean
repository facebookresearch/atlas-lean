/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Differentiating ∫∑f_n term by term under absolute continuity

The following OpenBMB notice applies to the adapted statement and its documentation.

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

Attribution and modification notice: the statement below is taken from openbmb/ma-proofbench at
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_50.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l2_50 … := by sorry` into the Batteries `theorem_wanted`
`exists_hasDerivAt_integral_tsum_ae`; moved the informal problem statement docstring onto it and
placed the declarations in namespace
`MathlibExt.MeasureTheory.DerivIntegralSeriesAbsContWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system; corrected the statement: added the source's
hypothesis that each `f n` is measurable on `Ω × (a, b)` (`h_meas`), without which the statement
is false.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Prod

/-! # Termwise differentiation of an integrated series -/

@[expose] public section

open Filter MeasureTheory Set
open scoped Interval Topology

namespace MathlibExt.MeasureTheory.DerivIntegralSeriesAbsContWanted

private theorem integral_deriv_complex {g : ℝ → ℂ} {u v : ℝ}
    (hg : AbsolutelyContinuousOnInterval g u v)
    (hd : IntervalIntegrable (deriv g) volume u v) :
    (∫ t in u..v, deriv g t) = g v - g u := by
  have hre : AbsolutelyContinuousOnInterval (fun t => (g t).re) u v :=
    Complex.reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hg
  have him : AbsolutelyContinuousOnInterval (fun t => (g t).im) u v :=
    Complex.imCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hg
  have hdiff : ∀ᵐ x ∂(volume.restrict (uIoc u v)), DifferentiableAt ℝ g x := by
    have h := (hre.ae_differentiableAt.and him.ae_differentiableAt).filter_mono
      (ae_mono (Measure.restrict_le_self (s := uIoc u v)))
    filter_upwards [h, ae_restrict_mem measurableSet_uIoc] with x hx hmem
    have hr := Complex.ofRealCLM.differentiableAt.comp x (hx.1 (uIoc_subset_uIcc hmem))
    have hi := Complex.ofRealCLM.differentiableAt.comp x (hx.2 (uIoc_subset_uIcc hmem))
    have hadd := hr.fun_add (hi.fun_mul (differentiableAt_const Complex.I))
    simpa only [Function.comp_apply, Complex.ofRealCLM_apply, Complex.re_add_im] using hadd
  have hrEq : (fun t => (deriv g t).re) =ᵐ[volume.restrict (uIoc u v)]
      deriv (fun t => (g t).re) := by
    filter_upwards [hdiff] with x hx
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hx.hasDerivAt).deriv.symm
  have hiEq : (fun t => (deriv g t).im) =ᵐ[volume.restrict (uIoc u v)]
      deriv (fun t => (g t).im) := by
    filter_upwards [hdiff] with x hx
    exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hx.hasDerivAt).deriv.symm
  apply Complex.ext
  · change Complex.reCLM (∫ t in u..v, deriv g t) = (g v - g u).re
    rw [← Complex.reCLM.intervalIntegral_comp_comm hd]
    change (∫ t in u..v, (deriv g t).re) = (g v - g u).re
    rw [intervalIntegral.integral_congr_ae_restrict hrEq, hre.integral_deriv_eq_sub, Complex.sub_re]
  · change Complex.imCLM (∫ t in u..v, deriv g t) = (g v - g u).im
    rw [← Complex.imCLM.intervalIntegral_comp_comm hd]
    change (∫ t in u..v, (deriv g t).im) = (g v - g u).im
    rw [intervalIntegral.integral_congr_ae_restrict hiEq, him.integral_deriv_eq_sub, Complex.sub_im]

private theorem integrable_series {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure α} {g : ℕ → α → E}
    (hm : ∀ n, AEStronglyMeasurable (g n) μ)
    (hs : ∀ᵐ x ∂μ, Summable (fun n => ‖g n x‖))
    (hint : Integrable (fun x => ∑' n, ‖g n x‖) μ) :
    (∀ n, Integrable (g n) μ) ∧ Integrable (fun x => ∑' n, g n x) μ ∧
    HasSum (fun n => ∫ x, ‖g n x‖ ∂μ) (∫ x, ∑' n, ‖g n x‖ ∂μ) ∧
    HasSum (fun n => ∫ x, g n x ∂μ) (∫ x, ∑' n, g n x ∂μ) := by
  refine ⟨fun n => hint.mono' (hm n) ?_, hint.mono' (AEStronglyMeasurable.tsum hm) ?_, ?_, ?_⟩
  · filter_upwards [hs] with x hx
    exact hx.le_tsum n (fun i _ => norm_nonneg (g i x))
  · exact hs.mono fun _ hx => norm_tsum_le_tsum_norm hx
  · apply hasSum_integral_of_dominated_convergence (fun n x => ‖g n x‖)
      (fun n => (hm n).norm) (fun n => Eventually.of_forall fun x => by simp) hs hint
    exact hs.mono fun _ hx => hx.hasSum
  · exact hasSum_integral_of_dominated_convergence (fun n x => ‖g n x‖) hm
      (fun n => Eventually.of_forall fun _ => le_rfl) hs hint
      (hs.mono fun _ hx => hx.of_norm.hasSum)

private theorem hasSum_interval_series {D : ℕ → ℝ → ℂ} {a b u v : ℝ}
    (hu : u ∈ Icc a b) (hv : v ∈ Icc a b)
    (hm : ∀ n, AEStronglyMeasurable (D n) (volume.restrict (Icc a b)))
    (hs : ∀ᵐ t ∂volume.restrict (Icc a b), Summable (fun n => ‖D n t‖))
    (hint : IntegrableOn (fun t => ∑' n, ‖D n t‖) (Icc a b)) :
    HasSum (fun n => ∫ t in u..v, D n t) (∫ t in u..v, ∑' n, D n t) := by
  have h (s : Set ℝ) (hsub : s ⊆ Icc a b) :
      HasSum (fun n => ∫ t in s, D n t) (∫ t in s, ∑' n, D n t) := by
    have hμ : (volume.restrict s : Measure ℝ) ≤ volume.restrict (Icc a b) :=
      Measure.restrict_mono hsub le_rfl
    exact (integrable_series (fun n => (hm n).mono_measure hμ) (hs.filter_mono (ae_mono hμ))
      (hint.mono_set hsub)).2.2.2
  simpa only [intervalIntegral] using
    (h (Ioc u v) (Ioc_subset_Icc_self.trans (Icc_subset_Icc hu.1 hv.2))).sub
      (h (Ioc v u) (Ioc_subset_Icc_self.trans (Icc_subset_Icc hv.1 hu.2)))

private theorem sum_eq_anchor_add_integral {f : ℕ → ℝ → ℂ} {a b c : ℝ}
    (hab : a ≤ b) (hc : c ∈ Icc a b)
    (ha : ∀ n, AbsolutelyContinuousOnInterval (f n) a b)
    (hm : ∀ n, AEStronglyMeasurable (deriv (f n)) (volume.restrict (Icc a b)))
    (hs : ∀ᵐ t ∂volume.restrict (Icc a b), Summable (fun n => ‖deriv (f n) t‖))
    (hi : IntegrableOn (fun t => ∑' n, ‖deriv (f n) t‖) (Icc a b))
    (hbase : Summable (fun n => ‖f n c‖)) {y : ℝ} (hy : y ∈ Icc a b) :
    (Summable (fun n => ‖f n y‖) ∧
      ∑' n, ‖f n y‖ ≤ (∑' n, ‖f n c‖) + ∫ t in Icc a b, ∑' n, ‖deriv (f n) t‖) ∧
    (∑' n, f n y) = (∑' n, f n c) + ∫ t in c..y, ∑' n, deriv (f n) t := by
  obtain ⟨hDi, _, hnormsum, _⟩ := integrable_series hm hs hi
  have hsub : uIoc c y ⊆ Icc a b := uIoc_subset_uIcc.trans (uIcc_subset_Icc hc hy)
  have hftc (n : ℕ) : (∫ t in c..y, deriv (f n) t) = f n y - f n c := by
    have hcont : AbsolutelyContinuousOnInterval (f n) c y := (ha n).mono (by
      simpa only [uIcc_of_le hab] using uIcc_subset_Icc hc hy)
    have hD_on : IntegrableOn (deriv (f n)) (Icc a b) volume := hDi n
    exact integral_deriv_complex hcont (intervalIntegrable_iff.2 (hD_on.mono_set hsub))
  have hbound (n : ℕ) : ‖f n y‖ ≤ ‖f n c‖ + ∫ t in Icc a b, ‖deriv (f n) t‖ := by
    calc
      ‖f n y‖ = ‖f n c + ∫ t in c..y, deriv (f n) t‖ := by
        rw [hftc n, add_comm (f n c), sub_add_cancel]
      _ ≤ ‖f n c‖ + ‖∫ t in c..y, deriv (f n) t‖ := norm_add_le _ _
      _ ≤ _ := by
        gcongr
        refine (intervalIntegral.norm_integral_le_integral_norm_uIoc (μ := volume)).trans ?_
        exact setIntegral_mono_set (hDi n).norm (Eventually.of_forall fun t => norm_nonneg _)
          (Eventually.of_forall hsub)
  have hsum := hbase.add hnormsum.summable
  have hnorm := Summable.of_nonneg_of_le (fun n => norm_nonneg (f n y)) hbound hsum
  refine ⟨⟨hnorm, ?_⟩, ?_⟩
  · exact (hnorm.tsum_le_tsum hbound hsum).trans_eq
      ((hbase.tsum_add hnormsum.summable).trans (congrArg (_ + ·) hnormsum.tsum_eq))
  have heq := (hasSum_interval_series hc hy hm hs hi).tsum_eq
  simp_rw [hftc] at heq
  rw [hnorm.of_norm.tsum_sub hbase.of_norm] at heq
  exact eq_add_of_sub_eq' heq

private theorem integral_interval_swap {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SFinite μ] {D : α → ℝ → ℂ} {a b u v : ℝ}
    (hD : Integrable (Function.uncurry D) (μ.prod (volume.restrict (Icc a b))))
    (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) :
    Integrable (fun x => ∫ t in u..v, D x t) μ ∧
      (∫ x, (∫ t in u..v, D x t) ∂μ) = ∫ t in u..v, ∫ x, D x t ∂μ := by
  have hJ {l r : ℝ} (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) :
      Integrable (Function.uncurry D) (μ.prod (volume.restrict (Ioc l r))) :=
    hD.mono_measure (Measure.prod_mono le_rfl
      (Measure.restrict_mono (Ioc_subset_Icc_self.trans (Icc_subset_Icc hl.1 hr.2)) le_rfl))
  have h1 : Integrable (fun x => ∫ t in Ioc u v, D x t) μ := (hJ hu hv).integral_prod_left
  have h2 : Integrable (fun x => ∫ t in Ioc v u, D x t) μ := (hJ hv hu).integral_prod_left
  constructor
  · exact h1.sub h2
  · change (∫ x, ((∫ t in Ioc u v, D x t) - (∫ t in Ioc v u, D x t)) ∂μ) =
      (∫ t in Ioc u v, ∫ x, D x t ∂μ) - (∫ t in Ioc v u, ∫ x, D x t ∂μ)
    rw [integral_sub h1 h2]
    exact congrArg₂ (· - ·) (integral_integral_swap (hJ hu hv)) (integral_integral_swap (hJ hv hu))

private theorem exists_integrated_series {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    {a b c : ℝ} (hab : a < b) (hc : c ∈ Icc a b) (f : ℕ → α → ℝ → ℂ)
    (hfm : ∀ n, AEStronglyMeasurable (Function.uncurry (f n))
      (μ.prod (volume.restrict (Icc a b))))
    (hac : ∀ n, ∀ᵐ x ∂μ, AbsolutelyContinuousOnInterval (f n x) a b)
    (hdm : ∀ n, AEStronglyMeasurable (fun z : α × ℝ => deriv (f n z.1) z.2)
      (μ.prod (volume.restrict (Icc a b))))
    (hds : ∀ᵐ z ∂(μ.prod (volume.restrict (Icc a b))),
      Summable (fun n => ‖deriv (f n z.1) z.2‖))
    (hdi : Integrable (fun z : α × ℝ => ∑' n, ‖deriv (f n z.1) z.2‖)
      (μ.prod (volume.restrict (Icc a b))))
    (hcs : ∀ᵐ x ∂μ, Summable (fun n => ‖f n x c‖))
    (hci : Integrable (fun x => ∑' n, ‖f n x c‖) μ) :
    ∃ F : ℝ → ℂ,
      (∀ᵐ y ∂volume.restrict (Icc a b), Integrable (fun x => ∑' n, f n x y) μ) ∧
      (∀ᵐ y ∂volume.restrict (Icc a b), F y = ∫ x, ∑' n, f n x y ∂μ) ∧
      (∀ᵐ y ∂volume.restrict (Icc a b),
        HasDerivAt F (∑' n, ∫ x, deriv (f n x) y ∂μ) y) := by
  let ν := (volume : Measure ℝ).restrict (Icc a b)
  let S (y : ℝ) (x : α) := ∑' n, f n x y
  let D (x : α) (t : ℝ) := ∑' n, deriv (f n x) t
  let A (y : ℝ) (x : α) := ∫ t in c..y, D x t
  let G (t : ℝ) := ∫ x, D x t ∂μ
  have hD : Integrable (Function.uncurry D) (μ.prod ν) := (integrable_series hdm hds hdi).2.1
  have hpoint : ∀ᵐ x ∂μ, ∀ y ∈ Icc a b, S y x = S c x + A y x := by
    have hmx := ae_all_iff.2 (fun n => (hdm n).prodMk_left)
    filter_upwards [ae_all_iff.2 hac, hmx, Measure.ae_ae_of_ae_prod hds, hdi.prod_right_ae, hcs]
      with x hax hdx hsumx hintx hbase
    intro y hy
    exact (sum_eq_anchor_add_integral hab.le hc hax hdx hsumx hintx hbase hy).2
  have hAm (y : ℝ) (hy : y ∈ Icc a b) : Integrable (A y) μ ∧
      (∫ x, A y x ∂μ) = ∫ t in c..y, G t := integral_interval_swap hD hc hy
  have hνne : ν ≠ 0 := by
    intro hzero
    have hpos : 0 < ν univ := by
      dsimp only [ν]
      rw [Measure.restrict_apply_univ, Real.volume_Icc]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
    simp [hzero] at hpos
  let : NeZero ν := ⟨hνne⟩
  have hm : ∀ᵐ y ∂ν, AEStronglyMeasurable (S y) μ := by
    exact (ae_all_iff.2 (fun n => (hfm n).prodMk_right)).mono fun y hy =>
      AEStronglyMeasurable.tsum hy
  obtain ⟨y₀, hy₀, hmy₀⟩ := ((ae_restrict_mem measurableSet_Icc).and hm).exists
  have hSm : AEStronglyMeasurable (S c) μ := by
    refine (hmy₀.sub (hAm y₀ hy₀).1.aestronglyMeasurable).congr ?_
    filter_upwards [hpoint] with x hx
    change S y₀ x - A y₀ x = S c x
    rw [hx y₀ hy₀, add_sub_cancel_right]
  have hSi : Integrable (S c) μ := hci.mono' hSm
    (hcs.mono fun _ hx => norm_tsum_le_tsum_norm hx)
  let F (y : ℝ) := (∫ x, S c x ∂μ) + ∫ t in c..y, G t
  refine ⟨F, ?_, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact (hSi.add (hAm y hy).1).congr (hpoint.mono fun x hx => (hx y hy).symm)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    change _ = ∫ x, S y x ∂μ
    rw [integral_congr_ae (hpoint.mono fun x hx => hx y hy), integral_add hSi (hAm y hy).1,
      (hAm y hy).2]
  have hGi : IntegrableOn G (Icc a b) volume := hD.integral_prod_right
  have hG : IntervalIntegrable G volume a b :=
    intervalIntegrable_iff.2 (hGi.mono_set (by rw [uIoc_of_le hab.le]; exact Ioc_subset_Icc_self))
  have hF : ∀ᵐ y ∂ν, HasDerivAt F (G y) y := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hG.ae_hasDerivAt_integral]
      with y hy hdy
    rw [← uIcc_of_le hab.le] at hy hc
    exact (hdy hy c hc).const_add (∫ x, S c x ∂μ)
  have hds_swap : ∀ᵐ z : ℝ × α ∂ν.prod μ, Summable (fun n => ‖deriv (f n z.2) z.1‖) :=
    (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae hds
  have hSwapSlice := Measure.ae_ae_of_ae_prod hds_swap
  have hdm_slice := ae_all_iff.2 (fun n => (hdm n).prodMk_right)
  filter_upwards [hF, hSwapSlice, hdm_slice, hdi.prod_left_ae] with y hy hs' hm' hi'
  have hterm := (integrable_series hm' hs' hi').2.2.2.tsum_eq
  change HasDerivAt F (∑' n, ∫ x, deriv (f n x) y ∂μ) y
  rw [hterm]
  exact hy

/-- **Differentiating an integral of a series term by term.** Let $d \in \mathbb{N}$, let $\Omega$
be an open subset of $\mathbb{R}^d$, let $a < c < b$ be real numbers, and for each
$n \in \mathbb{N}$ let $f_n : \mathbb{R}^d \times \mathbb{R} \to \mathbb{C}$ be almost everywhere
measurable on $\Omega \times (a, b)$ with respect to Lebesgue measure. Write
$\partial_y f_n(x, y)$ for the derivative of $t \mapsto f_n(x, t)$ at $y$, taken to be $0$ where
this derivative does not exist, and give every series that does not converge absolutely the
sum $0$. Assume that:
(1) for each $n$ and almost every $x \in \Omega$, the function $y \mapsto f_n(x, y)$ is
absolutely continuous on $[a, b]$;
(2) each $\partial_y f_n$ is almost everywhere measurable on $\Omega \times (a, b)$, the series
$\sum_n |\partial_y f_n(x, y)|$ converges for almost every $(x, y) \in \Omega \times (a, b)$,
and its sum is integrable on $\Omega \times (a, b)$;
(3) the series $\sum_n |f_n(x, c)|$ converges for almost every $x \in \Omega$, and its sum is
integrable on $\Omega$.
Then there is a function $F : \mathbb{R} \to \mathbb{C}$ such that for almost every
$y \in (a, b)$ the function $x \mapsto \sum_n f_n(x, y)$ is integrable on $\Omega$,
$F(y) = \int_\Omega \sum_n f_n(x, y)\, dx$, and $F$ is differentiable at $y$ with
$$
F'(y) = \sum_n \int_\Omega \partial_y f_n(x, y)\, dx.
$$

The joint measurability of each $f_n$ is a hypothesis of the source that the first formalization
dropped. It is needed: for $d \ge 1$ and nonempty bounded $\Omega$, a non-measurable $f_0$ of
modulus one that does not depend on $y$, with $f_n = 0$ for $n \ge 1$, satisfies the other
hypotheses but not the conclusion.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_50.lean` at
openbmb/ma-proofbench@31bab4c, with the change above.
-/
theorem exists_hasDerivAt_integral_tsum_ae
    {d : ℕ} (Ω : Set (Fin d → ℝ)) (hΩ : IsOpen Ω)
    (a b c : ℝ) (hab : a < b) (hac : a < c) (hcb : c < b)
    (f : ℕ → (Fin d → ℝ) → ℝ → ℂ)
    (h_meas : ∀ n : ℕ,
      AEStronglyMeasurable (fun p : (Fin d → ℝ) × ℝ => f n p.1 p.2)
        ((volume.restrict Ω).prod (volume.restrict (Set.Ioo a b))))
    (h_ac : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict Ω),
      AbsolutelyContinuousOnInterval (fun y => f n x y) a b)
    (h_deriv_meas : ∀ n : ℕ,
      AEStronglyMeasurable (fun p : (Fin d → ℝ) × ℝ =>
        deriv (fun y => f n p.1 y) p.2)
        ((volume.restrict Ω).prod (volume.restrict (Set.Ioo a b))))
    (h_deriv_sum_finite_ae :
      ∀ᵐ p ∂((volume.restrict Ω).prod (volume.restrict (Set.Ioo a b))),
        Summable (fun n : ℕ => ‖deriv (fun y => f n p.1 y) p.2‖))
    (h_deriv_int :
      Integrable (fun p : (Fin d → ℝ) × ℝ =>
        ∑' n : ℕ, ‖deriv (fun y => f n p.1 y) p.2‖)
        ((volume.restrict Ω).prod (volume.restrict (Set.Ioo a b))))
    (h_at_c_sum_finite_ae :
      ∀ᵐ x ∂(volume.restrict Ω), Summable (fun n : ℕ => ‖f n x c‖))
    (h_at_c :
      Integrable (fun x : Fin d → ℝ => ∑' n : ℕ, ‖f n x c‖) (volume.restrict Ω)) :
    ∃ F : ℝ → ℂ,
      (∀ᵐ y ∂(volume.restrict (Set.Ioo a b)),
        Integrable (fun x : Fin d → ℝ => ∑' n : ℕ, f n x y) (volume.restrict Ω)) ∧
      (∀ᵐ y ∂(volume.restrict (Set.Ioo a b)),
        F y = ∫ x, ∑' n : ℕ, f n x y ∂(volume.restrict Ω)) ∧
      (∀ᵐ y ∂(volume.restrict (Set.Ioo a b)),
        HasDerivAt F (∑' n : ℕ, ∫ x, deriv (fun t => f n x t) y ∂(volume.restrict Ω)) y) := by
  -- The generalized product-measure argument only needs a sigma-finite spatial measure;
  -- keep the inherited openness hypothesis and the original parameter name.
  have _ : MeasurableSet Ω := hΩ.measurableSet
  have hν : (volume : Measure ℝ).restrict (Ioo a b) = volume.restrict (Icc a b) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc
  rw [hν] at h_meas h_deriv_meas h_deriv_sum_finite_ae h_deriv_int ⊢
  exact exists_integrated_series (volume.restrict Ω) hab ⟨hac.le, hcb.le⟩ f h_meas h_ac
    h_deriv_meas h_deriv_sum_finite_ae h_deriv_int h_at_c_sum_finite_ae h_at_c

end MathlibExt.MeasureTheory.DerivIntegralSeriesAbsContWanted
