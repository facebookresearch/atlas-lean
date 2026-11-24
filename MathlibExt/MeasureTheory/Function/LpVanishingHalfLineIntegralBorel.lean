/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Lp functions with integral over [0,L] tending to 0 form a Borel set

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_25.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l2_25 … := by sorry` into the Batteries `theorem_wanted`
`measurableSet_vanishingIntegralSet`; moved the informal problem statement docstring onto it and
placed the declarations in namespace
`MathlibExt.MeasureTheory.LpVanishingHalfLineIntegralBorelWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system; added docstrings to helper definitions.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity

/-! # The Borel set of functions with vanishing half-line integrals -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace MathlibExt.MeasureTheory.LpVanishingHalfLineIntegralBorelWanted

/-- **Functions with vanishing integrals over $[0, L]$.** For $0 \le p \le \infty$, this is the set
of real-valued $f \in L^p(\mathbb{R})$ (with respect to Lebesgue measure) such that
$\int_{[0, L]} f(x)\,dx \to 0$ as $L \to +\infty$, where the integral of a function that is not
integrable on $[0, L]$ counts as $0$. -/
def vanishingIntegralSet (p : ENNReal) : Set (Lp ℝ p (volume : Measure ℝ)) :=
  {f |
    Tendsto
      (fun L : ℝ => ∫ x in Set.Icc (0 : ℝ) L, f x ∂(volume : Measure ℝ))
      atTop (nhds 0)}

private theorem lp_integrableOn_finite {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℝ p (volume : Measure ℝ)) {s : Set ℝ} (hs : volume s < ∞) :
    IntegrableOn f s volume := by
  let : IsFiniteMeasure ((volume : Measure ℝ).restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hs⟩
  exact ((Lp.memLp f).restrict s).integrable (Fact.out : 1 ≤ p)

private theorem continuous_lp_setIntegral {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {s : Set ℝ} (hs : volume s < ∞) :
    Continuous (fun f : Lp ℝ p (volume : Measure ℝ) => ∫ x in s, f x ∂volume) := by
  let ν := (volume : Measure ℝ).restrict s
  let I : Lp ℝ p (volume : Measure ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∫ x, f x ∂ν
      map_add' := fun f g =>
        (integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add f g))).trans
          (integral_add (lp_integrableOn_finite f hs) (lp_integrableOn_finite g hs))
      map_smul' := fun c f =>
        (integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul c f))).trans (integral_smul c f) }
  let C : ℝ≥0∞ := volume s ^ (1 - 1 / p.toReal)
  have hexp : 0 ≤ 1 - 1 / p.toReal := by
    by_cases hp : p = ∞
    · simp [hp]
    · have hp' : (1 : ℝ) ≤ p.toReal := by
        simpa using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
      exact sub_nonneg.mpr ((div_le_one (zero_lt_one.trans_le hp')).mpr hp')
  have hC : C ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hexp hs.ne
  have hbound (f : Lp ℝ p (volume : Measure ℝ)) : ‖I f‖ ≤ C.toReal * ‖f‖ := by
    have hf := (Lp.memLp f).aestronglyMeasurable
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν) (Fact.out : 1 ≤ p)
      (f := (f : ℝ → ℝ)) hf.restrict
    change eLpNorm f 1 ν ≤ eLpNorm f p ν * ν univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) at h
    dsimp [ν] at h
    rw [Measure.restrict_apply_univ, div_one] at h
    have hn : eLpNorm f p ν ≤ eLpNorm f p volume :=
      eLpNorm_mono_measure (f : ℝ → ℝ) Measure.restrict_le_self
    calc
      ‖I f‖ ≤ ∫ x, ‖f x‖ ∂ν := norm_integral_le_integral_norm _
      _ = (eLpNorm f 1 ν).toReal := by
        rw [integral_norm_eq_lintegral_eNorm hf.restrict,
          eLpNorm_one_eq_lintegral_eNorm hf.restrict]
      _ ≤ C.toReal * ‖f‖ := by
        rw [Lp.norm_def, mul_comm, ← ENNReal.toReal_mul]
        exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) hC)
          (h.trans (mul_le_mul' hn le_rfl))
  exact (I.mkContinuous C.toReal hbound).continuous

private theorem continuous_lp_integral_endpoint {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℝ p (volume : Measure ℝ)) :
    Continuous (fun L : ℝ => ∫ x in Icc 0 L, f x ∂volume) := by
  have hprim : Continuous (fun L : ℝ => ∫ x in (0 : ℝ)..L, f x ∂volume) :=
    intervalIntegral.continuous_primitive (fun a b => by
      have hfin : (volume : Measure ℝ) (uIcc a b) < ∞ := isCompact_uIcc.measure_lt_top
      exact (lp_integrableOn_finite f hfin).intervalIntegrable) 0
  have heq (L : ℝ) : (∫ x in Icc 0 L, f x ∂volume) = ∫ x in (0 : ℝ)..max 0 L, f x ∂volume := by
    by_cases hL : 0 ≤ L
    · rw [max_eq_right hL, intervalIntegral.integral_of_le hL, integral_Icc_eq_integral_Ioc]
    · have hneg := lt_of_not_ge hL
      rw [Icc_eq_empty_of_lt hneg, setIntegral_empty, max_eq_left hneg.le,
        intervalIntegral.integral_same]
  rw [show (fun L : ℝ => ∫ x in Icc 0 L, f x ∂volume) = _ from funext heq]
  exact hprim.comp (continuous_const.max continuous_id)

/-- **$L^p$ functions whose integrals over $[0, L]$ tend to $0$ form a Borel set.** Let
$1 \le p \le \infty$. The set of real-valued $f \in L^p(\mathbb{R})$ (with respect to Lebesgue
measure) such that $\int_0^L f(x)\,dx \to 0$ as $L \to +\infty$ is a Borel subset of
$L^p(\mathbb{R})$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration; Set
functions, measures and integrals with values in abstract spaces),
`benchmark/level2/ma_proofbench_l2_25.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem measurableSet_vanishingIntegralSet
    (p : ENNReal)
    [Fact ((1 : ENNReal) ≤ p)] :
    @MeasurableSet (Lp ℝ p (volume : Measure ℝ))
      (borel (Lp ℝ p (volume : Measure ℝ)))
      (vanishingIntegralSet p) := by
  let radius (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  let S (k N : ℕ) (q : ℚ) := {f : Lp ℝ p (volume : Measure ℝ) |
    (N : ℝ) < (q : ℝ) → |∫ x in Icc 0 (q : ℝ), f x ∂volume| ≤ radius k}
  -- Rational endpoints suffice: a strict violation at a real endpoint would persist on an
  -- open set and hence also occur at a rational endpoint beyond the same cutoff.
  have heq : vanishingIntegralSet p = ⋂ k, ⋃ N, ⋂ q, S k N q := by
    ext f
    simp only [vanishingIntegralSet, mem_ofPred_eq, mem_iInter, mem_iUnion, S]
    rw [Metric.tendsto_nhds]
    simp only [Real.dist_eq, sub_zero]
    constructor
    · intro h k
      have hpos : 0 < radius k := by dsimp [radius]; positivity
      obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (h _ hpos)
      obtain ⟨N, hN⟩ := exists_nat_ge L₀
      exact ⟨N, fun q hq => (hL₀ _ (hN.trans hq.le)).le⟩
    · intro h ε hε
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      obtain ⟨N, hN⟩ := h k
      refine (eventually_gt_atTop (N : ℝ)).mono fun L hL => lt_of_le_of_lt ?_ hk
      by_contra hle
      let U := {t : ℝ | (N : ℝ) < t} ∩ {t : ℝ | radius k < |∫ x in Icc 0 t, f x ∂volume|}
      have hU : IsOpen U := (isOpen_lt continuous_const continuous_id).inter
        (isOpen_lt continuous_const (continuous_lp_integral_endpoint f).abs)
      obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open hU ⟨L, hL, lt_of_not_ge hle⟩
      exact hq.2.not_ge (hN q hq.1)
  let : MeasurableSpace (Lp ℝ p (volume : Measure ℝ)) := borel _
  let : BorelSpace (Lp ℝ p (volume : Measure ℝ)) := ⟨rfl⟩
  rw [heq]
  refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun N =>
    MeasurableSet.iInter fun q => ?_
  by_cases hq : (N : ℝ) < (q : ℝ)
  · have hc := continuous_lp_setIntegral (p := p) (isCompact_Icc (a := (0 : ℝ))
        (b := (q : ℝ))).measure_lt_top
    have hs : IsClosed (S k N q) := by
      simpa only [S, hq, true_implies] using isClosed_le hc.abs
        (continuous_const : Continuous fun _ : Lp ℝ p (volume : Measure ℝ) => radius k)
    exact hs.measurableSet
  · have hs : S k N q = univ := by
      ext f
      exact ⟨fun _ => trivial, fun _ h => (hq h).elim⟩
    rw [hs]
    exact MeasurableSet.univ

end MathlibExt.MeasureTheory.LpVanishingHalfLineIntegralBorelWanted
