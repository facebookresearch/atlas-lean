/-
# L^0 metric convergence is convergence in measure

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_07.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. The ATLAS import names the
distance `L0PseudoMetric` and states the result on measurable representatives, on which the
source's metric is a pseudometric. This move retains those definitions, names, statements, and
docstrings, supplies the proof, and narrows the imports.
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith

/-! # The unit-interval L⁰ pseudometric and convergence in measure -/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace MathlibExt.MeasureTheory.L0MetricTendstoInMeasureWanted

/-- **Measurable functions representing $L^0([0,1])$.** The type of Borel measurable functions
$f : \mathbb{R} \to \mathbb{R}$, used as representatives of the elements of $L^0([0,1])$.

The pseudometric and the convergence in measure built on them depend only on the restriction
of $f$ to $[0,1]$ up to a null set.
-/
abbrev L0UnitInterval : Type := {f : ℝ → ℝ // Measurable f}

/-- **The $L^0$ pseudometric on $[0,1]$.** For Borel measurable functions
$f, g : \mathbb{R} \to \mathbb{R}$,
$$
d(f,g) = \int_{[0,1]} \frac{|f(x) - g(x)|}{1 + |f(x) - g(x)|}\,dx,
$$
the integral being with respect to Lebesgue measure on $[0,1]$.

This is a pseudometric: functions that agree almost everywhere on $[0,1]$ are at distance $0$,
and on the almost-everywhere classes it is the usual metric of $L^0([0,1])$.
-/
noncomputable def L0PseudoMetric (f g : L0UnitInterval) : ℝ :=
  ∫ x, |f.1 x - g.1 x| / (1 + |f.1 x - g.1 x|)
    ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))

/-- **Convergence in the $L^0$ pseudometric is convergence in measure.** Let $f$ and
$f_0, f_1, f_2, \ldots$ be Borel measurable functions $\mathbb{R} \to \mathbb{R}$, and let $d$ be
the pseudometric
$$
d(g,h) = \int_{[0,1]} \frac{|g(x) - h(x)|}{1 + |g(x) - h(x)|}\,dx
$$
on such functions, the integral being with respect to Lebesgue measure. Then
$d(f_n, f) \to 0$ as $n \to \infty$ if and only if $f_n \to f$ in measure with respect to
Lebesgue measure on $[0,1]$: for every $\varepsilon > 0$, the Lebesgue measure of
$\{x \in [0,1] : |f_n(x) - f(x)| \ge \varepsilon\}$ tends to $0$ as $n \to \infty$.

The source states this for $L^0([0,1])$, on which $d$ is a metric; here it is stated for
representatives, on which $d$ is only a pseudometric. Both sides depend only on the
almost-everywhere classes of the functions on $[0,1]$, so the two statements say the same thing.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_07.lean` at
openbmb/ma-proofbench@31bab4c, with the change above.
-/
theorem tendsto_L0PseudoMetric_zero_iff_tendstoInMeasure
    (fSeq : ℕ → L0UnitInterval) (f : L0UnitInterval) :
    Filter.Tendsto (fun n => L0PseudoMetric (fSeq n) f) Filter.atTop (𝓝 (0 : ℝ)) ↔
      MeasureTheory.TendstoInMeasure
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
        (fun n x => (fSeq n).1 x) Filter.atTop (fun x => f.1 x) := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 (by simp [Real.volume_Icc])
  let u (n : ℕ) (x : ℝ) := |(fSeq n).1 x - f.1 x| / (1 + |(fSeq n).1 x - f.1 x|)
  have hu_meas (n : ℕ) : Measurable (u n) := by
    have h : Measurable (fun x : ℝ => |(fSeq n).1 x - f.1 x|) :=
      continuous_abs.measurable.comp ((fSeq n).2.sub f.2)
    exact h.div (measurable_const.add h)
  have hnonneg (n : ℕ) (x : ℝ) : 0 ≤ u n x := by
    dsimp [u]
    positivity
  have hbound (n : ℕ) (x : ℝ) : ‖u n x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hnonneg n x)]
    dsimp [u]
    exact (div_le_iff₀ (by positivity)).2 (by linarith)
  change Tendsto (fun n => ∫ x, u n x ∂μ) atTop (𝓝 0) ↔
    TendstoInMeasure μ (fun n x => (fSeq n).1 x) atTop (fun x => f.1 x)
  constructor
  · intro h
    have hu_int (n : ℕ) : Integrable (u n) μ :=
      (integrable_const (1 : ℝ)).mono (hu_meas n).aestronglyMeasurable
        (Eventually.of_forall fun x => by simpa using hbound n x)
    have hu_norm (n : ℕ) : eLpNorm (u n) 1 μ = ENNReal.ofReal (∫ x, u n x ∂μ) := by
      rw [eLpNorm_one_eq_lintegral_eNorm (hu_meas n).aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_eNorm (hu_int n)]
      congr 1
      exact integral_congr_ae (Eventually.of_forall fun x => Real.norm_of_nonneg (hnonneg n x))
    have hu_tendsto : TendstoInMeasure μ u atTop (0 : ℝ → ℝ) := by
      apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
      simpa [hu_norm] using ENNReal.tendsto_ofReal h
    rw [tendstoInMeasure_iff_measureReal_norm] at hu_tendsto ⊢
    intro ε hε
    let δ := ε / (1 + ε)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hu_tendsto δ hδ)
      (fun _ => measureReal_nonneg) fun n => ?_
    refine measureReal_mono ?_ (measure_ne_top μ _)
    intro x hx
    change ε ≤ ‖(fSeq n).1 x - f.1 x‖ at hx
    change δ ≤ ‖u n x - 0‖
    rw [sub_zero, Real.norm_of_nonneg (hnonneg n x)]
    rw [Real.norm_eq_abs] at hx
    dsimp [δ, u]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith only [hx]
  · intro h
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ms, -, hlim⟩ := (h.comp hns).exists_seq_tendsto_ae
    refine ⟨ms, ?_⟩
    have hsub : ∀ᵐ x ∂μ, Tendsto (fun n => u (ns (ms n)) x) atTop (𝓝 (0 : ℝ)) := by
      filter_upwards [hlim] with x hx
      have ha : Tendsto (fun n => |(fSeq (ns (ms n))).1 x - f.1 x|) atTop (𝓝 (0 : ℝ)) := by
        simpa using (hx.sub_const (f.1 x)).abs
      have hden : Tendsto (fun n => 1 + |(fSeq (ns (ms n))).1 x - f.1 x|) atTop (𝓝 1) := by
        simpa using ha.const_add (1 : ℝ)
      have hq := ha.div hden one_ne_zero
      rw [zero_div] at hq
      refine hq.congr' (Eventually.of_forall fun n => ?_)
      simp only [Pi.div_apply, u]
    simpa only [integral_zero] using
      tendsto_integral_of_dominated_convergence (μ := μ) (f := fun _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (fun n => (hu_meas (ns (ms n))).aestronglyMeasurable)
        (integrable_const 1) (fun n => Eventually.of_forall (hbound (ns (ms n)))) hsub

end MathlibExt.MeasureTheory.L0MetricTendstoInMeasureWanted
