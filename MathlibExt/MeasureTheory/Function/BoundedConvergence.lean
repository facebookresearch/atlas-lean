/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Bounded convergence theorem

If a sequence of functions `F n` on a finite measure space is uniformly bounded
(`‖F n a‖ ≤ C` almost everywhere) and converges in measure (i.e. in
probability) to `f`, then the integrals converge: `∫ F n → ∫ f`. In fact the
convergence holds in `L¹`: `∫ ‖F n - f‖ → 0`.

## Source

This formalizes the target "Bounded convergence theorem" (Lecture 5) of
`v1/Atlas/TheoryOfProbability/targets.yaml`: "If `μ` is a probability measure
and `|f_n| ≤ M` a.s. for all `n` and some fixed `M > 0`, and `f_n → f` in
probability, then `∫ f dμ = lim_{n→∞} ∫ f_n dμ`." Two mechanical
generalizations: the measure need only be finite (not a probability measure),
and the functions may take values in any normed space over `ℝ`. The `L¹`
form `tendsto_integral_norm_sub_of_bounded_convergence` is a strengthening
of the book's statement, proved first; the book's integral form follows from
it by the triangle inequality for integrals.

Mathlib's dominated convergence theorem
(`MeasureTheory.tendsto_integral_of_dominated_convergence`) requires almost
everywhere convergence, which does not follow from convergence in measure, so
this is not a restatement of it. The proof uses the subsequence principle:
every subsequence has a further subsequence converging a.e., to which
dominated convergence applies, and `tendsto_of_subseq_tendsto` reassembles
the conclusion. (Mathlib's bounded-convergence results, e.g.
`MeasureTheory.FiniteMeasure.tendsto_lintegral_nn_of_le_const`, are stated
only for bounded continuous `ℝ≥0`-valued functions and `lintegral`, not for
Bochner integrals of normed-space-valued functions converging in measure.)
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace MeasureTheory

/-- If `F n → f` in measure and every `F n` is bounded by `C` almost everywhere,
then `f` is bounded by `C` almost everywhere: along an almost-everywhere
convergent subsequence the bound passes to the limit. -/
private lemma ae_norm_le_of_tendstoInMeasure_of_forall_ae_norm_le
    {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℕ → α → G} {f : α → G} {C : ℝ}
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ C)
    (h_lim : TendstoInMeasure μ F atTop f) :
    ∀ᵐ a ∂μ, ‖f a‖ ≤ C := by
  obtain ⟨ms, -, hms⟩ := h_lim.exists_seq_tendsto_ae
  have hbound_all : ∀ᵐ a ∂μ, ∀ n, ‖F n a‖ ≤ C := by
    rw [ae_all_iff]
    exact h_bound
  filter_upwards [hms, hbound_all] with a ha hb
  exact le_of_tendsto ha.norm (Eventually.of_forall fun n => hb (ms n))

/-- **Bounded convergence theorem, $L^1$ form.** Let $\mu$ be a finite measure on a measurable
space $\alpha$, let $G$ be a real normed space, let $C$ be a real number, and let
$F_n : \alpha \to G$ for $n \in \mathbb{N}$ and $f : \alpha \to G$ be functions. Suppose that each
$F_n$ is almost everywhere strongly measurable, that for every $n$ we have $\|F_n(a)\| \le C$ for
$\mu$-almost every $a$, and that $F_n \to f$ in $\mu$-measure. Then
$\int_\alpha \|F_n(a) - f(a)\| \, d\mu(a) \to 0$ as $n \to \infty$. -/
theorem tendsto_integral_norm_sub_of_bounded_convergence
    {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℕ → α → G} {f : α → G} {C : ℝ}
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ C)
    (h_lim : TendstoInMeasure μ F atTop f) :
    Tendsto (fun n ↦ ∫ a, ‖F n a - f a‖ ∂μ) atTop (𝓝 0) := by
  have hf_meas : AEStronglyMeasurable f μ := h_lim.aestronglyMeasurable hF_meas
  have hf_bound : ∀ᵐ a ∂μ, ‖f a‖ ≤ C :=
    ae_norm_le_of_tendstoInMeasure_of_forall_ae_norm_le h_bound h_lim
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have h_lim_ns : TendstoInMeasure μ (fun n ↦ F (ns n)) atTop f :=
    fun ε hε ↦ (h_lim ε hε).comp hns
  obtain ⟨ms, -, hms_ae⟩ := h_lim_ns.exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hDCT := tendsto_integral_of_dominated_convergence
    (F := fun n a ↦ ‖F (ns (ms n)) a - f a‖) (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ C + C)
    (fun n ↦ ((hF_meas (ns (ms n))).sub hf_meas).norm)
    (integrable_const (C + C))
    (fun n ↦ by
      filter_upwards [h_bound (ns (ms n)), hf_bound] with a ha hb
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact (norm_sub_le _ _).trans (add_le_add ha hb))
    (by
      filter_upwards [hms_ae] with a ha
      have h0 : Tendsto (fun n ↦ ‖F (ns (ms n)) a - f a‖) atTop
          (𝓝 ‖f a - f a‖) :=
        (ha.sub tendsto_const_nhds).norm
      simpa using h0)
  simpa using hDCT

/-- **Bounded convergence theorem.** Let $\mu$ be a finite measure on a measurable space $\alpha$,
let $G$ be a real normed space, let $C$ be a real number, and let $F_n : \alpha \to G$ for
$n \in \mathbb{N}$ and $f : \alpha \to G$ be functions. Suppose that each $F_n$ is almost
everywhere strongly measurable, that for every $n$ we have $\|F_n(a)\| \le C$ for $\mu$-almost
every $a$, and that $F_n \to f$ in $\mu$-measure (in probability). Then
$\int_\alpha F_n \, d\mu \to \int_\alpha f \, d\mu$ as $n \to \infty$. -/
theorem tendsto_integral_of_bounded_convergence
    {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℕ → α → G} {f : α → G} {C : ℝ}
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ C)
    (h_lim : TendstoInMeasure μ F atTop f) :
    Tendsto (fun n ↦ ∫ a, F n a ∂μ) atTop (𝓝 (∫ a, f a ∂μ)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have h_lim_ns : TendstoInMeasure μ (fun n ↦ F (ns n)) atTop f :=
    fun ε hε ↦ (h_lim ε hε).comp hns
  obtain ⟨ms, -, hms_ae⟩ := h_lim_ns.exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  exact tendsto_integral_of_dominated_convergence (fun _ ↦ C)
    (fun n ↦ hF_meas (ns (ms n)))
    (integrable_const C)
    (fun n ↦ h_bound (ns (ms n)))
    hms_ae

end MeasureTheory

end
