/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic.TFAE

/-!
# Scheffé's lemma and uniform integrability

If `f n → g` almost everywhere and the `L¹` norms converge,
`‖f n‖₁ → ‖g‖₁`, then `f n → g` in `L¹`. This is Scheffé's lemma. Combined
with a subsequence argument, the same conclusion holds when a.e. convergence
is weakened to convergence in measure. Since `L¹` convergence implies uniform
integrability (Vitali's theorem, in Mathlib), convergence of the `L¹` norms
together with convergence in measure also implies uniform integrability.

## Source

This formalizes the target "Theorem (Uniform integrability equivalences)"
(Lecture 28) of `v1/Atlas/TheoryOfProbability/targets.yaml`: "If `X_n → X`
in probability then the following are equivalent: (1) `X_n` are uniformly
integrable, (2) `X_n → X` in `L¹`, (3) `E|X_n| → E|X| < ∞`." Its v1
formalization is `v1/Atlas/TheoryOfProbability/code/UIConvergenceEquiv.lean`
(`ui_convergence_equivalences`, fully proved in v1), assembles the equivalence
while reusing Mathlib's Vitali implications. Here the two implications contained in Mathlib's Vitali
convergence theorem (`tendstoInMeasure_iff_tendsto_Lp_finite`) are taken from
Mathlib; the new content is Scheffé's lemma and the
norm-convergence `⇒` `L¹`-convergence implication, which Mathlib does not have.

## Main results

* `MeasureTheory.scheffe_lemma`: a.e. convergence plus convergence of the
  `L¹` norms implies `L¹` convergence.
* `MeasureTheory.tendsto_eLpNorm_one_of_tendstoInMeasure_of_tendsto_eLpNorm`:
  convergence in measure plus convergence of the `L¹` norms implies `L¹`
  convergence.
* `MeasureTheory.uniformIntegrable_of_tendstoInMeasure_of_tendsto_eLpNorm`:
  convergence in measure plus convergence of the `L¹` norms implies uniform
  integrability.
* `MeasureTheory.uniformIntegrable_tfae_of_tendstoInMeasure`: under
  convergence in measure, uniform integrability, `L¹` convergence, and
  convergence of the `L¹` norms are equivalent.
-/

@[expose] public section

open scoped MeasureTheory NNReal ENNReal Topology
open MeasureTheory Filter

namespace MeasureTheory

/-- Squeeze-style lemma in `ℝ≥0∞`: if `b n ≤ a n`, `a n → c < ∞`, and the
liminf of `a n - b n` is at least `c`, then `b n → 0`. -/
private theorem ennreal_tendsto_zero_of_squeeze {a b : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (hba : ∀ n, b n ≤ a n) (ha : Tendsto a atTop (𝓝 c))
    (hc_ne_top : c ≠ ⊤) (h : c ≤ liminf (fun n => a n - b n) atTop) :
    Tendsto b atTop (𝓝 0) := by
  have hab_tendsto : Tendsto (fun n => a n - b n) atTop (𝓝 c) :=
    tendsto_of_le_liminf_of_limsup_le h
      (limsup_le_limsup (Eventually.of_forall fun _ => tsub_le_self)
        ⟨⊥, fun _ _ => bot_le⟩ ha.isBoundedUnder_le |>.trans ha.limsup_eq.le)
  have ha_ne_top : ∀ᶠ n in atTop, a n ≠ ⊤ :=
    (ha.eventually (gt_mem_nhds (lt_top_iff_ne_top.mpr hc_ne_top))).mono fun _ h => h.ne
  rw [show (0 : ℝ≥0∞) = c - c from (tsub_self c).symm]
  exact (ENNReal.Tendsto.sub ha hab_tendsto (.inl hc_ne_top)).congr'
    (ha_ne_top.mono fun n hn => ENNReal.sub_sub_cancel hn (hba n))

/-- Pointwise (a.e.) convergence step in Scheffé's lemma: if `f n → g`
a.e., then the auxiliary quantity
`‖f n‖ₑ + ‖g‖ₑ - ‖f n - g‖ₑ` converges a.e. to `2‖g‖ₑ`. -/
private theorem scheffe_hn_tendsto_ae {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    ∀ᵐ x ∂μ, Tendsto (fun n => ‖f n x‖ₑ + ‖g x‖ₑ - ‖f n x - g x‖ₑ)
      atTop (𝓝 (‖g x‖ₑ + ‖g x‖ₑ)) := by
  filter_upwards [hae] with x hx
  have h1 : Tendsto (fun n => ‖f n x‖ₑ) atTop (𝓝 ‖g x‖ₑ) :=
    (continuous_enorm.tendsto _).comp hx
  have h2 : Tendsto (fun n => ‖f n x - g x‖ₑ) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n => f n x - g x) atTop (𝓝 0) := by
      have := hx.sub (@tendsto_const_nhds _ _ _ (g x) _)
      rwa [sub_self] at this
    have hcomp := (continuous_enorm.tendsto _).comp hsub
    rw [enorm_zero] at hcomp
    exact hcomp
  rw [show ‖g x‖ₑ + ‖g x‖ₑ = (‖g x‖ₑ + ‖g x‖ₑ) - 0 from (tsub_zero _).symm]
  exact ENNReal.Tendsto.sub (h1.add tendsto_const_nhds) h2
    (.inl (ENNReal.add_ne_top.mpr ⟨enorm_ne_top, enorm_ne_top⟩))

/-- Integration identity used in the proof of Scheffé's lemma: the
`lintegral` of the auxiliary quantity equals
`(eLpNorm (f n) 1 μ + eLpNorm g 1 μ) - eLpNorm (f n - g) 1 μ`. -/
private theorem scheffe_lintegral_eq {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
    (hgm : AEStronglyMeasurable g μ)
    (hg : MemLp g 1 μ)
    {n : ℕ} (hfn : eLpNorm (f n) 1 μ < ⊤) :
    ∫⁻ x, (‖f n x‖ₑ + ‖g x‖ₑ - ‖f n x - g x‖ₑ) ∂μ =
      (eLpNorm (f n) 1 μ + eLpNorm g 1 μ) - eLpNorm (f n - g) 1 μ := by
  set ψ : α → ℝ≥0∞ := fun x => ‖f n x - g x‖ₑ
  have hψ_meas : AEMeasurable ψ μ := ((hfm n).sub hgm).enorm
  have hψ_ne_top : ∫⁻ x, ψ x ∂μ ≠ ⊤ := by
    have : (fun x => ‖f n x - g x‖ₑ) = (fun x => ‖(f n - g) x‖ₑ) := by
      ext; simp [Pi.sub_apply]
    rw [this, ← eLpNorm_one_eq_lintegral_enorm ((hfm n).sub hgm)]
    exact ((eLpNorm_sub_le le_rfl).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hfn, hg.eLpNorm_lt_top⟩)).ne
  rw [lintegral_sub' hψ_meas hψ_ne_top (Eventually.of_forall fun x => enorm_sub_le),
      lintegral_add_left' (hfm n).enorm,
      ← eLpNorm_one_eq_lintegral_enorm (f := f n) (hfm n),
      ← eLpNorm_one_eq_lintegral_enorm (f := g) hgm]
  congr 1
  exact (eLpNorm_one_eq_lintegral_enorm ((hfm n).sub hgm)).symm

/-- **Scheffé's lemma.** Let $\mu$ be a measure on a measurable space $\alpha$, let
$f_n : \alpha \to \mathbb{R}$ ($n \in \mathbb{N}$) be $\mu$-almost everywhere strongly measurable,
and let $g : \alpha \to \mathbb{R}$ be in $L^1(\mu)$. Write
$\|h\|_1 = \int |h| \, d\mu \in [0, \infty]$ for the $L^1$ seminorm. If $f_n(x) \to g(x)$ for
$\mu$-almost every $x$ and $\|f_n\|_1 \to \|g\|_1$ in $[0, \infty]$, then $\|f_n - g\|_1 \to 0$,
that is, $f_n \to g$ in $L^1(\mu)$. -/
theorem scheffe_lemma {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : MemLp g 1 μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hnorm : Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 (eLpNorm g 1 μ))) :
    Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0) := by
  have hgm := hg.aestronglyMeasurable
  set hn : ℕ → α → ℝ≥0∞ := fun n x => ‖f n x‖ₑ + ‖g x‖ₑ - ‖f n x - g x‖ₑ
  have hn_tendsto_ae := scheffe_hn_tendsto_ae hae
  have C_le : eLpNorm g 1 μ + eLpNorm g 1 μ ≤ ∫⁻ x, liminf (hn · x) atTop ∂μ :=
    (show eLpNorm g 1 μ + eLpNorm g 1 μ = ∫⁻ x, (‖g x‖ₑ + ‖g x‖ₑ) ∂μ by
      rw [eLpNorm_one_eq_lintegral_enorm hgm, lintegral_add_left' hgm.enorm]).symm ▸
    lintegral_mono_ae (hn_tendsto_ae.mono fun x hx => hx.liminf_eq ▸ le_refl _)
  have h_hn_meas : ∀ n, AEMeasurable (hn n) μ := fun n =>
    ((hfm n).enorm.add hgm.enorm).sub ((hfm n).sub hgm).enorm
  have hfn_lt : ∀ᶠ n in atTop, eLpNorm (f n) 1 μ < ⊤ :=
    hnorm.eventually (gt_mem_nhds (lt_top_iff_ne_top.mpr hg.eLpNorm_lt_top.ne))
  have lintegral_hn_eq : ∀ᶠ n in atTop,
      ∫⁻ x, hn n x ∂μ = (eLpNorm (f n) 1 μ + eLpNorm g 1 μ) - eLpNorm (f n - g) 1 μ := by
    filter_upwards [hfn_lt] with n hfn
    exact scheffe_lintegral_eq hfm hgm hg hfn
  have C_le_liminf : eLpNorm g 1 μ + eLpNorm g 1 μ ≤
      liminf (fun n => (eLpNorm (f n) 1 μ + eLpNorm g 1 μ) - eLpNorm (f n - g) 1 μ) atTop :=
    C_le.trans ((lintegral_liminf_le' h_hn_meas).trans (liminf_congr lintegral_hn_eq).le)
  exact ennreal_tendsto_zero_of_squeeze
    (fun n => eLpNorm_sub_le le_rfl)
    (hnorm.add tendsto_const_nhds)
    (ENNReal.add_ne_top.mpr ⟨hg.eLpNorm_lt_top.ne, hg.eLpNorm_lt_top.ne⟩)
    C_le_liminf

/-- If `f n → g` in `L¹`, then the `L¹` norms converge:
`‖f n‖₁ → ‖g‖₁`. This is the reverse triangle inequality for `eLpNorm`. -/
private theorem tendsto_eLpNorm_of_tendsto_eLpNorm_sub {α : Type*} {m : MeasurableSpace α}
    {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ}
    (hg_ne_top : eLpNorm g 1 μ ≠ ⊤)
    (h : Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 (eLpNorm g 1 μ)) := by
  rw [ENNReal.tendsto_nhds hg_ne_top]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero] at h
  filter_upwards [h ε hε] with n hn
  refine ⟨?_, ?_⟩
  · have h1 : eLpNorm g 1 μ ≤ eLpNorm (f n) 1 μ + ε := by
      calc eLpNorm g 1 μ
          = eLpNorm ((g - f n) + f n) 1 μ := by ring_nf
        _ ≤ eLpNorm (g - f n) 1 μ + eLpNorm (f n) 1 μ :=
            eLpNorm_add_le le_rfl
        _ = eLpNorm (f n - g) 1 μ + eLpNorm (f n) 1 μ := by
            rw [show g - f n = -(f n - g) from by ring, eLpNorm_neg]
        _ ≤ ε + eLpNorm (f n) 1 μ := by gcongr
        _ = eLpNorm (f n) 1 μ + ε := add_comm _ _
    exact tsub_le_iff_right.mpr h1
  · calc eLpNorm (f n) 1 μ
        = eLpNorm ((f n - g) + g) 1 μ := by ring_nf
      _ ≤ eLpNorm (f n - g) 1 μ + eLpNorm g 1 μ :=
          eLpNorm_add_le le_rfl
      _ ≤ ε + eLpNorm g 1 μ := by gcongr
      _ = eLpNorm g 1 μ + ε := add_comm _ _

/-- If `f n → g` in `L¹` and `f n, g` are in `L¹`, then the `eLpNorm`s of
`f n` are uniformly bounded by some `C : ℝ≥0`. -/
private theorem eLpNorm_uniformly_bounded_of_tendsto_eLpNorm_sub {α : Type*}
    {m : MeasurableSpace α} {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, MemLp (f n) 1 μ) (hg : MemLp g 1 μ)
    (hL1 : Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0)) :
    ∃ C : ℝ≥0, ∀ i, eLpNorm (f i) 1 μ ≤ C := by
  rw [ENNReal.tendsto_nhds_zero] at hL1
  obtain ⟨N, hN⟩ := (hL1 1 one_pos).exists_forall_of_atTop
  have hg_ne : eLpNorm g 1 μ ≠ ⊤ := hg.eLpNorm_lt_top.ne
  set Ctail : ℝ≥0 := 1 + (eLpNorm g 1 μ).toNNReal
  set Cinit : ℝ≥0 := (Finset.range N).sup fun n => (eLpNorm (f n) 1 μ).toNNReal
  refine ⟨Cinit ⊔ Ctail, fun i => ?_⟩
  by_cases hi : i < N
  · have h1 : (eLpNorm (f i) 1 μ).toNNReal ≤ Cinit :=
      Finset.le_sup (f := fun n => (eLpNorm (f n) 1 μ).toNNReal) (Finset.mem_range.mpr hi)
    calc eLpNorm (f i) 1 μ
        = ↑((eLpNorm (f i) 1 μ).toNNReal) := (ENNReal.coe_toNNReal (hf i).eLpNorm_lt_top.ne).symm
      _ ≤ ↑Cinit := ENNReal.coe_le_coe.mpr h1
      _ ≤ ↑(Cinit ⊔ Ctail) := ENNReal.coe_le_coe.mpr le_sup_left
  · simp only [not_lt] at hi
    calc eLpNorm (f i) 1 μ
        = eLpNorm ((f i - g) + g) 1 μ := by ring_nf
      _ ≤ eLpNorm (f i - g) 1 μ + eLpNorm g 1 μ :=
          eLpNorm_add_le le_rfl
      _ ≤ 1 + eLpNorm g 1 μ := by gcongr; exact hN i hi
      _ = ↑(1 : ℝ≥0) + ↑((eLpNorm g 1 μ).toNNReal) := by
          rw [ENNReal.coe_toNNReal hg_ne, ENNReal.coe_one]
      _ = ↑Ctail := by push_cast; rfl
      _ ≤ ↑(Cinit ⊔ Ctail) := ENNReal.coe_le_coe.mpr le_sup_right

/-- **Scheffé's lemma for convergence in measure.** Let $\mu$ be a measure on a measurable space
$\alpha$, let $f_n : \alpha \to \mathbb{R}$ ($n \in \mathbb{N}$) and $g : \alpha \to \mathbb{R}$ be
in $L^1(\mu)$, and write $\|h\|_1 = \int |h| \, d\mu$. If $f_n \to g$ in $\mu$-measure (for every
$\varepsilon > 0$, $\mu\{x : |f_n(x) - g(x)| \ge \varepsilon\} \to 0$) and $\|f_n\|_1 \to \|g\|_1$,
then $\|f_n - g\|_1 \to 0$, that is, $f_n \to g$ in $L^1(\mu)$.

The proof applies Scheffé's lemma along a further subsequence, extracted from every subsequence by
convergence in measure. -/
theorem tendsto_eLpNorm_one_of_tendstoInMeasure_of_tendsto_eLpNorm
    {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, MemLp (f n) 1 μ) (hg : MemLp g 1 μ)
    (hfg : TendstoInMeasure μ f atTop g)
    (hnorm : Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 (eLpNorm g 1 μ))) :
    Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hfg_sub : TendstoInMeasure μ (f ∘ ns) atTop g := fun ε hε => (hfg ε hε).comp hns
  obtain ⟨ms, hms_mono, hms_ae⟩ := hfg_sub.exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  exact scheffe_lemma (fun n => (hf (ns (ms n))).aestronglyMeasurable) hg hms_ae
    (hnorm.comp (hns.comp hms_mono.tendsto_atTop))

/-- **Convergence in measure with converging L¹ norms implies uniform integrability.** Let $\mu$
be a measure on a measurable space $\alpha$, let $f_n : \alpha \to \mathbb{R}$ ($n \in \mathbb{N}$)
and $g : \alpha \to \mathbb{R}$ be in $L^1(\mu)$, and write $\|h\|_1 = \int |h| \, d\mu$. If
$f_n \to g$ in $\mu$-measure (for every $\varepsilon > 0$,
$\mu\{x : |f_n(x) - g(x)| \ge \varepsilon\} \to 0$) and $\|f_n\|_1 \to \|g\|_1$, then the family
$(f_n)$ is uniformly integrable: $\sup_n \|f_n\|_1 < \infty$, and the supremum of
$\int_s |f_n| \, d\mu$ over all $n$ and all sets $s \subseteq \alpha$ with $\mu(s) \le \delta$
tends to $0$ as $\delta \to 0$.

The proof combines the $L^1$ convergence $\|f_n - g\|_1 \to 0$ given by Scheffé's lemma for
convergence in measure with the Vitali convergence theorem. -/
theorem uniformIntegrable_of_tendstoInMeasure_of_tendsto_eLpNorm
    {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, MemLp (f n) 1 μ) (hg : MemLp g 1 μ)
    (hfg : TendstoInMeasure μ f atTop g)
    (hnorm : Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 (eLpNorm g 1 μ))) :
    UniformIntegrable f 1 μ := by
  have hL1 := tendsto_eLpNorm_one_of_tendstoInMeasure_of_tendsto_eLpNorm hf hg hfg hnorm
  exact ⟨unifIntegrable_of_tendsto_Lp le_rfl ENNReal.one_ne_top hf hg hL1,
    eLpNorm_uniformly_bounded_of_tendsto_eLpNorm_sub hf hg hL1⟩

/-- **Uniform integrability equivalences.** Let $\mu$ be a finite measure on a measurable space
$\alpha$, let $f_n : \alpha \to \mathbb{R}$ ($n \in \mathbb{N}$) and $g : \alpha \to \mathbb{R}$ be
in $L^1(\mu)$, write $\|h\|_1 = \int |h| \, d\mu$, and suppose that $f_n \to g$ in $\mu$-measure
(for every $\varepsilon > 0$, $\mu\{x : |f_n(x) - g(x)| \ge \varepsilon\} \to 0$). Then the
following are equivalent: (1) the family $(f_n)$ is uniformly integrable, that is,
$\sup_n \|f_n\|_1 < \infty$ and the supremum of $\int_s |f_n| \, d\mu$ over all $n$ and all sets
$s \subseteq \alpha$ with $\mu(s) \le \delta$ tends to $0$ as $\delta \to 0$; (2) $f_n \to g$ in
$L^1(\mu)$, that is, $\|f_n - g\|_1 \to 0$; (3) $\|f_n\|_1 \to \|g\|_1$.

The equivalence of (1) and (2) is the Vitali convergence theorem; (3) implies (2) by Scheffé's
lemma for convergence in measure, and (2) implies (3) by the reverse triangle inequality. -/
theorem uniformIntegrable_tfae_of_tendstoInMeasure
    {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [IsFiniteMeasure μ]
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, MemLp (f n) 1 μ) (hg : MemLp g 1 μ)
    (hfg : TendstoInMeasure μ f atTop g) :
    [UniformIntegrable f 1 μ,
     Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0),
     Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 (eLpNorm g 1 μ))].TFAE := by
  tfae_have 1 → 2 := fun hUI =>
    tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
      (fun n => (hf n).aestronglyMeasurable) hg hUI.unifIntegrable hfg
  tfae_have 2 → 1 := fun hL1 =>
    ⟨unifIntegrable_of_tendsto_Lp le_rfl ENNReal.one_ne_top hf hg hL1,
     eLpNorm_uniformly_bounded_of_tendsto_eLpNorm_sub hf hg hL1⟩
  tfae_have 2 → 3 := fun hL1 =>
    tendsto_eLpNorm_of_tendsto_eLpNorm_sub hg.eLpNorm_lt_top.ne hL1
  tfae_have 3 → 2 := fun hnorm =>
    tendsto_eLpNorm_one_of_tendstoInMeasure_of_tendsto_eLpNorm hf hg hfg hnorm
  tfae_finish

end MeasureTheory
