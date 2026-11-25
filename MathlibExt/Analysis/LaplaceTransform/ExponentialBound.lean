/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.ExpDecay
public import MathlibExt.Analysis.LaplaceTransform.Basic

/-!
# Laplace convergence and holomorphy from exponential bounds

Let `f : ℝ → E` satisfy `‖f t‖ ≤ C * Real.exp (a * t)` for `t ≥ 0`.
This file shows Laplace convergence for `s.re > a` and holomorphy on
`{s | a < s.re}`. Measurability on `volume.restrict (Set.Ioi 0)` is an
explicit hypothesis: Lean's totalized integral would otherwise make the
Laplace integral vanish on the nonmeasurable branch, giving vacuous
holomorphy. Only the genuine measurable branch is proved here.

## ATLAS source correspondence

ATLAS item `NumberTheoryI:N320` (ATLAS Definition 16.9), defined in
`Atlas/NumberTheoryI/targets.yaml` (lines 2242--2248), with implementation/proof
context in `Atlas/NumberTheoryI/code/LaplaceTransform.lean` (lines 15--16) and
`Atlas/NumberTheoryI/code/PNT.lean` (lines 314--444). Authored by Muse Spark 1.3.

The motivating source is Andrew V. Sutherland, *18.785 Number Theory I*, Lecture 16,
[Lemma 16.10](https://math.mit.edu/classes/18.785/2021fa/LectureNotes16.pdf#page=6).
It invokes Definition 16.9: if a real-valued function has exponential growth
`h(t) = O(exp(c t))`, then its positive-ray Laplace transform is holomorphic on
`Re(s) > c`.  For `h(t) = ϑ(exp t)`, Lemma 16.7 supplies `h(t) = O(exp t)`,
giving holomorphy on `Re(s) > 1`.

Source-to-API map: ATLAS N320 is implemented by
`laplaceConvergent_of_isBigO_exp` (convergence for `a < s.re`) and
`differentiableOn_laplace_of_isBigO_exp` (holomorphy on `{s | a < s.re}`).
These two APIs together are not a literal full target; they are a corrected,
strengthened-premise formalization of N320's intended convergence/holomorphy
claim. Both carry the strengthened assumption `LocallyIntegrableOn f (Set.Ici 0)`,
which explicitly repairs the missing endpoint condition, since the source's
open-positive-ray (piecewise continuity on `ℝ_{>0}`) wording does not control the
singularity at zero. This is not a literal proof of the under-specified source
wording.

The public theorems below isolate and strengthen precisely that analytic step.

* `laplaceConvergent_of_norm_le_exp` replaces big-O notation by an explicit bound
  `‖f t‖ ≤ C exp(a t)` for `t ≥ 0` and proves convergence whenever `a < s.re`.
* `differentiableOn_laplace_of_norm_le_exp` proves holomorphy on the full half-plane
  `{s | a < s.re}` by dominated differentiation.
* `laplaceConvergent_of_isBigO_exp` and `differentiableOn_laplace_of_isBigO_exp`
  are the source-shaped endpoints: from `LocallyIntegrableOn f (Set.Ici 0)` and an
  eventual bound `f =O[atTop] exp (a * t)` they prove convergence and holomorphy.
  The `Ici 0` hypothesis does not restate the source: ATLAS's piecewise continuity
  on `ℝ_{>0}` does not supply near-zero integrability. The counterexample
  `f(t) = 1/t` is piecewise continuous (indeed continuous) on `ℝ_{>0}`, locally
  integrable on `(0, ∞)`, and `O(1)` at infinity, but not integrable at `0`, so
  the open-ray wording alone would be insufficient.

The Lean result allows Banach-space-valued functions `f : ℝ → E`, a genuine
generalization of the source's real-valued statement.  It explicitly assumes
`AEStronglyMeasurable f` on `Set.Ioi 0`, whereas the source's piecewise continuity
implies this measurability.  The positive ray and strict half-plane are unchanged.
The separate prime-sum identity in Lemma 16.10 is handled in `LaplaceTheta`; this module
provides its exponential-bound/holomorphy input.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private lemma integrableOn_mul_exp_neg_Ioi' {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-r * t))
      (Set.Ioi (0 : ℝ)) := by
  have hr2 : (0 : ℝ) < r / 2 := by linarith
  apply integrable_of_isBigO_exp_neg hr2
  · exact (continuous_id.mul
      (Real.continuous_exp.comp
        (continuous_const.mul continuous_id'))).continuousOn
  · rw [Asymptotics.isBigO_iff]
    use 2 / r
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ht (Real.exp_nonneg _))]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hle : t ≤ (2 / r) * Real.exp (r / 2 * t) :=
      calc t = (2 / r) * (r / 2 * t) := by field_simp
        _ ≤ (2 / r) * Real.exp (r / 2 * t) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith [Real.add_one_le_exp (r / 2 * t)]
    calc t * Real.exp (-r * t)
        = t * (Real.exp (-(r / 2) * t) *
          Real.exp (-(r / 2) * t)) := by
          rw [← Real.exp_add]
          congr 1
          ring_nf
      _ ≤ (2 / r) * Real.exp (r / 2 * t) *
            (Real.exp (-(r / 2) * t) *
              Real.exp (-(r / 2) * t)) := by
          apply mul_le_mul_of_nonneg_right hle
          exact mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = (2 / r) * (Real.exp (r / 2 * t) *
            Real.exp (-(r / 2) * t)) *
            Real.exp (-(r / 2) * t) := by ring
      _ = 2 / r * Real.exp (-(r / 2) * t) := by
          rw [← Real.exp_add]
          simp only [neg_mul, add_neg_cancel, Real.exp_zero]
          ring

/-- **Convergence of the Laplace transform under an exponential bound.** Let $E$ be a complex
normed space, $f : \mathbb{R} \to E$ almost everywhere strongly measurable on $(0, \infty)$, and
$a, C \in \mathbb{R}$ with $C \ge 0$ such that $\|f(t)\| \le C e^{a t}$ for all $t \ge 0$. Then for
every $s \in \mathbb{C}$ with $\operatorname{Re} s > a$ the Laplace transform of $f$ converges at
$s$, that is, $t \mapsto e^{-st} f(t)$ is integrable on $(0, \infty)$. -/
theorem laplaceConvergent_of_norm_le_exp
    (f : ℝ → E) (a C : ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)))
    (hC : 0 ≤ C)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ C * Real.exp (a * t))
    {s : ℂ} (hs : a < s.re) :
    LaplaceConvergent f s := by
  unfold LaplaceConvergent
  have hpos : 0 < s.re - a := sub_pos.mpr hs
  have hbound_int :
      IntegrableOn (fun t : ℝ => C * Real.exp (-(s.re - a) * t))
        (Set.Ioi (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi 0 hpos).const_mul C
  have hexp : AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-s * (t : ℂ)))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • f t)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hexp.smul hf
  apply Integrable.mono hbound_int hmeas
  rw [ae_restrict_iff' measurableSet_Ioi]
  apply ae_of_all
  intro t ht
  simp only [Set.mem_Ioi] at ht
  rw [norm_smul, Complex.norm_exp]
  have hre : (-s * (t : ℂ)).re = -s.re * t := by
    simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
  rw [hre]
  calc Real.exp (-s.re * t) * ‖f t‖
      ≤ Real.exp (-s.re * t) * (C * Real.exp (a * t)) :=
        mul_le_mul_of_nonneg_left (hbound t (le_of_lt ht))
          (Real.exp_nonneg _)
    _ = C * Real.exp (-(s.re - a) * t) := by
        rw [show -(s.re - a) * t = -s.re * t + a * t from by ring]
        rw [Real.exp_add]
        ring
    _ ≤ ‖C * Real.exp (-(s.re - a) * t)‖ := by
        rw [Real.norm_of_nonneg
          (mul_nonneg hC (Real.exp_nonneg _))]

/-- **Convergence of the Laplace transform under exponential growth.** Let $E$ be a complex
normed space, $a \in \mathbb{R}$, and $f : \mathbb{R} \to E$ locally integrable on $[0, \infty)$
with $\|f(t)\| = O(e^{a t})$ as $t \to \infty$. Then for every $s \in \mathbb{C}$ with
$\operatorname{Re} s > a$ the Laplace transform of $f$ converges at $s$, that is,
$t \mapsto e^{-st} f(t)$ is integrable on $(0, \infty)$.

Local integrability on $[0, \infty)$, not only on $(0, \infty)$, is needed: $f(t) = 1/t$ is
continuous on $(0, \infty)$ and bounded at infinity, but not integrable near $0$.

Source: ATLAS NumberTheoryI N320 (Sutherland, 18.785 Number Theory I, Lecture 16); a corrected,
strengthened-premise formalization of the intended convergence claim, since the source's piecewise
continuity on the open ray does not give integrability near 0. This is not a literal proof of the
under-specified source wording. -/
theorem laplaceConvergent_of_isBigO_exp
    (f : ℝ → E) (a : ℝ)
    (hloc : LocallyIntegrableOn f (Set.Ici 0))
    (ho : f =O[Filter.atTop] (fun t : ℝ => Real.exp (a * t)))
    {s : ℂ} (hs : a < s.re) :
    LaplaceConvergent f s := by
  unfold LaplaceConvergent
  set r : ℝ := s.re - a with hr_def
  have hr : 0 < r := sub_pos.mpr hs
  have hcont_exp : Continuous (fun t : ℝ => Complex.exp (-s * (t : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hF_loc : LocallyIntegrableOn
      (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • f t) (Set.Ici 0) :=
    hloc.continuousOn_smul isClosed_Ici.isLocallyClosed hcont_exp.continuousOn
  have hg_ioi : IntegrableOn (fun t : ℝ => Real.exp (-r * t))
      (Set.Ioi (0 : ℝ)) :=
    exp_neg_integrableOn_Ioi 0 hr
  have htail : IntegrableAtFilter (fun t : ℝ => Real.exp (-r * t))
      Filter.atTop volume :=
    (integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp hg_ioi).1
  have hbig : (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • f t)
      =O[Filter.atTop] (fun t : ℝ => Real.exp (-r * t)) := by
    rw [Asymptotics.isBigO_iff] at ho ⊢
    obtain ⟨C, hC⟩ := ho
    refine ⟨C, ?_⟩
    filter_upwards [hC] with t ht
    rw [norm_smul, Complex.norm_exp]
    have hre : (-s * (t : ℂ)).re = -s.re * t := by
      simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [hre]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at ht
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-s.re * t) * ‖f t‖
        ≤ Real.exp (-s.re * t) * (C * Real.exp (a * t)) :=
          mul_le_mul_of_nonneg_left ht (Real.exp_nonneg _)
      _ = C * Real.exp (-r * t) := by
          rw [hr_def, show -((s.re - a)) * t = -s.re * t + a * t from by ring]
          rw [Real.exp_add]
          ring
  have hIci : IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • f t)
      (Set.Ici (0 : ℝ)) :=
    hF_loc.integrableOn_of_isBigO_atTop hbig htail
  exact hIci.mono_set Set.Ioi_subset_Ici_self

/-- **Holomorphy of the Laplace transform under an exponential bound.** Let $E$ be a complex
Banach space, $f : \mathbb{R} \to E$ almost everywhere strongly measurable on $(0, \infty)$, and
$a, C \in \mathbb{R}$ with $C \ge 0$ such that $\|f(t)\| \le C e^{a t}$ for all $t \ge 0$. Then the
Laplace transform $s \mapsto \int_{(0, \infty)} e^{-st} f(t)\,dt$ is complex differentiable at
every point of the half-plane $\{s \in \mathbb{C} : \operatorname{Re} s > a\}$. -/
theorem differentiableOn_laplace_of_norm_le_exp
    (f : ℝ → E) (a C : ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)))
    (hC : 0 ≤ C)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ C * Real.exp (a * t))
    [CompleteSpace E] :
    DifferentiableOn ℂ (laplace f) {s | a < s.re} := by
  intro s₀ hs₀
  simp only [Set.mem_ofPred_eq] at hs₀
  set μ := volume.restrict (Set.Ioi (0 : ℝ)) with hμ_def
  set δ := (s₀.re - a) / 2 with hδ_def
  set b := (s₀.re + a) / 2 with hb_def
  have hδ : 0 < δ := by
    simp only [hδ_def]
    linarith
  have hba : 0 < b - a := by
    simp only [hb_def]
    linarith
  have hball_re : ∀ z ∈ Metric.ball s₀ δ, b ≤ z.re := by
    intro z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have habs_re : |z.re - s₀.re| ≤ ‖z - s₀‖ := by
      rw [← Complex.sub_re]
      exact Complex.abs_re_le_norm _
    have hlt : |z.re - s₀.re| < δ := lt_of_le_of_lt habs_re hz
    have hmem := abs_lt.mp hlt
    simp only [hb_def, hδ_def] at hmem ⊢
    linarith [hmem.1, hmem.2]
  have hmeas_F : ∀ z : ℂ, AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-z * (t : ℂ)) • f t) μ := by
    intro z
    have hexp : AEStronglyMeasurable
        (fun t : ℝ => Complex.exp (-z * (t : ℂ)))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      apply Continuous.aestronglyMeasurable
      exact Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)
    rw [hμ_def]
    exact hexp.smul hf
  have hF_int : Integrable
      (fun t : ℝ => Complex.exp (-s₀ * (t : ℂ)) • f t) μ := by
    have hconv := laplaceConvergent_of_norm_le_exp f a C hf hC hbound
      (show a < s₀.re from hs₀)
    unfold LaplaceConvergent at hconv
    rw [hμ_def]
    exact hconv
  have hmeas_deriv : AEStronglyMeasurable
      (fun t : ℝ => (-(t : ℂ) * Complex.exp (-s₀ * (t : ℂ))) • f t)
      μ := by
    have hcont : Continuous
        (fun t : ℝ => (-(t : ℂ) * Complex.exp (-s₀ * (t : ℂ))) :
          ℝ → ℂ) := by
      apply Continuous.mul
      · exact Complex.continuous_ofReal.neg
      · exact Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)
    rw [hμ_def]
    exact hcont.aestronglyMeasurable.smul hf
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ)
    (F := fun (s : ℂ) (t : ℝ) => Complex.exp (-s * (t : ℂ)) • f t)
    (F' := fun (s : ℂ) (t : ℝ) =>
      (-(t : ℂ) * Complex.exp (-s * (t : ℂ))) • f t)
    (bound := fun t : ℝ => C * |t| * Real.exp (-(b - a) * t))
    (s := Metric.ball s₀ δ)
    (x₀ := s₀)
    (Metric.ball_mem_nhds s₀ hδ)
    (Filter.Eventually.of_forall (fun z => hmeas_F z))
    hF_int
    hmeas_deriv
    ?_ ?_ ?_
  · exact key.2.differentiableAt.differentiableWithinAt
  · rw [ae_restrict_iff' measurableSet_Ioi]
    apply ae_of_all
    intro t ht z hz
    simp only [Set.mem_Ioi] at ht
    rw [norm_smul, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-z * (t : ℂ)).re = -z.re * t := by
      simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [hre]
    have hht : ‖f t‖ ≤ C * Real.exp (a * t) := hbound t (le_of_lt ht)
    have hb : b ≤ z.re := hball_re z hz
    calc |t| * Real.exp (-z.re * t) * ‖f t‖
        ≤ |t| * Real.exp (-b * t) * ‖f t‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp_of_le
              (mul_le_mul_of_nonneg_right (neg_le_neg hb)
                (le_of_lt ht)))
            (abs_nonneg t)
      _ ≤ |t| * Real.exp (-b * t) * (C * Real.exp (a * t)) := by
          apply mul_le_mul_of_nonneg_left hht
          exact mul_nonneg (abs_nonneg t) (Real.exp_nonneg _)
      _ = C * |t| * Real.exp (-(b - a) * t) := by
          rw [show -(b - a) * t = -b * t + a * t from by ring]
          rw [Real.exp_add]
          ring
  · rw [hμ_def]
    change IntegrableOn
      (fun t : ℝ => C * |t| * Real.exp (-(b - a) * t))
      (Set.Ioi (0 : ℝ))
    have h1 : IntegrableOn
        (fun t : ℝ => C * (t * Real.exp (-(b - a) * t)))
        (Set.Ioi (0 : ℝ)) :=
      (integrableOn_mul_exp_neg_Ioi' hba).const_mul C
    apply h1.congr_fun _ measurableSet_Ioi
    intro t ht
    simp only [Set.mem_Ioi] at ht
    change C * (t * Real.exp (-(b - a) * t)) =
      C * |t| * Real.exp (-(b - a) * t)
    rw [abs_of_pos ht]
    ring
  · apply ae_of_all
    intro t z _
    have h1 : HasDerivAt (fun s : ℂ => -s * (t : ℂ)) (-(t : ℂ)) z := by
      have hder := (hasDerivAt_neg (𝕜 := ℂ) z).mul_const (t : ℂ)
      simp only [neg_one_mul] at hder
      exact hder
    have h2 := h1.cexp.smul_const (f t)
    have heq : Complex.exp (-z * (t : ℂ)) * (-(t : ℂ)) =
        -(t : ℂ) * Complex.exp (-z * (t : ℂ)) := mul_comm _ _
    rw [heq] at h2
    exact h2

/-- **Holomorphy of the Laplace transform under exponential growth.** Let $E$ be a complex
Banach space, $a \in \mathbb{R}$, and $f : \mathbb{R} \to E$ locally integrable on $[0, \infty)$
with $\|f(t)\| = O(e^{a t})$ as $t \to \infty$. Then the Laplace transform
$s \mapsto \int_{(0, \infty)} e^{-st} f(t)\,dt$ is complex differentiable at every point of the
half-plane $\{s \in \mathbb{C} : \operatorname{Re} s > a\}$.

Local integrability on $[0, \infty)$, not only on $(0, \infty)$, is what makes the Laplace
integral converge on this half-plane: $f(t) = 1/t$ is continuous on $(0, \infty)$ and bounded at
infinity, but not integrable near $0$, so its Laplace integral diverges for every $s$.

Source: ATLAS NumberTheoryI N320 (Sutherland, 18.785 Number Theory I, Lecture 16); a corrected,
strengthened-premise formalization of the intended holomorphy claim, since the source's piecewise
continuity on the open ray does not give integrability near 0. This is not a literal proof of the
under-specified source wording. -/
theorem differentiableOn_laplace_of_isBigO_exp
    (f : ℝ → E) (a : ℝ)
    (hf : LocallyIntegrableOn f (Set.Ici 0))
    (hO : f =O[Filter.atTop] (fun t : ℝ => Real.exp (a * t)))
    [CompleteSpace E] :
    DifferentiableOn ℂ (laplace f) {s | a < s.re} := by
  intro s₀ hs₀
  simp only [Set.mem_ofPred_eq] at hs₀
  set μ := volume.restrict (Set.Ioi (0 : ℝ)) with hμ_def
  set δ := (s₀.re - a) / 2 with hδ_def
  set b := (s₀.re + a) / 2 with hb_def
  have hδ : 0 < δ := by
    simp only [hδ_def]
    linarith
  have hab : a < b := by
    simp only [hb_def]
    linarith
  have hba : 0 < b - a := sub_pos.mpr hab
  have hball_re : ∀ z ∈ Metric.ball s₀ δ, b ≤ z.re := by
    intro z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have habs_re : |z.re - s₀.re| ≤ ‖z - s₀‖ := by
      rw [← Complex.sub_re]
      exact Complex.abs_re_le_norm _
    have hlt : |z.re - s₀.re| < δ := lt_of_le_of_lt habs_re hz
    have hmem := abs_lt.mp hlt
    simp only [hb_def, hδ_def] at hmem ⊢
    linarith [hmem.1, hmem.2]
  have hfIoi : LocallyIntegrableOn f (Set.Ioi (0 : ℝ)) :=
    hf.mono_set Set.Ioi_subset_Ici_self
  have hmeas_F : ∀ z : ℂ, AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-z * (t : ℂ)) • f t) μ := by
    intro z
    have hexp : AEStronglyMeasurable
        (fun t : ℝ => Complex.exp (-z * (t : ℂ)))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      apply Continuous.aestronglyMeasurable
      exact Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)
    rw [hμ_def]
    exact hexp.smul hfIoi.aestronglyMeasurable
  have hF_int : Integrable
      (fun t : ℝ => Complex.exp (-s₀ * (t : ℂ)) • f t) μ := by
    have hconv := laplaceConvergent_of_isBigO_exp f a hf hO
      (show a < s₀.re from hs₀)
    unfold LaplaceConvergent at hconv
    rw [hμ_def]
    exact hconv
  have hmeas_deriv : AEStronglyMeasurable
      (fun t : ℝ => (-(t : ℂ) * Complex.exp (-s₀ * (t : ℂ))) • f t)
      μ := by
    have hcont : Continuous
        (fun t : ℝ => (-(t : ℂ) * Complex.exp (-s₀ * (t : ℂ))) :
          ℝ → ℂ) := by
      apply Continuous.mul
      · exact Complex.continuous_ofReal.neg
      · exact Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)
    rw [hμ_def]
    exact hcont.aestronglyMeasurable.smul hfIoi.aestronglyMeasurable
  have hB_loc : LocallyIntegrableOn
      (fun t : ℝ => |t| * Real.exp (-b * t) * ‖f t‖) (Set.Ici 0) := by
    have hcont : ContinuousOn (fun t : ℝ => |t| * Real.exp (-b * t))
        (Set.Ici (0 : ℝ)) :=
      (continuous_abs.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id'))).continuousOn
    exact hf.norm.continuousOn_mul hcont isClosed_Ici.isLocallyClosed
  have hcomp_int : IntegrableAtFilter
      (fun t : ℝ => t * Real.exp (-(b - a) * t)) Filter.atTop volume :=
    (integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp
      (integrableOn_mul_exp_neg_Ioi' hba)).1
  have hbig : (fun t : ℝ => |t| * Real.exp (-b * t) * ‖f t‖)
      =O[Filter.atTop]
      (fun t : ℝ => t * Real.exp (-(b - a) * t)) := by
    rw [Asymptotics.isBigO_iff] at hO ⊢
    obtain ⟨C, hC⟩ := hO
    refine ⟨C, ?_⟩
    filter_upwards [hC, Filter.eventually_ge_atTop (0 : ℝ)] with t ht ht0
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at ht
    show ‖|t| * Real.exp (-b * t) * ‖f t‖‖ ≤
      C * ‖t * Real.exp (-(b - a) * t)‖
    have hnn : 0 ≤ |t| * Real.exp (-b * t) * ‖f t‖ :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))
        (norm_nonneg _)
    have hnn2 : 0 ≤ t * Real.exp (-(b - a) * t) :=
      mul_nonneg ht0 (Real.exp_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn,
      Real.norm_eq_abs, abs_of_nonneg hnn2, abs_of_nonneg ht0]
    calc t * Real.exp (-b * t) * ‖f t‖
        ≤ t * Real.exp (-b * t) * (C * Real.exp (a * t)) :=
          mul_le_mul_of_nonneg_left ht
            (mul_nonneg ht0 (Real.exp_nonneg _))
      _ = C * (t * Real.exp (-(b - a) * t)) := by
          rw [show -(b - a) * t = -b * t + a * t from by ring]
          rw [Real.exp_add]
          ring
  have hbound_int : Integrable
      (fun t : ℝ => |t| * Real.exp (-b * t) * ‖f t‖) μ := by
    rw [hμ_def]
    exact (hB_loc.integrableOn_of_isBigO_atTop hbig hcomp_int).mono_set
      Set.Ioi_subset_Ici_self
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ)
    (F := fun (s : ℂ) (t : ℝ) => Complex.exp (-s * (t : ℂ)) • f t)
    (F' := fun (s : ℂ) (t : ℝ) =>
      (-(t : ℂ) * Complex.exp (-s * (t : ℂ))) • f t)
    (bound := fun t : ℝ => |t| * Real.exp (-b * t) * ‖f t‖)
    (s := Metric.ball s₀ δ)
    (x₀ := s₀)
    (Metric.ball_mem_nhds s₀ hδ)
    (Filter.Eventually.of_forall (fun z => hmeas_F z))
    hF_int
    hmeas_deriv
    ?_ ?_ ?_
  · exact key.2.differentiableAt.differentiableWithinAt
  · rw [ae_restrict_iff' measurableSet_Ioi]
    apply ae_of_all
    intro t ht z hz
    simp only [Set.mem_Ioi] at ht
    rw [norm_smul, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-z * (t : ℂ)).re = -z.re * t := by
      simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [hre]
    have hb : b ≤ z.re := hball_re z hz
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp_of_le
          (mul_le_mul_of_nonneg_right (neg_le_neg hb) (le_of_lt ht)))
        (abs_nonneg t))
      (norm_nonneg _)
  · exact hbound_int
  · apply ae_of_all
    intro t z _
    have h1 : HasDerivAt (fun s : ℂ => -s * (t : ℂ)) (-(t : ℂ)) z := by
      have hder := (hasDerivAt_neg (𝕜 := ℂ) z).mul_const (t : ℂ)
      simp only [neg_one_mul] at hder
      exact hder
    have h2 := h1.cexp.smul_const (f t)
    have heq : Complex.exp (-z * (t : ℂ)) * (-(t : ℂ)) =
        -(t : ℂ) * Complex.exp (-z * (t : ℂ)) := mul_comm _ _
    rw [heq] at h2
    exact h2
