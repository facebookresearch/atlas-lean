/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ViscositySolution.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Stability of viscosity solutions under locally uniform limits

A locally uniform limit of continuous viscosity subsolutions (supersolutions, solutions) of a
fixed continuous first-order equation on an open subset of a finite-dimensional real inner
product space is again a viscosity subsolution (supersolution, solution). This is the
locally uniform case of the half-relaxed-limit stability of Crandall, Ishii and Lions.

## Main results

* `IsViscositySubsolution.of_tendstoLocallyUniformlyOn`
* `IsViscositySupersolution.of_tendstoLocallyUniformlyOn`
* `IsViscositySolution.of_tendstoLocallyUniformlyOn`

## References

* M. G. Crandall, H. Ishii and P.-L. Lions, *User's guide to viscosity solutions of second order
  partial differential equations*, Bull. Amer. Math. Soc. 27 (1992) 1–67, arXiv:math/9207212,
  §6 (Lemma 6.1, Remarks 6.2–6.4).
-/

@[expose] public section

namespace MathlibExt.Analysis.ViscositySolution

open Filter Topology Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : E → ℝ → (E →L[ℝ] ℝ) → ℝ} {Ω : Set E}

/-- Core of the stability argument, for subsolutions of `F ≤ 0`. -/
private theorem stability_aux
    (hF : Continuous fun q : E × ℝ × (E →L[ℝ] ℝ) => F q.1 q.2.1 q.2.2) (hΩ : IsOpen Ω)
    {u : ℕ → E → ℝ} {U : E → ℝ}
    (hu : ∀ n, ∀ x ∈ Ω, ∀ φ : E → ℝ, ContDiff ℝ 1 φ →
      IsLocalMaxOn (fun y => u n y - φ y) Ω x → F x (u n x) (fderiv ℝ φ x) ≤ 0)
    (hcont : ∀ n, ContinuousOn (u n) Ω) (hlim : TendstoLocallyUniformlyOn u U atTop Ω)
    {x₀ : E} (hx₀ : x₀ ∈ Ω) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hmax : IsLocalMaxOn (fun y => U y - φ y) Ω x₀) : F x₀ (U x₀) (fderiv ℝ φ x₀) ≤ 0 := by
  have hUc : ContinuousOn U Ω := hlim.continuousOn (Frequently.of_forall hcont)
  -- a closed ball inside `Ω` on which `x₀` maximises `U - φ`
  have hmax' : ∀ᶠ y in 𝓝 x₀, U y - φ y ≤ U x₀ - φ x₀ := by
    rw [← nhdsWithin_eq_nhds.2 (hΩ.mem_nhds hx₀)]; exact hmax
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.eventually_nhds_iff_ball.1 hmax'
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.isOpen_iff.1 hΩ x₀ hx₀
  set r := min r₁ r₂ / 2 with hr
  have hrpos : 0 < r := by positivity
  have hrlt₁ : r < r₁ := by rw [hr]; linarith [min_le_left r₁ r₂]
  have hrlt₂ : r < r₂ := by rw [hr]; linarith [min_le_right r₁ r₂]
  set K := closedBall x₀ r with hK
  have hKΩ : K ⊆ Ω := (closedBall_subset_ball hrlt₂).trans hball₂
  have hKmax : ∀ y ∈ K, U y - φ y ≤ U x₀ - φ x₀ :=
    fun y hy => hball₁ y (closedBall_subset_ball hrlt₁ hy)
  have hKc : IsCompact K := isCompact_closedBall x₀ r
  have hx₀K : x₀ ∈ K := mem_closedBall_self hrpos.le
  -- the strict perturbation `ψ = φ + ‖· - x₀‖²`
  set ψ : E → ℝ := fun y => φ y + ‖y - x₀‖ ^ 2 with hψ
  have hψc : ContDiff ℝ 1 ψ :=
    hφ.add ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
  have hsqd : DifferentiableAt ℝ (fun y : E => ‖y - x₀‖ ^ 2) x₀ :=
    (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).differentiable
      one_ne_zero) x₀
  have hsq0 : fderiv ℝ (fun y : E => ‖y - x₀‖ ^ 2) x₀ = 0 := by
    refine IsLocalMin.fderiv_eq_zero (Eventually.of_forall fun y => ?_)
    simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  have hψx₀ : fderiv ℝ ψ x₀ = fderiv ℝ φ x₀ := by
    rw [hψ, fderiv_fun_add ((hφ.differentiable one_ne_zero) x₀) hsqd, hsq0, add_zero]
  -- maximisers of `u n - ψ` on `K`
  have hexists : ∀ n, ∃ x ∈ K, IsMaxOn (fun y => u n y - ψ y) K x := fun n =>
    hKc.exists_isMaxOn ⟨x₀, hx₀K⟩
      (((hcont n).mono hKΩ).sub (hψc.continuous.continuousOn))
  choose xs hxsK hxsmax using hexists
  have hunif : TendstoUniformlyOn u U atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).1 hlim K hKΩ hKc
  -- the maximisers converge to `x₀`
  have hxs : Tendsto xs atTop (𝓝 x₀) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    set ρ := min (ε / 2) r with hρ
    have hρpos : 0 < ρ := lt_min (by positivity) hrpos
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (Metric.tendstoUniformlyOn_iff.1 hunif (ρ ^ 2 / 2) (by positivity))
    refine ⟨N, fun n hn => ?_⟩
    have hρε : ρ < ε := (min_le_left _ _).trans_lt (by linarith)
    refine lt_of_lt_of_le ?_ hρε.le
    by_contra hfar
    push Not at hfar
    have h1 := hN n hn (xs n) (hxsK n)
    have h2 := hN n hn x₀ hx₀K
    have h3 := hKmax (xs n) (hxsK n)
    have h4 : u n x₀ - ψ x₀ ≤ u n (xs n) - ψ (xs n) := hxsmax n hx₀K
    simp only [hψ, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, add_zero] at h4
    rw [Real.dist_eq] at h1 h2
    have hfar2 : ρ ^ 2 ≤ ‖xs n - x₀‖ ^ 2 := by
      rw [← dist_eq_norm]; exact pow_le_pow_left₀ hρpos.le hfar 2
    have := (abs_lt.1 h1).1
    have := (abs_lt.1 h2).2
    linarith
  -- eventually the maximisers are interior, hence the subsolution test applies
  have hinner : ∀ᶠ n in atTop, xs n ∈ ball x₀ r := hxs (ball_mem_nhds x₀ hrpos)
  have hineq : ∀ᶠ n in atTop, F (xs n) (u n (xs n)) (fderiv ℝ ψ (xs n)) ≤ 0 := by
    filter_upwards [hinner] with n hn
    refine hu n (xs n) (hKΩ (hxsK n)) ψ hψc ?_
    exact ((hxsmax n).isLocalMax (mem_of_superset (isOpen_ball.mem_nhds hn)
      ball_subset_closedBall)).isLocalMaxOn Ω
  -- pass to the limit
  have hval : Tendsto (fun n => u n (xs n)) atTop (𝓝 (U x₀)) :=
    hunif.tendsto_comp ((hUc x₀ hx₀).mono hKΩ)
      (tendsto_nhdsWithin_iff.2 ⟨hxs, Eventually.of_forall hxsK⟩)
  have hder : Tendsto (fun n => fderiv ℝ ψ (xs n)) atTop (𝓝 (fderiv ℝ ψ x₀)) :=
    ((hψc.continuous_fderiv one_ne_zero).tendsto x₀).comp hxs
  have hlimF : Tendsto (fun n => F (xs n) (u n (xs n)) (fderiv ℝ ψ (xs n))) atTop
      (𝓝 (F x₀ (U x₀) (fderiv ℝ ψ x₀))) :=
    (hF.tendsto (x₀, U x₀, fderiv ℝ ψ x₀)).comp (hxs.prodMk_nhds (hval.prodMk_nhds hder))
  rw [← hψx₀]
  exact le_of_tendsto hlimF hineq

/-- **Stability of viscosity subsolutions under locally uniform limits** (Crandall, Ishii and
Lions, *User's guide*, Bull. AMS 1992, Lemma 6.1 with Remark 6.4, first-order case with a fixed
equation). Let `F` be jointly continuous, `Ω` open in a finite-dimensional real inner product
space, and `uₙ` continuous viscosity subsolutions of `F(x, u, Du) = 0` on `Ω` converging locally
uniformly on `Ω` to `U`. Then `U` is a viscosity subsolution on `Ω`. Lemma 6.1 itself treats
merely upper semicontinuous `uₙ` through the half-relaxed limit `limsup*`, and Remark 6.3 lets
the equation vary with `n`; neither generality is claimed here. -/
theorem IsViscositySubsolution.of_tendstoLocallyUniformlyOn
    (hF : Continuous fun q : E × ℝ × (E →L[ℝ] ℝ) => F q.1 q.2.1 q.2.2) (hΩ : IsOpen Ω)
    {u : ℕ → E → ℝ} {U : E → ℝ} (hu : ∀ n, IsViscositySubsolution F Ω (u n))
    (hcont : ∀ n, ContinuousOn (u n) Ω) (hlim : TendstoLocallyUniformlyOn u U atTop Ω) :
    IsViscositySubsolution F Ω U :=
  ⟨(hlim.continuousOn (Frequently.of_forall hcont)).upperSemicontinuousOn,
    fun _ hx₀ _ hφ hmax => stability_aux hF hΩ (fun n => (hu n).2) hcont hlim hx₀ hφ hmax⟩

/-- **Stability of viscosity supersolutions under locally uniform limits** (Crandall, Ishii and
Lions, *User's guide*, Remark 6.2 with Remark 6.4, first-order case with a fixed equation). A
locally uniform limit on the open set `Ω` of continuous viscosity supersolutions of the jointly
continuous equation `F(x, u, Du) = 0` is a viscosity supersolution. Proved by applying the
subsolution case to `-uₙ` and the equation `-F(x, -r, -p) = 0`. -/
theorem IsViscositySupersolution.of_tendstoLocallyUniformlyOn
    (hF : Continuous fun q : E × ℝ × (E →L[ℝ] ℝ) => F q.1 q.2.1 q.2.2) (hΩ : IsOpen Ω)
    {u : ℕ → E → ℝ} {U : E → ℝ} (hu : ∀ n, IsViscositySupersolution F Ω (u n))
    (hcont : ∀ n, ContinuousOn (u n) Ω) (hlim : TendstoLocallyUniformlyOn u U atTop Ω) :
    IsViscositySupersolution F Ω U := by
  set G : E → ℝ → (E →L[ℝ] ℝ) → ℝ := fun x r p => -F x (-r) (-p) with hG
  have hGc : Continuous fun q : E × ℝ × (E →L[ℝ] ℝ) => G q.1 q.2.1 q.2.2 :=
    (hF.comp (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).neg.prodMk
      (continuous_snd.comp continuous_snd).neg))).neg
  have hneg : ∀ n, ∀ x ∈ Ω, ∀ φ : E → ℝ, ContDiff ℝ 1 φ →
      IsLocalMaxOn (fun y => (fun n y => -u n y) n y - φ y) Ω x →
      G x ((fun n y => -u n y) n x) (fderiv ℝ φ x) ≤ 0 := by
    intro n x hx φ hφ hmax
    have hmin : IsLocalMinOn (fun y => u n y - (fun y => -φ y) y) Ω x := by
      filter_upwards [hmax] with y hy
      change -u n y - φ y ≤ -u n x - φ x at hy
      change u n x - -φ x ≤ u n y - -φ y
      linarith
    have := (hu n).2 x hx (fun y => -φ y) hφ.neg hmin
    rw [fderiv_fun_neg] at this
    change -F x (-(-u n x)) (-fderiv ℝ φ x) ≤ 0
    rw [neg_neg]
    linarith
  have hlim' : TendstoLocallyUniformlyOn (fun n y => -u n y) (fun y => -U y) atTop Ω := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ] at hlim ⊢
    intro K hK hKc
    have h := Metric.tendstoUniformlyOn_iff.1 (hlim K hK hKc)
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
    filter_upwards [h ε hε] with n hn y hy
    rw [dist_neg_neg]
    exact hn y hy
  refine ⟨(hlim.continuousOn (Frequently.of_forall hcont)).lowerSemicontinuousOn,
    fun x₀ hx₀ φ hφ hmin => ?_⟩
  have hmax : IsLocalMaxOn (fun y => (fun y => -U y) y - (fun y => -φ y) y) Ω x₀ := by
    filter_upwards [hmin] with y hy
    change U x₀ - φ x₀ ≤ U y - φ y at hy
    change -U y - -φ y ≤ -U x₀ - -φ x₀
    linarith
  have := stability_aux hGc hΩ hneg (fun n => (hcont n).neg) hlim' hx₀ hφ.neg hmax
  rw [fderiv_fun_neg] at this
  change -F x₀ (-(-U x₀)) (-(-fderiv ℝ φ x₀)) ≤ 0 at this
  rw [neg_neg, neg_neg] at this
  linarith

/-- **Stability of viscosity solutions under locally uniform limits** (Crandall, Ishii and
Lions, *User's guide*, Lemma 6.1 and Remarks 6.2–6.4, first-order case with a fixed equation).
A locally uniform limit on the open set `Ω` of continuous viscosity solutions of the jointly
continuous equation `F(x, u, Du) = 0` is a viscosity solution. -/
theorem IsViscositySolution.of_tendstoLocallyUniformlyOn
    (hF : Continuous fun q : E × ℝ × (E →L[ℝ] ℝ) => F q.1 q.2.1 q.2.2) (hΩ : IsOpen Ω)
    {u : ℕ → E → ℝ} {U : E → ℝ} (hu : ∀ n, IsViscositySolution F Ω (u n))
    (hcont : ∀ n, ContinuousOn (u n) Ω) (hlim : TendstoLocallyUniformlyOn u U atTop Ω) :
    IsViscositySolution F Ω U :=
  ⟨IsViscositySubsolution.of_tendstoLocallyUniformlyOn hF hΩ (fun n => (hu n).1) hcont hlim,
    IsViscositySupersolution.of_tendstoLocallyUniformlyOn hF hΩ (fun n => (hu n).2) hcont hlim⟩

end MathlibExt.Analysis.ViscositySolution
