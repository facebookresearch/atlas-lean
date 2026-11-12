/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

open scoped Topology
open Filter

/-!
# Small-tax deadweight loss with a controlled remainder

Inverse demand `Pd` and inverse supply `Ps` cross at the no-tax equilibrium
quantity `qstar`. A per-unit tax `τ` drives a wedge between the price buyers pay
and the price sellers receive: an equilibrium quantity `q` under the tax solves
`Pd q - Ps q = τ`. The deadweight loss of moving from `qstar` to `q` is the lost
gains from trade `∫_q^qstar (Pd x - Ps x) dx`, counted as a positive loss.

For `C²` schedules with `s = Ps'(qstar) - Pd'(qstar) > 0`:

* small taxes have an equilibrium path `τ ↦ q τ` through `qstar`, continuous at
  `0` (inverse function theorem, `exists_taxEquilibrium_path`);
* along any such path, the deadweight loss equals the Harberger triangle
  `τ² / (2 s)` up to `O(τ³)` (`deadweightLoss_sub_harberger_isBigO`).

The triangle formula is exact for linear schedules but not in general; only the
remainder is controlled. Income effects are not modelled (the schedules are
fixed functions), and no identification of consumer surplus with welfare beyond
this Marshallian definition is made.

## Main results

* `MathlibExt.Economics.DeadweightLoss.exists_taxEquilibrium_path`
* `MathlibExt.Economics.DeadweightLoss.deadweightLoss_sub_harberger_isBigO`

## References

* A. C. Harberger, "The Measurement of Waste", American Economic Review 54
  (1964), 58–76.
* Standard intermediate-microeconomics treatment of tax incidence and
  deadweight loss (e.g. MIT 14.04; Varian, *Intermediate Microeconomics*).

Atlas roadmap target EC09.T04.
-/

namespace MathlibExt.Economics.DeadweightLoss

/-- Deadweight loss of moving traded quantity from the no-tax equilibrium
`qstar` to `q`, with inverse demand `Pd` and inverse supply `Ps`: the lost
gains from trade `∫_q^qstar (Pd x - Ps x) dx`. Sign convention: a loss is
positive (for a tax, `q < qstar` and `Pd > Ps` on `(q, qstar)`). -/
noncomputable def deadweightLoss (Pd Ps : ℝ → ℝ) (qstar q : ℝ) : ℝ :=
  ∫ x in q..qstar, (Pd x - Ps x)

/-- `q` is an equilibrium quantity under a per-unit tax `τ`: the price buyers pay
exceeds the price sellers receive by exactly the tax, `Pd q - Ps q = τ`. -/
def IsTaxEquilibrium (Pd Ps : ℝ → ℝ) (τ q : ℝ) : Prop :=
  Pd q - Ps q = τ

private theorem isBigO_nonneg_bound {α : Type*} {E F : Type*} [Norm E] [SeminormedAddGroup F]
    {l : Filter α} {f : α → E} {g : α → F}
    (h : f =O[l] g) : ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by
  rw [Asymptotics.isBigO_iff] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨max c 0, le_max_right _ _, ?_⟩
  filter_upwards [hc] with x hx
  calc ‖f x‖ ≤ c * ‖g x‖ := hx
    _ ≤ max c 0 * ‖g x‖ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg (g x))

private theorem norm_sub_le_of_mem_uIoc {t p q : ℝ} (h : t ∈ Set.uIoc p q) :
    ‖t - p‖ ≤ ‖q - p‖ ∧ ‖t - q‖ ≤ ‖p - q‖ := by
  rw [Set.mem_uIoc] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · constructor
    · rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr h1.le),
        abs_of_nonneg (sub_nonneg.mpr (le_trans h1.le h2))]
      exact sub_le_sub_right h2 p
    · rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr h2),
        abs_of_nonpos (sub_nonpos.mpr (lt_of_lt_of_le h1 h2).le)]
      linarith
  · constructor
    · rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr h2),
        abs_of_nonpos (sub_nonpos.mpr (lt_of_lt_of_le h1 h2).le)]
      linarith
    · rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr h1.le),
        abs_of_nonneg (sub_nonneg.mpr (le_trans h1.le h2))]
      exact sub_le_sub_right h2 q

private theorem exists_linear_bound_of_contDiffAt {g : ℝ → ℝ} {a : ℝ}
    (hg : ContDiffAt ℝ 1 g a) (hga : g a = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in 𝓝 a, ‖g x‖ ≤ C * ‖x - a‖ := by
  obtain ⟨u, hu_mem, hu⟩ := hg.contDiffOn le_rfl (fun h => absurd h (by decide))
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.mem_nhds_iff.mp hu_mem
  have hB : ContDiffOn ℝ 1 g (Metric.ball a r) := hu.mono hr_sub
  have hderiv : ∀ x ∈ Metric.ball a r, DifferentiableAt ℝ g x := fun x hx =>
    (hB.differentiableOn (by decide)).differentiableAt (Metric.isOpen_ball.mem_nhds hx)
  have hcont : ContinuousAt (deriv g) a :=
    (hB.continuousOn_deriv_of_isOpen Metric.isOpen_ball le_rfl).continuousAt
      (Metric.ball_mem_nhds a hr_pos)
  have hM_pos : (0 : ℝ) < ‖deriv g a‖ + 1 := by
    have hnn : (0 : ℝ) ≤ ‖deriv g a‖ := norm_nonneg _
    linarith
  have hev : ∀ᶠ x in 𝓝 a, ‖deriv g x‖ ≤ ‖deriv g a‖ + 1 := by
    have h2 : ∀ᶠ y in 𝓝 (‖deriv g a‖), y ≤ ‖deriv g a‖ + 1 := by
      have hlt : ∀ᶠ y in 𝓝 (‖deriv g a‖), y < ‖deriv g a‖ + 1 :=
        eventually_lt_nhds (lt_add_one _)
      exact hlt.mono (fun y hy => le_of_lt hy)
    have h3 : Filter.Tendsto (fun y : ℝ => ‖y‖) (𝓝 (deriv g a)) (𝓝 ‖deriv g a‖) :=
      continuous_norm.tendsto _
    exact Filter.Tendsto.eventually hcont (h3.eventually h2)
  obtain ⟨r₂, hr₂_pos, hr₂_sub⟩ := Metric.mem_nhds_iff.mp hev
  have hr'_pos : (0 : ℝ) < min r r₂ := lt_min hr_pos hr₂_pos
  refine ⟨‖deriv g a‖ + 1, le_of_lt hM_pos, ?_⟩
  filter_upwards [Metric.ball_mem_nhds a hr'_pos] with x hx
  have hbound : ∀ y ∈ Metric.ball a (min r r₂), ‖deriv g y‖ ≤ ‖deriv g a‖ + 1 := by
    intro y hy
    have hy₂ : y ∈ Metric.ball a r₂ := by
      rw [Metric.mem_ball] at hy ⊢
      exact lt_of_lt_of_le hy (min_le_right r r₂)
    exact hr₂_sub hy₂
  have hderiv' : ∀ y ∈ Metric.ball a (min r r₂), DifferentiableAt ℝ g y := fun y hy =>
    hderiv y (by
      rw [Metric.mem_ball] at hy ⊢
      exact lt_of_lt_of_le hy (min_le_left r r₂))
  have ha_mem : a ∈ Metric.ball a (min r r₂) := Metric.mem_ball_self hr'_pos
  have hle := Convex.norm_image_sub_le_of_norm_deriv_le hderiv' hbound
    (convex_ball a (min r r₂)) ha_mem hx
  simpa [hga] using hle

private theorem exists_quad_bound_of_contDiffAt {g : ℝ → ℝ} {a : ℝ}
    (hg : ContDiffAt ℝ 2 g a) (hga : g a = 0) (hg'a : deriv g a = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in 𝓝 a, ‖g x‖ ≤ C * ‖x - a‖ ^ 2 := by
  obtain ⟨u, hu_mem, hu⟩ := hg.contDiffOn le_rfl (fun h => absurd h (by decide))
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.mem_nhds_iff.mp hu_mem
  have hB : ContDiffOn ℝ 2 g (Metric.ball a r) := hu.mono hr_sub
  have hB1 : ContDiffOn ℝ 1 (deriv g) (Metric.ball a r) :=
    hB.deriv_of_isOpen Metric.isOpen_ball (by decide)
  have hg'a_at : ContDiffAt ℝ 1 (deriv g) a :=
    hB1.contDiffAt (Metric.ball_mem_nhds a hr_pos)
  obtain ⟨C₁, hC₁_nonneg, hC₁⟩ :=
    exists_linear_bound_of_contDiffAt hg'a_at hg'a
  obtain ⟨r₂, hr₂_pos, hr₂_sub⟩ := Metric.mem_nhds_iff.mp hC₁
  have hr'_pos : (0 : ℝ) < min r r₂ := lt_min hr_pos hr₂_pos
  refine ⟨C₁, hC₁_nonneg, ?_⟩
  filter_upwards [Metric.ball_mem_nhds a hr'_pos] with x hx
  have hx_r : x ∈ Metric.ball a r := by
    rw [Metric.mem_ball] at hx ⊢
    exact lt_of_lt_of_le hx (min_le_left r r₂)
  have hseg : Set.uIcc a x ⊆ Metric.ball a r := by
    rw [← segment_eq_uIcc]
    exact (convex_ball a r).segment_subset (Metric.mem_ball_self hr_pos) hx_r
  have hseg₂ : Set.uIcc a x ⊆ Metric.ball a r₂ := by
    rw [← segment_eq_uIcc]
    exact (convex_ball a r₂).segment_subset (Metric.mem_ball_self hr₂_pos) (by
      rw [Metric.mem_ball] at hx ⊢
      exact lt_of_lt_of_le hx (min_le_right r r₂))
  have hdiff : ∀ t ∈ Set.uIcc a x, DifferentiableAt ℝ g t := fun t ht =>
    (hB.differentiableOn (by decide)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (hseg ht))
  have hcont : ContinuousOn (deriv g) (Set.uIcc a x) := hB1.continuousOn.mono hseg
  have hint : IntervalIntegrable (deriv g) MeasureTheory.volume a x :=
    hcont.intervalIntegrable
  have hFTC : (∫ t in a..x, deriv g t) = g x - g a :=
    intervalIntegral.integral_deriv_eq_sub hdiff hint
  have hpt : ∀ t ∈ Set.uIoc a x, ‖deriv g t‖ ≤ C₁ * ‖x - a‖ := by
    intro t ht
    have ht_cc : t ∈ Set.uIcc a x := by
      rw [Set.mem_uIoc] at ht
      rw [Set.mem_uIcc]
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.le, h2⟩
      · exact Or.inr ⟨h1.le, h2⟩
    have hle : ‖deriv g t‖ ≤ C₁ * ‖t - a‖ := hr₂_sub (hseg₂ ht_cc)
    have habs : ‖t - a‖ ≤ ‖x - a‖ := (norm_sub_le_of_mem_uIoc ht).1
    calc ‖deriv g t‖ ≤ C₁ * ‖t - a‖ := hle
      _ ≤ C₁ * ‖x - a‖ := mul_le_mul_of_nonneg_left habs hC₁_nonneg
  have hnorm : ‖∫ t in a..x, deriv g t‖ ≤ (C₁ * ‖x - a‖) * |x - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [hFTC, hga, sub_zero] at hnorm
  calc ‖g x‖ ≤ (C₁ * ‖x - a‖) * |x - a| := hnorm
    _ = C₁ * ‖x - a‖ ^ 2 := by rw [Real.norm_eq_abs]; ring

private theorem contDiffAt_remainder {Pd Ps : ℝ → ℝ} {qstar s : ℝ}
    (hd : ContDiffAt ℝ 2 Pd qstar) (hs : ContDiffAt ℝ 2 Ps qstar)
    (hsdef : s = deriv Ps qstar - deriv Pd qstar)
    (heq : Pd qstar = Ps qstar) :
    ContDiffAt ℝ 2 (fun x => (Pd x - Ps x) + s * (x - qstar)) qstar ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in 𝓝 qstar,
      ‖(Pd x - Ps x) + s * (x - qstar)‖ ≤ C * ‖x - qstar‖ ^ 2 := by
  have hPd : DifferentiableAt ℝ Pd qstar := hd.differentiableAt (by decide)
  have hPs : DifferentiableAt ℝ Ps qstar := hs.differentiableAt (by decide)
  have hsub : ContDiffAt ℝ 2 (fun x => Pd x - Ps x) qstar := hd.sub hs
  have haff : ContDiffAt ℝ 2 (fun x : ℝ => s * (x - qstar)) qstar :=
    (ContDiff.mul contDiff_const (contDiff_id.sub contDiff_const)).contDiffAt
  have hR : ContDiffAt ℝ 2 (fun x => (Pd x - Ps x) + s * (x - qstar)) qstar :=
    hsub.add haff
  refine ⟨hR, ?_⟩
  have hR0 : (Pd qstar - Ps qstar) + s * (qstar - qstar) = 0 := by
    rw [sub_eq_zero.mpr heq, sub_self, mul_zero, add_zero]
  have hdw : deriv (fun x => Pd x - Ps x) qstar = deriv Pd qstar - deriv Ps qstar :=
    deriv_sub hPd hPs
  have haff' : deriv (fun x : ℝ => s * (x - qstar)) qstar = s := by
    have h : HasDerivAt (fun x : ℝ => s * (x - qstar)) (s * 1) qstar :=
      HasDerivAt.const_mul s ((hasDerivAt_id qstar).sub_const qstar)
    have hder := h.deriv
    rw [hder]
    ring
  have hR' : deriv (fun x => (Pd x - Ps x) + s * (x - qstar)) qstar = 0 := by
    have h1 : DifferentiableAt ℝ (fun x => Pd x - Ps x) qstar :=
      hsub.differentiableAt (by decide)
    have h2 : DifferentiableAt ℝ (fun x : ℝ => s * (x - qstar)) qstar :=
      haff.differentiableAt (by decide)
    have hadd := deriv_add h1 h2
    have hadd' : deriv (fun x => (Pd x - Ps x) + s * (x - qstar)) qstar
        = (deriv Pd qstar - deriv Ps qstar) + s := by
      have h3 : deriv ((fun x => Pd x - Ps x) + (fun x : ℝ => s * (x - qstar))) qstar
          = (deriv Pd qstar - deriv Ps qstar) + s := by
        rw [hadd, hdw, haff']
      exact h3
    rw [hadd', hsdef]
    ring
  have hR0' : (fun x => (Pd x - Ps x) + s * (x - qstar)) qstar = 0 := hR0
  exact exists_quad_bound_of_contDiffAt hR hR0' hR'

private theorem hasDerivAt_quad_antideriv (s qstar x : ℝ) :
    HasDerivAt (fun x => -((s / 2) * (x - qstar) ^ 2))
      (-((s / 2) * (2 * (x - qstar)))) x := by
  have h1 : HasDerivAt (fun x : ℝ => x - qstar) 1 x :=
    (hasDerivAt_id x).sub_const qstar
  have h2 : HasDerivAt (fun x : ℝ => (x - qstar) ^ 2) (2 * (x - qstar)) x := by
    simpa [Function.comp_def] using (hasDerivAt_pow 2 (x - qstar)).comp x h1
  exact (h2.const_mul (s / 2)).neg

/-- Small taxes have equilibria near the no-tax equilibrium: for `C²` inverse
demand and supply crossing at `qstar` with supply steeper than demand, there is
an equilibrium quantity path `τ ↦ q τ`, continuous at `0` with `q 0 = qstar`. -/
theorem exists_taxEquilibrium_path {Pd Ps : ℝ → ℝ} {qstar : ℝ}
    (hd : ContDiffAt ℝ 2 Pd qstar) (hs : ContDiffAt ℝ 2 Ps qstar)
    (heq : Pd qstar = Ps qstar) (hslope : 0 < deriv Ps qstar - deriv Pd qstar) :
    ∃ q : ℝ → ℝ, q 0 = qstar ∧ ContinuousAt q 0 ∧
      ∀ᶠ τ in 𝓝 0, IsTaxEquilibrium Pd Ps τ (q τ) := by
  have hw2 : ContDiffAt ℝ 2 (fun x => Pd x - Ps x) qstar := hd.sub hs
  have hPd : DifferentiableAt ℝ Pd qstar := hd.differentiableAt (by decide)
  have hPs : DifferentiableAt ℝ Ps qstar := hs.differentiableAt (by decide)
  have hdw : deriv (fun x => Pd x - Ps x) qstar
      = -(deriv Ps qstar - deriv Pd qstar) := by
    have h2 : deriv (fun x => Pd x - Ps x) qstar
        = deriv Pd qstar - deriv Ps qstar := deriv_sub hPd hPs
    rw [h2]
    ring
  have hw0 : Pd qstar - Ps qstar = 0 := sub_eq_zero.mpr heq
  have hstrict0 : HasStrictDerivAt (fun x => Pd x - Ps x)
      (-(deriv Ps qstar - deriv Pd qstar)) qstar := by
    have h := hw2.hasStrictDerivAt (by decide)
    rw [hdw] at h
    exact h
  have hsne : -(deriv Ps qstar - deriv Pd qstar) ≠ 0 :=
    neg_ne_zero.mpr (ne_of_gt hslope)
  refine ⟨HasStrictDerivAt.localInverse (fun x => Pd x - Ps x)
    (-(deriv Ps qstar - deriv Pd qstar)) qstar hstrict0 hsne, ?_, ?_, ?_⟩
  · have hleft := hstrict0.eventually_left_inverse hsne
    have hpt := hleft.self_of_nhds
    have hpt' : HasStrictDerivAt.localInverse (fun x => Pd x - Ps x)
          (-(deriv Ps qstar - deriv Pd qstar)) qstar hstrict0 hsne
          (Pd qstar - Ps qstar) = qstar := hpt
    rw [hw0] at hpt'
    exact hpt'
  · have hcont := hstrict0.to_localInverse hsne
    have hcont' : HasStrictDerivAt (HasStrictDerivAt.localInverse (fun x => Pd x - Ps x)
          (-(deriv Ps qstar - deriv Pd qstar)) qstar hstrict0 hsne)
        (-(deriv Ps qstar - deriv Pd qstar))⁻¹ (Pd qstar - Ps qstar) := hcont
    rw [hw0] at hcont'
    exact hcont'.hasDerivAt.continuousAt
  · have hright := hstrict0.eventually_right_inverse hsne
    have hright' : ∀ᶠ x in 𝓝 (Pd qstar - Ps qstar),
        (fun x => Pd x - Ps x) (HasStrictDerivAt.localInverse (fun x => Pd x - Ps x)
          (-(deriv Ps qstar - deriv Pd qstar)) qstar hstrict0 hsne x) = x := hright
    rw [hw0] at hright'
    filter_upwards [hright'] with τ hτ
    exact hτ

/-- Harberger small-tax approximation with a controlled remainder: along any
equilibrium path continuous at `τ = 0` (the branch through `qstar`), the
deadweight loss equals `τ² / (2 (Ps'(qstar) - Pd'(qstar)))` up to `O(τ³)`. For
nonlinear schedules the triangle formula is not exact; only the remainder is
controlled. -/
theorem deadweightLoss_sub_harberger_isBigO {Pd Ps : ℝ → ℝ} {qstar : ℝ} {q : ℝ → ℝ}
    (hd : ContDiffAt ℝ 2 Pd qstar) (hs : ContDiffAt ℝ 2 Ps qstar)
    (hslope : 0 < deriv Ps qstar - deriv Pd qstar)
    (hq0 : q 0 = qstar) (hqc : ContinuousAt q 0)
    (hqeq : ∀ᶠ τ in 𝓝 0, IsTaxEquilibrium Pd Ps τ (q τ)) :
    (fun τ : ℝ => deadweightLoss Pd Ps qstar (q τ) -
        τ ^ 2 / (2 * (deriv Ps qstar - deriv Pd qstar)))
      =O[𝓝 0] fun τ : ℝ => τ ^ 3 := by
  set s : ℝ := deriv Ps qstar - deriv Pd qstar with hsdef
  have hsne : s ≠ 0 := ne_of_gt hslope
  have h2s_ne : (2 : ℝ) * s ≠ 0 := mul_ne_zero two_ne_zero hsne
  have heq : Pd qstar = Ps qstar := by
    have hweq : (fun τ => Pd (q τ) - Ps (q τ)) =ᶠ[𝓝 0] (fun τ => τ) := by
      filter_upwards [hqeq] with τ hτ
      exact hτ
    have h0 := Filter.EventuallyEq.eq_of_nhds hweq
    have h0' : Pd (q 0) - Ps (q 0) = (0 : ℝ) := h0
    rw [hq0] at h0'
    exact sub_eq_zero.mp h0'
  obtain ⟨hR_at, CR, hCR_nonneg, hCR⟩ := contDiffAt_remainder hd hs hsdef heq
  set C : ℝ := CR + 1 with hCdef
  have hC_pos : 0 < C := by
    have hle : (0 : ℝ) ≤ CR := hCR_nonneg
    linarith
  have hCne : C ≠ 0 := ne_of_gt hC_pos
  have h2C_ne : (2 : ℝ) * C ≠ 0 := mul_ne_zero two_ne_zero hCne
  have hCR' : ∀ᶠ x in 𝓝 qstar, ‖(Pd x - Ps x) + s * (x - qstar)‖ ≤ C * ‖x - qstar‖ ^ 2 := by
    filter_upwards [hCR] with x hx
    calc ‖(Pd x - Ps x) + s * (x - qstar)‖ ≤ CR * ‖x - qstar‖ ^ 2 := hx
      _ ≤ C * ‖x - qstar‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) 2)
        rw [hCdef]
        linarith [hCR_nonneg]
  have hqtend : Filter.Tendsto q (𝓝 0) (𝓝 qstar) := by
    rw [← hq0]
    exact hqc
  have hdtend : Filter.Tendsto (fun τ => q τ - qstar) (𝓝 0) (𝓝 0) := by
    have h : Filter.Tendsto (fun τ => q τ - qstar) (𝓝 0) (𝓝 (q 0 - qstar)) :=
      Filter.Tendsto.sub hqc tendsto_const_nhds
    simpa [hq0] using h
  have hrel : ∀ᶠ τ in 𝓝 (0:ℝ), s * (q τ - qstar)
      = ((Pd (q τ) - Ps (q τ)) + s * (q τ - qstar)) - τ := by
    filter_upwards [hqeq] with τ hτ
    have hτ' : Pd (q τ) - Ps (q τ) = τ := hτ
    conv_rhs => rw [hτ']
    ring
  have hRq : ∀ᶠ τ in 𝓝 (0:ℝ),
      ‖(Pd (q τ) - Ps (q τ)) + s * (q τ - qstar)‖ ≤ C * ‖q τ - qstar‖ ^ 2 :=
    hqtend.eventually hCR'
  have hsmall : ∀ᶠ τ in 𝓝 (0:ℝ), ‖q τ - qstar‖ ≤ s / (2 * C) := by
    have hpos : (0:ℝ) < s / (2 * C) := div_pos hslope (mul_pos two_pos hC_pos)
    have h1 : ∀ᶠ y in 𝓝 (0:ℝ), ‖y‖ ≤ s / (2 * C) := by
      have h2 : ∀ᶠ y in 𝓝 (‖(0:ℝ)‖), y ≤ s / (2 * C) := by
        rw [norm_zero]
        exact (eventually_lt_nhds hpos).mono (fun y hy => le_of_lt hy)
      have h3 : Filter.Tendsto (fun y : ℝ => ‖y‖) (𝓝 0) (𝓝 ‖(0:ℝ)‖) :=
        continuous_norm.tendsto 0
      exact h3.eventually h2
    exact hdtend.eventually h1
  have hlin : ∀ᶠ τ in 𝓝 (0:ℝ), ‖q τ - qstar‖ ≤ (2 / s) * ‖τ‖ := by
    filter_upwards [hrel, hRq, hsmall] with τ hrelτ hRqτ hsmallτ
    have hnorm_s : ‖s‖ = s := by rw [Real.norm_eq_abs, abs_of_pos hslope]
    have h1 : s * ‖q τ - qstar‖ ≤ C * ‖q τ - qstar‖ ^ 2 + ‖τ‖ := by
      have e1 : s * ‖q τ - qstar‖ = ‖s * (q τ - qstar)‖ := by
        rw [norm_mul, hnorm_s]
      rw [e1, hrelτ]
      exact (norm_sub_le _ _).trans (add_le_add hRqτ le_rfl)
    have h2 : C * ‖q τ - qstar‖ ^ 2 ≤ (s / 2) * ‖q τ - qstar‖ := by
      have hC' : C * ‖q τ - qstar‖ ≤ s / 2 := by
        calc C * ‖q τ - qstar‖ ≤ C * (s / (2 * C)) :=
              mul_le_mul_of_nonneg_left hsmallτ (le_of_lt hC_pos)
          _ = s / 2 := by field_simp
      calc C * ‖q τ - qstar‖ ^ 2 = (C * ‖q τ - qstar‖) * ‖q τ - qstar‖ := by ring
        _ ≤ (s / 2) * ‖q τ - qstar‖ :=
          mul_le_mul_of_nonneg_right hC' (norm_nonneg _)
    have h2' : s * ‖q τ - qstar‖ = 2 * ((s / 2) * ‖q τ - qstar‖) := by ring
    have h3 : (s / 2) * ‖q τ - qstar‖ ≤ ‖τ‖ := by linarith
    have hsinv : (2 / s) * (s / 2) = 1 := by field_simp
    calc ‖q τ - qstar‖ = ((2 / s) * (s / 2)) * ‖q τ - qstar‖ := by rw [hsinv, one_mul]
      _ = (2 / s) * ((s / 2) * ‖q τ - qstar‖) := by ring
      _ ≤ (2 / s) * ‖τ‖ := by
        apply mul_le_mul_of_nonneg_left h3
        apply div_nonneg zero_le_two (le_of_lt hslope)
  have hD : (fun τ : ℝ => q τ - qstar) =O[𝓝 0] (fun τ : ℝ => τ) :=
    Asymptotics.IsBigO.of_bound (2 / s) hlin
  have hD2 : (fun τ : ℝ => (q τ - qstar) ^ 2) =O[𝓝 0] (fun τ : ℝ => τ ^ 2) :=
    (hD.mul hD).congr (fun τ => by ring) (fun τ => by ring)
  have hRqO : (fun τ : ℝ => (Pd (q τ) - Ps (q τ)) + s * (q τ - qstar))
      =O[𝓝 0] (fun τ : ℝ => τ ^ 2) := by
    have h1 : (fun τ : ℝ => (Pd (q τ) - Ps (q τ)) + s * (q τ - qstar))
        =O[𝓝 0] (fun τ : ℝ => (q τ - qstar) ^ 2) :=
      Asymptotics.IsBigO.of_bound C (by
        filter_upwards [hRq] with τ hτ
        show ‖(Pd (q τ) - Ps (q τ)) + s * (q τ - qstar)‖ ≤ C * ‖(q τ - qstar) ^ 2‖
        rw [norm_pow]
        exact hτ)
    exact h1.trans hD2
  have hτ2τ : (fun τ : ℝ => τ ^ 2) =O[𝓝 0] (fun τ : ℝ => τ) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    have h1 : ∀ᶠ τ in 𝓝 (0:ℝ), ‖τ‖ ≤ 1 := by
      have h2 : ∀ᶠ y in 𝓝 (‖(0:ℝ)‖), y ≤ 1 := by
        rw [norm_zero]
        exact (eventually_lt_nhds one_pos).mono (fun y hy => le_of_lt hy)
      have h3 : Filter.Tendsto (fun y : ℝ => ‖y‖) (𝓝 0) (𝓝 ‖(0:ℝ)‖) :=
        continuous_norm.tendsto 0
      exact h3.eventually h2
    filter_upwards [h1] with τ hτ
    show ‖τ ^ 2‖ ≤ 1 * ‖τ‖
    rw [norm_pow]
    calc ‖τ‖ ^ 2 = ‖τ‖ * ‖τ‖ := by ring
      _ ≤ 1 * ‖τ‖ := mul_le_mul_of_nonneg_right hτ (norm_nonneg _)
  have hRqO1 : (fun τ : ℝ => (Pd (q τ) - Ps (q τ)) + s * (q τ - qstar))
      =O[𝓝 0] (fun τ : ℝ => τ) := hRqO.trans hτ2τ
  have hF1 : (fun τ : ℝ => s * (q τ - qstar) - τ) =O[𝓝 0] (fun τ : ℝ => τ) := by
    have hDecomp : (fun τ : ℝ => s * (q τ - qstar) - τ)
        =ᶠ[𝓝 (0:ℝ)] (fun τ : ℝ => ((Pd (q τ) - Ps (q τ)) + s * (q τ - qstar)) - 2 * τ) := by
      filter_upwards [hrel] with τ hτ
      show s * (q τ - qstar) - τ = ((Pd (q τ) - Ps (q τ)) + s * (q τ - qstar)) - 2 * τ
      linear_combination hτ
    have hconst : (fun τ : ℝ => -(2 * τ)) =O[𝓝 0] (fun τ : ℝ => τ) := by
      refine Asymptotics.IsBigO.of_bound 2 ?_
      filter_upwards with τ
      show ‖-(2 * τ)‖ ≤ 2 * ‖τ‖
      rw [norm_neg, norm_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have hR2 : (fun τ : ℝ => ((Pd (q τ) - Ps (q τ)) + s * (q τ - qstar)) - 2 * τ)
        =O[𝓝 0] (fun τ : ℝ => τ) := by
      have hadd := hRqO1.add hconst
      refine hadd.congr (fun τ => by ring) (fun τ => rfl)
    exact hR2.congr' hDecomp.symm EventuallyEq.rfl
  have hF2 : (fun τ : ℝ => s * (q τ - qstar) + τ) =O[𝓝 0] (fun τ : ℝ => τ ^ 2) := by
    have hDecomp : (fun τ : ℝ => s * (q τ - qstar) + τ)
        =ᶠ[𝓝 (0:ℝ)] (fun τ : ℝ => (Pd (q τ) - Ps (q τ)) + s * (q τ - qstar)) := by
      filter_upwards [hrel] with τ hτ
      show s * (q τ - qstar) + τ = (Pd (q τ) - Ps (q τ)) + s * (q τ - qstar)
      linear_combination hτ
    exact hRqO.congr' hDecomp.symm EventuallyEq.rfl
  have hMain : (fun τ : ℝ => s * (q τ - qstar) ^ 2 / 2 - τ ^ 2 / (2 * s))
      =O[𝓝 0] (fun τ : ℝ => τ ^ 3) := by
    obtain ⟨c₁, hc₁_nonneg, hc₁⟩ := isBigO_nonneg_bound hF1
    obtain ⟨c₂, hc₂_nonneg, hc₂⟩ := isBigO_nonneg_bound hF2
    have hAlg : ∀ τ : ℝ, s * (q τ - qstar) ^ 2 / 2 - τ ^ 2 / (2 * s)
        = (s * (q τ - qstar) - τ) * (s * (q τ - qstar) + τ) / (2 * s) := by
      intro τ
      field_simp
      ring
    have h2s_pos : (0:ℝ) < ‖2 * s‖ := by
      have h2s : (0:ℝ) < 2 * s := by linarith [hslope]
      rw [Real.norm_eq_abs, abs_of_pos h2s]
      exact h2s
    refine Asymptotics.IsBigO.of_bound (c₁ * c₂ / ‖2 * s‖) ?_
    filter_upwards [hc₁, hc₂] with τ h1 h2
    show ‖s * (q τ - qstar) ^ 2 / 2 - τ ^ 2 / (2 * s)‖ ≤ (c₁ * c₂ / ‖2 * s‖) * ‖τ ^ 3‖
    rw [hAlg]
    have h1' : ‖s * (q τ - qstar) - τ‖ ≤ c₁ * ‖τ‖ := h1
    have h2' : ‖s * (q τ - qstar) + τ‖ ≤ c₂ * ‖τ‖ ^ 2 := by
      rw [← norm_pow]
      exact h2
    rw [norm_div, norm_mul, norm_pow]
    rw [div_le_iff₀ h2s_pos]
    have hK : (c₁ * c₂ / ‖2 * s‖ * ‖τ‖ ^ 3) * ‖2 * s‖
        = (c₁ * ‖τ‖) * (c₂ * ‖τ‖ ^ 2) := by
      have h2s_ne' : ‖2 * s‖ ≠ 0 := ne_of_gt h2s_pos
      field_simp
    rw [hK]
    exact mul_le_mul h1' h2' (norm_nonneg _) (mul_nonneg hc₁_nonneg (norm_nonneg _))
  obtain ⟨rR, hrR_pos, hrR_sub⟩ := Metric.mem_nhds_iff.mp hCR'
  obtain ⟨uR, huR_mem, huR⟩ := hR_at.contDiffOn le_rfl (fun h => absurd h (by decide))
  obtain ⟨rC, hrC_pos, hrC_sub⟩ := Metric.mem_nhds_iff.mp huR_mem
  have hr0_pos : (0 : ℝ) < min rR rC := lt_min hrR_pos hrC_pos
  have hR_on : ContDiffOn ℝ 2 (fun x => (Pd x - Ps x) + s * (x - qstar))
      (Metric.ball qstar (min rR rC)) :=
    huR.mono (fun y hy => hrC_sub (by
      rw [Metric.mem_ball] at hy ⊢
      exact lt_of_lt_of_le hy (min_le_right rR rC)))
  have hRbound_on : ∀ y ∈ Metric.ball qstar (min rR rC),
      ‖(Pd y - Ps y) + s * (y - qstar)‖ ≤ C * ‖y - qstar‖ ^ 2 := fun y hy =>
    hrR_sub (by
      rw [Metric.mem_ball] at hy ⊢
      exact lt_of_lt_of_le hy (min_le_left rR rC))
  have hqball : ∀ᶠ τ in 𝓝 (0:ℝ), q τ ∈ Metric.ball qstar (min rR rC) :=
    hqtend.eventually (Metric.ball_mem_nhds qstar hr0_pos)
  have hsplit : ∀ᶠ τ in 𝓝 (0:ℝ), deadweightLoss Pd Ps qstar (q τ)
      = (∫ x in (q τ)..qstar, ((Pd x - Ps x) + s * (x - qstar)))
        + s * (q τ - qstar) ^ 2 / 2 := by
    filter_upwards [hqball] with τ hqτ
    have hseg : Set.uIcc (q τ) qstar ⊆ Metric.ball qstar (min rR rC) := by
      rw [← segment_eq_uIcc]
      exact (convex_ball _ _).segment_subset hqτ (Metric.mem_ball_self hr0_pos)
    have hRcont : ContinuousOn (fun x => (Pd x - Ps x) + s * (x - qstar))
        (Set.uIcc (q τ) qstar) := hR_on.continuousOn.mono hseg
    have hIntR : IntervalIntegrable (fun x => (Pd x - Ps x) + s * (x - qstar))
        MeasureTheory.volume (q τ) qstar := hRcont.intervalIntegrable
    have hIntA : IntervalIntegrable (fun x : ℝ => -(s * (x - qstar)))
        MeasureTheory.volume (q τ) qstar := by
      exact (by continuity : Continuous (fun x : ℝ => -(s * (x - qstar)))).intervalIntegrable _ _
    have hsplit_eq :
        (∫ x in (q τ)..qstar, (((Pd x - Ps x) + s * (x - qstar)) + (-(s * (x - qstar)))))
        = (∫ x in (q τ)..qstar, ((Pd x - Ps x) + s * (x - qstar)))
          + (∫ x in (q τ)..qstar, (-(s * (x - qstar)))) :=
      intervalIntegral.integral_add hIntR hIntA
    have hFTCaff : (∫ x in (q τ)..qstar, (-(s * (x - qstar))))
        = s * (q τ - qstar) ^ 2 / 2 := by
      have hint2 : IntervalIntegrable (fun x : ℝ => -((s / 2) * (2 * (x - qstar))))
          MeasureTheory.volume (q τ) qstar := by
        exact (by continuity : Continuous (fun x : ℝ => -((s / 2) * (2 * (x - qstar))))
          ).intervalIntegrable _ _
      have hFTC : (∫ x in (q τ)..qstar, (-((s / 2) * (2 * (x - qstar)))))
          = (-((s / 2) * (qstar - qstar) ^ 2)) - (-((s / 2) * (q τ - qstar) ^ 2)) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x _ => hasDerivAt_quad_antideriv s qstar x) hint2
      have hfun : (fun x : ℝ => -((s / 2) * (2 * (x - qstar))))
          = (fun x : ℝ => -(s * (x - qstar))) := by
        ext x; ring
      rw [← hfun] at ⊢
      rw [hFTC, sub_self]
      ring
    change deadweightLoss Pd Ps qstar (q τ)
      = (∫ x in (q τ)..qstar, ((Pd x - Ps x) + s * (x - qstar))) + s * (q τ - qstar) ^ 2 / 2
    have hfun2 : (fun x => Pd x - Ps x)
        = (fun x => ((Pd x - Ps x) + s * (x - qstar)) + (-(s * (x - qstar)))) := by
      ext x; ring
    have hdw : deadweightLoss Pd Ps qstar (q τ)
        = (∫ x in (q τ)..qstar, (((Pd x - Ps x) + s * (x - qstar)) + (-(s * (x - qstar))))) := by
      unfold deadweightLoss
      rw [hfun2]
    rw [hdw, hsplit_eq, hFTCaff]
  have hT2 : (fun τ : ℝ => ∫ x in (q τ)..qstar, ((Pd x - Ps x) + s * (x - qstar)))
      =O[𝓝 0] (fun τ : ℝ => τ ^ 3) := by
    refine Asymptotics.IsBigO.of_bound (C * (2 / s) ^ 3) ?_
    filter_upwards [hqball, hlin] with τ hqτ hlinτ
    show ‖∫ x in (q τ)..qstar, ((Pd x - Ps x) + s * (x - qstar))‖ ≤ (C * (2 / s) ^ 3) * ‖τ ^ 3‖
    have hseg : Set.uIcc (q τ) qstar ⊆ Metric.ball qstar (min rR rC) := by
      rw [← segment_eq_uIcc]
      exact (convex_ball _ _).segment_subset hqτ (Metric.mem_ball_self hr0_pos)
    have hpt : ∀ t ∈ Set.uIoc (q τ) qstar,
        ‖(Pd t - Ps t) + s * (t - qstar)‖ ≤ C * ‖q τ - qstar‖ ^ 2 := by
      intro t ht
      have ht_cc : t ∈ Set.uIcc (q τ) qstar := by
        rw [Set.mem_uIoc] at ht
        rw [Set.mem_uIcc]
        rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1.le, h2⟩
        · exact Or.inr ⟨h1.le, h2⟩
      have hle : ‖(Pd t - Ps t) + s * (t - qstar)‖ ≤ C * ‖t - qstar‖ ^ 2 :=
        hRbound_on t (hseg ht_cc)
      have habs : ‖t - qstar‖ ≤ ‖q τ - qstar‖ := (norm_sub_le_of_mem_uIoc ht).2
      calc ‖(Pd t - Ps t) + s * (t - qstar)‖ ≤ C * ‖t - qstar‖ ^ 2 := hle
        _ ≤ C * ‖q τ - qstar‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) habs 2) (le_of_lt hC_pos)
    have hnorm : ‖∫ x in (q τ)..qstar, ((Pd x - Ps x) + s * (x - qstar))‖
        ≤ (C * ‖q τ - qstar‖ ^ 2) * |qstar - q τ| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpt
    have habs2 : |qstar - q τ| = ‖q τ - qstar‖ :=
      (Real.norm_eq_abs _).symm.trans (norm_sub_rev _ _)
    rw [habs2] at hnorm
    have hcube : ‖q τ - qstar‖ ^ 3 ≤ ((2 / s) * ‖τ‖) ^ 3 :=
      pow_le_pow_left₀ (norm_nonneg _) hlinτ 3
    calc ‖∫ x in (q τ)..qstar, ((Pd x - Ps x) + s * (x - qstar))‖
        ≤ (C * ‖q τ - qstar‖ ^ 2) * ‖q τ - qstar‖ := hnorm
      _ = C * ‖q τ - qstar‖ ^ 3 := by ring
      _ ≤ C * (((2 / s) * ‖τ‖) ^ 3) := mul_le_mul_of_nonneg_left hcube (le_of_lt hC_pos)
      _ = (C * (2 / s) ^ 3) * ‖τ ^ 3‖ := by rw [norm_pow]; ring
  have hFinalEq : (fun τ : ℝ => deadweightLoss Pd Ps qstar (q τ) - τ ^ 2 / (2 * s))
      =ᶠ[𝓝 0] (fun τ : ℝ => (s * (q τ - qstar) ^ 2 / 2 - τ ^ 2 / (2 * s))
        + (∫ x in (q τ)..qstar, ((Pd x - Ps x) + s * (x - qstar)))) := by
    filter_upwards [hsplit] with τ hτ
    show deadweightLoss Pd Ps qstar (q τ) - τ ^ 2 / (2 * s)
      = (s * (q τ - qstar) ^ 2 / 2 - τ ^ 2 / (2 * s))
        + (∫ x in (q τ)..qstar, ((Pd x - Ps x) + s * (x - qstar)))
    rw [hτ]
    ring
  have hAdd : (fun τ : ℝ => (s * (q τ - qstar) ^ 2 / 2 - τ ^ 2 / (2 * s))
        + (∫ x in (q τ)..qstar, ((Pd x - Ps x) + s * (x - qstar))))
      =O[𝓝 0] (fun τ : ℝ => τ ^ 3) := hMain.add hT2
  exact hAdd.congr' hFinalEq.symm EventuallyEq.rfl

end MathlibExt.Economics.DeadweightLoss
