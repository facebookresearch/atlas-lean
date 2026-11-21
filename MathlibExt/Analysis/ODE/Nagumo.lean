/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Topology.MetricSpace.HausdorffDistance
import MathlibExt.Analysis.ODE.MaximalSolution

/-!
# Nagumo's invariance theorem

The closed set need not be convex or have smooth boundary. Tangency uses
positive time increments (the Bouligand contingent cone), not the two-sided
`tangentConeAt ℝ`. Invariance is asserted only while a solution exists.
The proof bounds the lower right Dini slope of the distance to the set. Nearest
points exist by finite-dimensional properness. A compact ball containing both
the trajectory and its nearest points supplies one Lipschitz constant, so the
liminf form of Grönwall keeps the distance zero. Necessity uses local existence.

Source: M. Nagumo, Über die Lage der Integralkurven gewöhnlicher
Differentialgleichungen, Proc. Phys.-Math. Soc. Japan 24 (1942), 551–559.
See also Ghorbal et al., A Hierarchy of Proof Rules for Checking Positive
Invariance, https://logic.kastel.kit.edu/pub/alginv-bench-long.pdf.
-/
@[expose] public section
open Set Filter Metric
open scoped Topology NNReal
namespace Nagumo

/-- Positive-time contingent tangency at a point of an arbitrary closed set. -/
def IsContingent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set E) (x v : E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ →
    ∃ h : ℝ, 0 < h ∧ h < δ ∧ ∃ y ∈ s, ‖y - x - h • v‖ ≤ ε * h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem derivative_error {u : ℝ → E} {v : E} {t ε : ℝ}
    (hu : HasDerivWithinAt u v (Ici t) t) (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : ℝ, 0 < h → h < δ →
      ‖u (t + h) - u t - h • v‖ ≤ ε * h := by
  obtain ⟨δ, hδ, hbound⟩ := Metric.mem_nhdsWithin_iff.mp (hu.isLittleO.def hε)
  refine ⟨δ, hδ, ?_⟩
  intro h hh hhδ
  have hm : t + h ∈ ball t δ ∩ Ici t := by
    constructor
    · simpa [mem_ball, Real.dist_eq, abs_of_pos hh] using hhδ
    · exact le_add_of_nonneg_right hh.le
  simpa [Real.norm_eq_abs, abs_of_pos hh] using hbound hm

/-- A right differentiable curve in a set has a contingent velocity. -/
theorem isContingent_of_curve {s : Set E} {u : ℝ → E} {v : E} {T : ℝ}
    (hT : 0 < T) (hu : HasDerivWithinAt u v (Icc 0 T) 0)
    (hs : MapsTo u (Icc 0 T) s) : IsContingent s (u 0) v := by
  have hd : HasDerivWithinAt u v (Ici 0) 0 :=
    hu.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hT)
  intro ε hε δ hδ
  obtain ⟨r, hr, herror⟩ := derivative_error hd hε
  let h := min (min r δ) T / 2
  have hh : 0 < h := by dsimp [h]; positivity
  have hhmin : h < min (min r δ) T := half_lt_self (lt_min (lt_min hr hδ) hT)
  have hhr : h < r := hhmin.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hhδ : h < δ := hhmin.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hhT : h ≤ T := (hhmin.trans_le (min_le_right _ _)).le
  refine ⟨h, hh, hhδ, u h, hs ⟨hh.le, hhT⟩, ?_⟩
  simpa using herror h hh hhr

private theorem distance_step_bound (a b y z p q : E) {h : ℝ} (hh : 0 ≤ h) :
    dist a z ≤ ‖a - b - h • p‖ + dist b y + h * ‖p - q‖ + ‖z - y - h • q‖ := by
  rw [dist_eq_norm, dist_eq_norm]
  have he : a - z = ((a - b - h • p) + (b - y) + h • (p - q)) -
      (z - y - h • q) := by module
  rw [he]
  calc
    _ ≤ ‖(a - b - h • p) + (b - y) + h • (p - q)‖ + ‖z - y - h • q‖ :=
      norm_sub_le _ _
    _ ≤ (‖(a - b - h • p) + (b - y)‖ + ‖h • (p - q)‖) +
        ‖z - y - h • q‖ := by
      linarith [norm_add_le ((a - b - h • p) + (b - y)) (h • (p - q))]
    _ ≤ (‖a - b - h • p‖ + ‖b - y‖ + ‖h • (p - q)‖) +
        ‖z - y - h • q‖ := by
      linarith [norm_add_le (a - b - h • p) (b - y)]
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]

private theorem liminf_distance_slope {s : Set E} {f : E → E} {u : ℝ → E}
    {t K : ℝ} {y : E}
    (hnear : infDist (u t) s = dist (u t) y)
    (htan : IsContingent s y (f y))
    (hu : HasDerivWithinAt u (f (u t)) (Ici t) t)
    (hlip : ‖f (u t) - f y‖ ≤ K * infDist (u t) s) :
    ∀ r, K * infDist (u t) s < r →
      ∃ᶠ z in 𝓝[>] t, (z - t)⁻¹ * (infDist (u z) s - infDist (u t) s) < r := by
  intro r hr
  let ε := (r - K * infDist (u t) s) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨δ, hδ, herr⟩ := derivative_error hu hε
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhdsWithin_iff.mp hU
  obtain ⟨h, hh, hsmall, z, hz, htanerr⟩ := htan ε hε (min δ η) (lt_min hδ hη)
  have hhδ := hsmall.trans_le (min_le_left δ η)
  have hhη := hsmall.trans_le (min_le_right δ η)
  refine ⟨t + h, hball ⟨?_, by simpa using hh⟩, ?_⟩
  · simpa [mem_ball, Real.dist_eq, abs_of_pos hh] using hhη
  have hdist := (infDist_le_dist_of_mem hz (x := u (t + h))).trans
    (distance_step_bound (u (t + h)) (u t) y z (f (u t)) (f y) hh.le)
  have hscaled := mul_le_mul_of_nonneg_left hlip hh.le
  have herror := herr h hh hhδ
  rw [← hnear] at hdist
  have hbound : infDist (u (t + h)) s - infDist (u t) s ≤
      h * (K * infDist (u t) s + 2 * ε) := by nlinarith
  simp only [add_sub_cancel_left]
  rw [← div_eq_inv_mul, div_lt_iff₀ hh]
  dsimp [ε] at hbound
  nlinarith

/-- Contingent tangency preserves a closed set along every existing solution.
Only local Lipschitz continuity is needed; the set need not be convex. -/
theorem mapsTo_of_contingent [FiniteDimensional ℝ E]
    {f : E → E} (hf : LocallyLipschitz f) {s : Set E} (hs : IsClosed s)
    (htan : ∀ x ∈ s, IsContingent s x (f x)) {a b : ℝ} {u : ℝ → E}
    (hu : ∀ t ∈ Icc a b, HasDerivWithinAt u (f (u t)) (Icc a b) t)
    (hu₀ : u a ∈ s) : MapsTo u (Icc a b) s := by
  have hc : ContinuousOn u (Icc a b) := fun t ht => (hu t ht).continuousWithinAt
  obtain ⟨R, hR, hball⟩ :=
    (isCompact_Icc.image_of_continuousOn hc).isBounded.subset_closedBall_lt 0 (u a)
  have hbound (t : ℝ) (ht : t ∈ Icc a b) : dist (u t) (u a) ≤ R :=
    hball ⟨t, ht, rfl⟩
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (u a) (2 * R)) hf.locallyLipschitzOn
  have hslope (t : ℝ) (ht : t ∈ Ico a b) :
      ∀ r, (L : ℝ) * infDist (u t) s < r →
        ∃ᶠ z in 𝓝[>] t, (z - t)⁻¹ * (infDist (u z) s - infDist (u t) s) < r := by
    obtain ⟨y, hy, hnear⟩ := hs.exists_infDist_eq_dist ⟨u a, hu₀⟩ (u t)
    have ht' := Ico_subset_Icc_self ht
    have hty : dist (u t) y ≤ R := by
      rw [← hnear]
      exact (infDist_le_dist_of_mem hu₀).trans (hbound t ht')
    have hyt : y ∈ closedBall (u a) (2 * R) := by
      change dist y (u a) ≤ 2 * R
      have htri := dist_triangle y (u t) (u a)
      rw [dist_comm y (u t)] at htri
      linarith [hbound t ht']
    have hut : u t ∈ closedBall (u a) (2 * R) := by
      change dist (u t) (u a) ≤ 2 * R
      linarith [hbound t ht']
    have hdiff := hL.dist_le_mul (u t) hut y hyt
    rw [← hnear, dist_eq_norm] at hdiff
    exact liminf_distance_slope hnear (htan y hy)
      ((hu t ht').mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))) hdiff
  have hgron := le_gronwallBound_of_liminf_deriv_right_le
    (f := fun t => infDist (u t) s) (f' := fun t => (L : ℝ) * infDist (u t) s)
    (δ := 0) (K := (L : ℝ)) (ε := 0)
    ((continuous_infDist_pt s).comp_continuousOn hc) hslope
    (by simp [infDist_zero_of_mem hu₀]) (by intro t ht; simp)
  intro t ht
  apply (hs.mem_iff_infDist_zero ⟨u a, hu₀⟩).2
  exact le_antisymm (by simpa [gronwallBound_ε0_δ0] using hgron t ht) infDist_nonneg

/-- Invariance forces contingent tangency, by local existence through each point. -/
theorem contingent_of_invariant [FiniteDimensional ℝ E]
    {f : E → E} (hf : LocallyLipschitz f) {s : Set E}
    (hinv : ∀ (T : ℝ), 0 < T → ∀ u : ℝ → E,
      (∀ t ∈ Icc 0 T, HasDerivWithinAt u (f (u t)) (Icc 0 T) t) →
      u 0 ∈ s → ∀ t ∈ Icc 0 T, u t ∈ s) :
    ∀ x ∈ s, IsContingent s x (f x) := by
  intro x hx
  obtain ⟨I, u, hu₀, hI, h0, -, hu, -⟩ :=
    MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_maximal_solution_exit_compact
      univ (fun p => f p.2) 0 x isOpen_univ trivial
      (hf.continuous.comp continuous_snd).continuousOn fun p _ => by
        obtain ⟨L, S, hS, hL⟩ := hf p.2
        exact ⟨L, univ ×ˢ S, prod_mem_nhds univ_mem hS,
          fun t y z hy hz => hL.dist_le_mul y hy.1.2 z hz.1.2⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds h0)
  have hsub : Icc 0 (r / 2) ⊆ I := by
    intro t ht
    apply hball
    simpa [mem_ball, Real.dist_eq, abs_of_nonneg ht.1] using
      ht.2.trans_lt (half_lt_self hr)
  have hderiv : ∀ t ∈ Icc 0 (r / 2),
      HasDerivWithinAt u (f (u t)) (Icc 0 (r / 2)) t :=
    fun t ht => (hu t (hsub ht)).2.hasDerivWithinAt
  have hmaps := hinv (r / 2) (half_pos hr) u hderiv (by simpa [hu₀] using hx)
  have htan := isContingent_of_curve (half_pos hr)
    (hderiv 0 ⟨le_rfl, (half_pos hr).le⟩) hmaps
  simpa [hu₀] using htan

/-- Nagumo's criterion for a locally Lipschitz autonomous vector field. -/
theorem invariant_iff_contingent [FiniteDimensional ℝ E]
    (f : E → E) (hf : LocallyLipschitz f) (s : Set E) (hs : IsClosed s) :
    (∀ x ∈ s, IsContingent s x (f x)) ↔
      ∀ (T : ℝ), 0 < T → ∀ u : ℝ → E,
        (∀ t ∈ Icc 0 T, HasDerivWithinAt u (f (u t)) (Icc 0 T) t) →
        u 0 ∈ s → ∀ t ∈ Icc 0 T, u t ∈ s := by
  constructor
  · intro htan T _ u hu hu₀
    exact mapsTo_of_contingent hf hs htan hu hu₀
  · exact contingent_of_invariant hf

end Nagumo
