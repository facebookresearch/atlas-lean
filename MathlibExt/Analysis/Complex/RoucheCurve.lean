/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Circle
public import MathlibExt.Topology.Inside
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Meromorphic.Divisor
import MathlibExt.Analysis.Complex.Rouche

/-!
# Rouché's theorem for a simple closed curve

Let `f` and `g` be holomorphic in a region `Ω`, let `γ` be a simple closed curve in `Ω` with
interior contained in `Ω`, and assume `‖f z - g z‖ < ‖f z‖` on `γ`. Then `f` and `g` have the same
number of zeros inside `γ` (`Complex.rouche`).

A simple closed curve is a continuous injective map `γ : Circle → ℂ`. Its interior is
`Set.inside (Set.range γ)`, the points off the curve whose connected component in the complement
is bounded; by the Jordan curve theorem this is the bounded complementary component. Zeros are
counted with multiplicity, via `analyticOrderNatAt`, and both zero sets are proved finite, so the
counts are genuine finite sums.

The proof works for any bounded open set `U` in place of the interior
(`Complex.rouche_of_isBounded`). Along the homotopy `f + t (g - f)`, `t ∈ [0, 1]`, no function
vanishes on `frontier U`, and the number of zeros in `U` is locally constant in `t`: near each zero
it is constant by Rouché's theorem on a small disc
(`MathlibExt.Analysis.Complex.Rouche.rouche_closedBall`), and away from the zeros the functions
stay bounded away from zero. No contour integral over `γ` is needed. Mathlib has no Rouché
theorem, and MathlibExt only had the disc case, in divisor-sum form.

Rubric-guided revision of v1 ComplexVariables target 23 (`rouche_theorem` in
`v1/Atlas/ComplexVariables/code/Lecture14.lean` at commit
`6191bf1ba03d204784385ef5be2472be88035b93`). The archived formalization proved the statement only
for a circle `C(c, R)` instead of a simple closed curve; it assumed that `f` does not vanish on the
circle and that both zero sets are finite, all of which follow from the other hypotheses; it
encoded holomorphy as pointwise differentiability on the closed disc; and its proof depended on two
false `sorry`ed lemmas (`diffContOnCl_piecewise_cauchy_extension` and
`continuousOn_deriv_of_differentiableAt_closedBall`). The archived formalization and its original
license/provenance remain in `v1/` (the original license text is `v1/LICENSE`).
-/

set_option autoImplicit false

open Metric Set Filter Topology Bornology

namespace Complex

variable {U S : Set ℂ} {f g h p : ℂ → ℂ}

/-- A function analytic near `closure U`, for a bounded open set `U`, that does not vanish on
`frontier U` has finitely many zeros in `closure U`. -/
private theorem finite_zeros (hU : IsOpen U) (hUb : IsBounded U)
    (hh : AnalyticOnNhd ℂ h (closure U)) (h0 : ∀ z ∈ frontier U, h z ≠ 0) :
    {z ∈ closure U | h z = 0}.Finite := by
  -- `h` does not vanish identically near any point of `closure U`
  have htop : ∀ z ∈ closure U, analyticOrderAt h z ≠ ⊤ := by
    intro z hz htop
    rw [analyticOrderAt_eq_top] at htop
    have hzU : z ∈ U := by
      by_contra hzU
      exact h0 z (by rw [hU.frontier_eq]; exact ⟨hz, hzU⟩) htop.self_of_nhds
    have hCo : IsOpen (connectedComponentIn U z) := hU.connectedComponentIn
    have hzC : z ∈ connectedComponentIn U z := mem_connectedComponentIn hzU
    have hCU : connectedComponentIn U z ⊆ U := connectedComponentIn_subset U z
    -- by the identity theorem `h` vanishes on the component of `z` in `U`
    have hC0 : EqOn h 0 (connectedComponentIn U z) :=
      (hh.mono (hCU.trans subset_closure)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_connectedComponentIn hzC htop
    -- that component is open, nonempty and bounded, so it has a closure point outside it
    obtain ⟨w, hwC, hwnC⟩ : ∃ w ∈ closure (connectedComponentIn U z),
        w ∉ connectedComponentIn U z := by
      by_contra! H
      rcases isClopen_iff.1 ⟨isClosed_of_closure_subset H, hCo⟩ with hCe | hCu
      · rw [hCe] at hzC
        simp at hzC
      · exact NormedSpace.unbounded_univ ℝ ℂ (hCu ▸ hUb.subset hCU)
    -- such a point lies on `frontier U`, where `h` does not vanish
    have hwU : w ∉ U := by
      intro hwU
      obtain ⟨v, hvw, hvC⟩ :=
        mem_closure_iff.1 hwC _ hU.connectedComponentIn (mem_connectedComponentIn hwU)
      apply hwnC
      rw [connectedComponentIn_eq hvC, ← connectedComponentIn_eq hvw]
      exact mem_connectedComponentIn hwU
    have hcl : EqOn h 0 (closure (connectedComponentIn U z)) :=
      hC0.of_subset_closure (hh.continuousOn.mono (closure_mono hCU))
        continuous_zero.continuousOn subset_closure subset_rfl
    exact h0 w (by rw [hU.frontier_eq]; exact ⟨closure_mono hCU hwC, hwU⟩) (hcl hwC)
  -- so its zeros are in the support of its divisor on the compact set `closure U`
  refine ((MeromorphicOn.divisor h (closure U)).finiteSupport hUb.isCompact_closure).subset ?_
  rintro z ⟨hz, hz0⟩
  rw [Function.mem_support, MeromorphicOn.divisor_apply hh.meromorphicOn hz,
    (hh z hz).meromorphicOrderAt_eq]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (htop z hz)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact (hh z hz).analyticOrderAt_eq_zero.1 (by simpa using hn.symm) hz0
  rw [← hn]
  simpa using hn0

/-- On a set where `h` is analytic, the divisor of `h` counts zeros with multiplicity. -/
private theorem divisor_apply_eq_indicator (hh : AnalyticOnNhd ℂ h S) (z : ℂ) :
    MeromorphicOn.divisor h S z = S.indicator (fun w => (analyticOrderNatAt h w : ℤ)) z := by
  by_cases hz : z ∈ S
  · rw [MeromorphicOn.divisor_apply hh.meromorphicOn hz, (hh z hz).meromorphicOrderAt_eq,
      indicator_of_mem hz]
    simp only [analyticOrderNatAt]
    generalize analyticOrderAt h z = n
    induction n using ENat.recTopCoe <;> simp
  · rw [indicator_of_notMem hz]
    exact (MeromorphicOn.divisor h S).apply_eq_zero_of_notMem hz

/-- The divisor sum of `h` on a set `S` where `h` is analytic with finitely many zeros is the
number of zeros of `h` in `S`, counted with multiplicity. -/
private theorem finsum_divisor_eq (hh : AnalyticOnNhd ℂ h S)
    (hfin : {z ∈ S | h z = 0}.Finite) :
    ∑ᶠ z, MeromorphicOn.divisor h S z = ((∑ᶠ z ∈ S, analyticOrderNatAt h z : ℕ) : ℤ) := by
  have hsupp : (Function.support (S.indicator fun z => analyticOrderNatAt h z)).Finite := by
    refine hfin.subset fun z hz => ?_
    rw [Function.mem_support] at hz
    have hzS : z ∈ S := by
      by_contra hzS
      exact hz (indicator_of_notMem hzS _)
    refine ⟨hzS, ?_⟩
    rw [indicator_of_mem hzS] at hz
    by_contra hz0
    exact hz (by simp [analyticOrderNatAt, (hh z hzS).analyticOrderAt_eq_zero.2 hz0])
  have hcast := (Nat.castAddMonoidHom ℤ).map_finsum hsupp
  rw [Nat.coe_castAddMonoidHom] at hcast
  rw [finsum_mem_def, hcast]
  refine finsum_congr fun z => ?_
  rw [divisor_apply_eq_indicator hh]
  by_cases hz : z ∈ S <;> simp [hz]

/-- Rouché's theorem on a disc, counting zeros with multiplicity: if `‖g‖ < ‖f‖` on the circle,
then `f + g` and `f` have the same number of zeros in the open disc. -/
private theorem finsum_ball_add_eq {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) (hg : AnalyticOnNhd ℂ g (closedBall c r))
    (hfg : ∀ z ∈ sphere c r, ‖g z‖ < ‖f z‖) :
    ∑ᶠ z ∈ ball c r, analyticOrderNatAt (fun w => f w + g w) z =
      ∑ᶠ z ∈ ball c r, analyticOrderNatAt f z := by
  have hfg' : AnalyticOnNhd ℂ (fun w => f w + g w) (closedBall c r) := hf.add hg
  have hfin : ∀ F : ℂ → ℂ, AnalyticOnNhd ℂ F (closedBall c r) →
      (∀ z ∈ sphere c r, F z ≠ 0) → {z ∈ ball c r | F z = 0}.Finite := by
    intro F hF hF0
    rw [← closure_ball c hr.ne'] at hF
    rw [← frontier_ball c hr.ne'] at hF0
    exact (finite_zeros isOpen_ball isBounded_ball hF hF0).subset
      fun z hz => ⟨subset_closure hz.1, hz.2⟩
  have hf0 : ∀ z ∈ sphere c r, f z ≠ 0 := fun z hz hz0 => by
    have h1 := hfg z hz
    rw [hz0, norm_zero] at h1
    exact (norm_nonneg _).not_gt h1
  have hfg0 : ∀ z ∈ sphere c r, f z + g z ≠ 0 := fun z hz hz0 => by
    have h1 := hfg z hz
    rw [eq_neg_of_add_eq_zero_left hz0, norm_neg] at h1
    exact lt_irrefl _ h1
  have hR := MathlibExt.Analysis.Complex.Rouche.rouche_closedBall hr hf hg hfg
  rw [finsum_divisor_eq (hf.mono ball_subset_closedBall) (hfin f hf hf0),
    finsum_divisor_eq (hfg'.mono ball_subset_closedBall) (hfin _ hfg' hfg0)] at hR
  exact_mod_cast hR.symm

/-- Around the points of a finite subset `Z` of an open set `U` there are closed discs of a common
radius `r > 0` that lie in `U` and whose centres are more than `2 r` apart. -/
private theorem exists_separated_closedBalls {Z : Set ℂ} (hU : IsOpen U) (hZ : Z.Finite)
    (hZU : Z ⊆ U) :
    ∃ r > 0, (∀ z ∈ Z, closedBall z r ⊆ U) ∧ ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → 2 * r < dist z z' := by
  have h1 : ∀ z ∈ Z, ∀ᶠ r in 𝓝[>] (0 : ℝ), closedBall z r ⊆ U := by
    intro z hz
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hU z (hZU hz)
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    exact (closedBall_subset_ball hr.2).trans hδU
  have h2 : ∀ z ∈ Z, ∀ z' ∈ Z, ∀ᶠ r in 𝓝[>] (0 : ℝ), z ≠ z' → 2 * r < dist z z' := by
    intro z _ z' _
    by_cases hzz : z = z'
    · exact Eventually.of_forall fun _ hne => absurd hzz hne
    · filter_upwards [Ioo_mem_nhdsGT (half_pos (dist_pos.2 hzz))] with r hr _
      linarith [hr.2]
  have h3 := ((eventually_all_finite hZ).2 h1).and
    ((eventually_all_finite hZ).2 fun z hz => (eventually_all_finite hZ).2 (h2 z hz))
  obtain ⟨r, ⟨hrU, hrZ⟩, hr⟩ := (h3.and self_mem_nhdsWithin).exists
  exact ⟨r, hr, hrU, hrZ⟩

/-- If `F` has finitely many zeros in `U`, all lying in the union of pairwise disjoint subsets
`B z ⊆ U` indexed by a finite set `Z`, then the number of zeros of `F` in `U` is the sum of its
numbers of zeros in the sets `B z`, counted with multiplicity. -/
private theorem finsum_mem_eq_finsum_biUnion {Z : Set ℂ} {B : ℂ → Set ℂ} {F : ℂ → ℂ}
    (hZ : Z.Finite) (hBU : ∀ z ∈ Z, B z ⊆ U) (hdisj : Z.PairwiseDisjoint B)
    (hfin : {w ∈ U | F w = 0}.Finite) (hcover : ∀ w ∈ U, F w = 0 → w ∈ ⋃ z ∈ Z, B z) :
    ∑ᶠ w ∈ U, analyticOrderNatAt F w = ∑ᶠ z ∈ Z, ∑ᶠ w ∈ B z, analyticOrderNatAt F w := by
  have hsupp : Function.support (analyticOrderNatAt F) ⊆ {w | F w = 0} := by
    intro w hw
    rw [Function.mem_support] at hw
    rw [mem_ofPred_eq]
    by_contra hw0
    exact hw (by simp [analyticOrderNatAt, analyticOrderAt_eq_zero.2 (Or.inr hw0)])
  have hiff : ∀ w ∈ Function.support (analyticOrderNatAt F),
      w ∈ U ↔ w ∈ ⋃ z ∈ Z, B z ∩ Function.support (analyticOrderNatAt F) := by
    intro w hw
    rw [mem_iUnion₂]
    constructor
    · intro hwU
      obtain ⟨z, hz, hwz⟩ := mem_iUnion₂.1 (hcover w hwU (hsupp hw))
      exact ⟨z, hz, hwz, hw⟩
    · rintro ⟨z, hz, hwz, -⟩
      exact hBU z hz hwz
  have hfinT : ∀ z ∈ Z, (B z ∩ Function.support (analyticOrderNatAt F)).Finite :=
    fun z hz => hfin.subset fun w hw => ⟨hBU z hz hw.1, hsupp hw.2⟩
  rw [finsum_mem_inter_support_eq' _ U _ hiff,
    finsum_mem_biUnion (hdisj.mono fun _ => inter_subset_left) hZ hfinT]
  exact finsum_mem_congr rfl fun z _ => finsum_mem_inter_support _ _

/-- The number of zeros in `U` is stable under small perturbations: if `h` is analytic near
`closure U` and does not vanish on `frontier U`, then `h + s p` has as many zeros in `U` as `h`,
counted with multiplicity, for all small `s`. -/
private theorem eventually_finsum_add_mul_eq (hU : IsOpen U) (hUb : IsBounded U)
    (hh : AnalyticOnNhd ℂ h (closure U)) (hp : AnalyticOnNhd ℂ p (closure U))
    (h0 : ∀ z ∈ frontier U, h z ≠ 0) :
    ∀ᶠ s in 𝓝 (0 : ℂ), ∑ᶠ z ∈ U, analyticOrderNatAt (fun w => h w + s * p w) z =
      ∑ᶠ z ∈ U, analyticOrderNatAt h z := by
  set Z := {z ∈ closure U | h z = 0}
  have hZU : Z ⊆ U := fun z ⟨hz, hz0⟩ => by
    by_contra hzU
    exact h0 z (by rw [hU.frontier_eq]; exact ⟨hz, hzU⟩) hz0
  have hZ : Z.Finite := finite_zeros hU hUb hh h0
  -- pairwise disjoint discs around the zeros of `h`, with closures inside `U`
  obtain ⟨r, hr, hrU, hrZ⟩ := exists_separated_closedBalls hU hZ hZU
  have hBU : ∀ z ∈ Z, ball z r ⊆ U := fun z hz => ball_subset_closedBall.trans (hrU z hz)
  -- off the discs, `‖h‖` has a positive lower bound `m`
  set K := closure U \ ⋃ z ∈ Z, ball z r
  have hKc : IsCompact K := hUb.isCompact_closure.diff (isOpen_biUnion fun _ _ => isOpen_ball)
  have hKh : ∀ w ∈ K, 0 < ‖h w‖ := by
    rintro w ⟨hw, hwB⟩
    rw [norm_pos_iff]
    intro hw0
    exact hwB (mem_biUnion (x := w) ⟨hw, hw0⟩ (mem_ball_self hr))
  obtain ⟨m, hm, hmK⟩ := hKc.exists_forall_le' (hh.continuousOn.mono sdiff_subset).norm hKh
  have hfrK : frontier U ⊆ K := by
    intro w hw
    rw [hU.frontier_eq] at hw
    refine ⟨hw.1, ?_⟩
    rw [mem_iUnion₂]
    rintro ⟨z, hz, hwz⟩
    exact hw.2 (hBU z hz hwz)
  have hsphK : ∀ z ∈ Z, sphere z r ⊆ K := by
    intro z hz w hw
    refine ⟨subset_closure (hrU z hz (sphere_subset_closedBall hw)), ?_⟩
    rw [mem_iUnion₂]
    rintro ⟨z', hz', hwz'⟩
    rw [mem_sphere] at hw
    rw [mem_ball] at hwz'
    by_cases hzz : z = z'
    · subst hzz
      linarith
    · linarith [hrZ z hz z' hz' hzz, dist_triangle_left z z' w]
  -- a function analytic near `closure U` without zeros on `K` has all its zeros in `U` inside
  -- the discs, so its zero count in `U` is the sum of its zero counts in the discs
  have key : ∀ F : ℂ → ℂ, AnalyticOnNhd ℂ F (closure U) → (∀ w ∈ K, F w ≠ 0) →
      ∑ᶠ w ∈ U, analyticOrderNatAt F w =
        ∑ᶠ z ∈ Z, ∑ᶠ w ∈ ball z r, analyticOrderNatAt F w := fun F hF hFK =>
    finsum_mem_eq_finsum_biUnion hZ hBU
      (fun z hz z' hz' hzz => ball_disjoint_ball (by linarith [hrZ z hz z' hz' hzz]))
      ((finite_zeros hU hUb hF fun w hw => hFK w (hfrK hw)).subset
        fun w hw => ⟨subset_closure hw.1, hw.2⟩)
      fun w hw hw0 => Classical.byContradiction fun hwB => hFK w ⟨subset_closure hw, hwB⟩ hw0
  -- for small `s`, `‖s p‖ < m` on `closure U`
  obtain ⟨M, hM⟩ := hUb.isCompact_closure.exists_bound_of_continuousOn hp.continuousOn
  have hM' : 0 < max M 0 + 1 := by positivity
  filter_upwards [ball_mem_nhds (0 : ℂ) (div_pos hm hM')] with s hs
  rw [mem_ball_zero_iff, lt_div_iff₀ hM'] at hs
  have hsp : ∀ w ∈ closure U, ‖s * p w‖ < m := fun w hw => by
    rw [norm_mul]
    calc ‖s‖ * ‖p w‖ ≤ ‖s‖ * (max M 0 + 1) := by
          gcongr
          linarith [hM w hw, le_max_left M 0]
      _ < m := hs
  have hq : AnalyticOnNhd ℂ (fun w => h w + s * p w) (closure U) :=
    hh.add (analyticOnNhd_const.mul hp)
  have hqK : ∀ w ∈ K, h w + s * p w ≠ 0 := by
    intro w hw hq0
    have h1 := hmK w hw
    have h2 := hsp w hw.1
    rw [eq_neg_of_add_eq_zero_left hq0, norm_neg] at h1
    linarith
  rw [key _ hq hqK, key h hh fun w hw => norm_pos_iff.1 (hKh w hw)]
  -- on each disc, Rouché's theorem for the disc compares `h + s p` with `h`
  refine finsum_mem_congr rfl fun z hz => ?_
  have hzB : closedBall z r ⊆ closure U := (hrU z hz).trans subset_closure
  exact finsum_ball_add_eq hr (hh.mono hzB) ((analyticOnNhd_const.mul hp).mono hzB)
    fun w hw => (hsp w (hzB (sphere_subset_closedBall hw))).trans_le (hmK w (hsphK z hz hw))

/-- **Rouché's theorem** for a bounded open set: if `f` and `g` are analytic on a neighbourhood
of `closure U` and `‖f z - g z‖ < ‖f z‖` on `frontier U`, then `f` and `g` have finitely many
zeros in `U`, and the same number of them, counted with multiplicity. -/
public theorem rouche_of_isBounded (hU : IsOpen U) (hUb : IsBounded U)
    (hf : AnalyticOnNhd ℂ f (closure U)) (hg : AnalyticOnNhd ℂ g (closure U))
    (hfg : ∀ z ∈ frontier U, ‖f z - g z‖ < ‖f z‖) :
    {z ∈ U | f z = 0}.Finite ∧ {z ∈ U | g z = 0}.Finite ∧
      ∑ᶠ z ∈ U, analyticOrderNatAt f z = ∑ᶠ z ∈ U, analyticOrderNatAt g z := by
  have hf0 : ∀ z ∈ frontier U, f z ≠ 0 := fun z hz hz0 => by
    have := hfg z hz
    rw [hz0, norm_zero] at this
    exact absurd this (not_lt.2 (norm_nonneg _))
  have hg0 : ∀ z ∈ frontier U, g z ≠ 0 := fun z hz hz0 => by
    have := hfg z hz
    rw [hz0, sub_zero] at this
    exact lt_irrefl _ this
  refine ⟨(finite_zeros hU hUb hf hf0).subset fun z hz => ⟨subset_closure hz.1, hz.2⟩,
    (finite_zeros hU hUb hg hg0).subset fun z hz => ⟨subset_closure hz.1, hz.2⟩, ?_⟩
  -- the homotopy `H t = f + t (g - f)` does not vanish on `frontier U` for `t ∈ [0, 1]`
  let H : ℝ → ℂ → ℂ := fun t z => f z + (t : ℂ) * (g z - f z)
  have hH : ∀ t, AnalyticOnNhd ℂ (H t) (closure U) := fun t =>
    hf.add (analyticOnNhd_const.mul (hg.sub hf))
  have hH0 : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ frontier U, H t z ≠ 0 := by
    rintro t ⟨ht0, ht1⟩ z hz hHz
    have h1 : f z = (t : ℂ) * (f z - g z) := by
      simp only [H] at hHz
      linear_combination hHz
    have h2 := congrArg (‖·‖) h1
    simp only [norm_mul, norm_real, Real.norm_of_nonneg ht0] at h2
    linarith [hfg z hz, mul_le_of_le_one_left (norm_nonneg (f z - g z)) ht1]
  -- so the number of zeros of `H t` in `U` is locally constant on `[0, 1]`
  have hN : ∀ t₀ ∈ Icc (0 : ℝ) 1, ∀ᶠ t in 𝓝 t₀,
      ∑ᶠ z ∈ U, analyticOrderNatAt (H t) z = ∑ᶠ z ∈ U, analyticOrderNatAt (H t₀) z := by
    intro t₀ ht₀
    have h1 := eventually_finsum_add_mul_eq hU hUb (hH t₀) (hg.sub hf) (hH0 t₀ ht₀)
    have h2 : Tendsto (fun t : ℝ => ((t - t₀ : ℝ) : ℂ)) (𝓝 t₀) (𝓝 0) := by
      have : Continuous (fun t : ℝ => ((t - t₀ : ℝ) : ℂ)) := by fun_prop
      simpa using this.tendsto t₀
    filter_upwards [h2.eventually h1] with t ht
    have hfun : (fun w => H t₀ w + ((t - t₀ : ℝ) : ℂ) * (g - f) w) = H t := by
      funext w
      simp only [H, Pi.sub_apply]
      push_cast
      ring
    rw [← hfun]
    exact ht
  have hconst : ∑ᶠ z ∈ U, analyticOrderNatAt (H 0) z = ∑ᶠ z ∈ U, analyticOrderNatAt (H 1) z := by
    refine isPreconnected_Icc.constant (f := fun t => ∑ᶠ z ∈ U, analyticOrderNatAt (H t) z)
      (fun t ht => ?_) (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
    rw [ContinuousWithinAt, nhds_discrete ℕ, tendsto_pure]
    exact (hN t ht).filter_mono nhdsWithin_le_nhds
  have hH0' : H 0 = f := by
    funext z
    simp [H]
  have hH1 : H 1 = g := by
    funext z
    simp [H]
  rwa [hH0', hH1] at hconst

/-- **Rouché's theorem.** Let `f` and `g` be holomorphic in a region `Ω`, let `γ` be a simple
closed curve in `Ω` whose interior `Set.inside (Set.range γ)` lies in `Ω`, and suppose
`‖f z - g z‖ < ‖f z‖` on `γ`. Then `f` and `g` have finitely many zeros inside `γ`, and the same
number of them, counted with multiplicity.

The source's hypotheses that `Ω` is connected (it is a region) and that `γ` is simple are kept as
`_hΩc` and `_hγ` although the proof does not use them: by `rouche_of_isBounded` the conclusion
holds for any closed curve and any open `Ω`. -/
public theorem rouche {Ω : Set ℂ} (hΩ : IsOpen Ω) (_hΩc : IsConnected Ω)
    (hf : DifferentiableOn ℂ f Ω) (hg : DifferentiableOn ℂ g Ω)
    {γ : Circle → ℂ} (hγc : Continuous γ) (_hγ : Function.Injective γ)
    (hγΩ : range γ ⊆ Ω) (hinside : (range γ).inside ⊆ Ω)
    (hfg : ∀ t, ‖f (γ t) - g (γ t)‖ < ‖f (γ t)‖) :
    {z ∈ (range γ).inside | f z = 0}.Finite ∧ {z ∈ (range γ).inside | g z = 0}.Finite ∧
      ∑ᶠ z ∈ (range γ).inside, analyticOrderNatAt f z =
        ∑ᶠ z ∈ (range γ).inside, analyticOrderNatAt g z := by
  have hK : IsCompact (range γ) := isCompact_range hγc
  have hcl : closure (range γ).inside ⊆ Ω :=
    (closure_inside_subset hK.isClosed).trans (union_subset hγΩ hinside)
  refine rouche_of_isBounded (isOpen_inside hK.isClosed) (isBounded_inside hK.isBounded)
    ((hf.analyticOnNhd hΩ).mono hcl) ((hg.analyticOnNhd hΩ).mono hcl) fun z hz => ?_
  obtain ⟨t, rfl⟩ := frontier_inside_subset hK.isClosed hz
  exact hfg t

end Complex
