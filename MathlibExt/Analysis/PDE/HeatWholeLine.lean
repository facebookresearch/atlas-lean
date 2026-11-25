/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.LaplaceMaximumPrinciple
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Whole-line heat comparison and uniqueness

On each finite strip `[0, T] × ℝ`, continuous classical subsolutions with a
uniform spatial bound `M * exp (c * |x|)` satisfy comparison with their initial
data. We use the strict supersolution
`exp ((ν * k² + 1) * t) * (exp (k*x) + exp (-k*x))`, with `k > c`,
to remove artificial lateral boundaries. Time derivatives at `T` are from the
left; no derivative at initial time is required. Nonnegative constant diffusivity
includes the degenerate equation `uₜ = 0`.

Comparison and same-source uniqueness apply to arbitrary classical fields, not
only convolution formulas. The growth constants must be uniform over the strip.
No unrestricted uniqueness or quadratic-exponential growth theorem is asserted.

Reference: Stanford Math 220B, *Heat Equation*, Theorems 18 and 20,
https://web.stanford.edu/class/math220b/handouts/heateqn.pdf. We prove the
one-dimensional linear-exponential subclass of the source's quadratic-exponential
growth setting, also for subsolutions. The finite-cylinder argument uses the
local maximum facts of `LaplaceMaximumPrinciple`, as in `HeatMaximumPrinciple`.
-/

@[expose] public section

open Set Filter Topology Real Laplacian InnerProductSpace
open scoped ContDiff
open MathlibExt.Analysis.PDE.LaplaceMaximumPrinciple

namespace MathlibExt.Analysis.PDE.HeatWholeLine

/-- Exponential spatial growth with constants uniform on the closed time strip. -/
def HasExpGrowthOnStrip (u : ℝ → ℝ → ℝ) (T : ℝ) : Prop :=
  ∃ M c : ℝ, 0 ≤ M ∧ 0 ≤ c ∧ ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M * exp (c * |x|)

/-- Uniformly bounded fields have uniform exponential strip growth. -/
theorem HasExpGrowthOnStrip.of_bounded {u : ℝ → ℝ → ℝ} {T : ℝ}
    (h : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M) : HasExpGrowthOnStrip u T := by
  obtain ⟨M, hM⟩ := h
  refine ⟨max M 0, 0, le_max_right _ _, le_rfl, fun t ht x => ?_⟩
  simpa only [zero_mul, exp_zero, mul_one] using (hM t ht x).trans (le_max_left M 0)

/-- Differences preserve uniform strip growth, allowing different growth rates. -/
theorem HasExpGrowthOnStrip.sub {u v : ℝ → ℝ → ℝ} {T : ℝ}
    (hu : HasExpGrowthOnStrip u T) (hv : HasExpGrowthOnStrip v T) :
    HasExpGrowthOnStrip (fun t x => u t x - v t x) T := by
  obtain ⟨M, c, hM, hc, hu⟩ := hu
  obtain ⟨N, d, hN, hd, hv⟩ := hv
  refine ⟨M + N, max c d, add_nonneg hM hN, hc.trans (le_max_left _ _), fun t ht x => ?_⟩
  calc
    |u t x - v t x| ≤ |u t x| + |v t x| := abs_sub _ _
    _ ≤ M * exp (c * |x|) + N * exp (d * |x|) := add_le_add (hu t ht x) (hv t ht x)
    _ ≤ M * exp (max c d * |x|) + N * exp (max c d * |x|) := add_le_add
      (mul_le_mul_of_nonneg_left (exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))) hM)
      (mul_le_mul_of_nonneg_left (exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))) hN)
    _ = _ := by ring

private theorem time_derivative_nonneg {f : ℝ → ℝ} {d t : ℝ} (ht : 0 < t)
    (hm : IsMaxOn f (Icc 0 t) t) (hd : HasDerivWithinAt f d (Iic t) t) : 0 ≤ d := by
  have hs : segment ℝ t 0 ⊆ Icc 0 t := by
    rw [segment_symm]
    exact (convex_Icc 0 t).segment_subset (by simp [ht.le]) (by simp [ht.le])
  have h := hm.isLocalMaxOn.hasFDerivWithinAt_nonpos
    (hd.mono Icc_subset_Iic_self).hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset hs)
  simp at h
  nlinarith

private theorem nonpos_on_rectangle {u ut : ℝ → ℝ → ℝ} {ν T R : ℝ}
    (hν : 0 ≤ ν)
    (hc : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc 0 T ×ˢ Icc (-R) R))
    (hx : ∀ t ∈ Ioc 0 T, ∀ x ∈ Ioo (-R) R, ContDiffAt ℝ 2 (u t) x)
    (ht : ∀ t ∈ Ioc 0 T, ∀ x ∈ Ioo (-R) R,
      HasDerivWithinAt (fun s => u s x) (ut t x) (Iic t) t)
    (hpde : ∀ t ∈ Ioc 0 T, ∀ x ∈ Ioo (-R) R,
      ut t x - ν * iteratedDeriv 2 (u t) x < 0)
    (h₀ : ∀ x ∈ Icc (-R) R, u 0 x ≤ 0)
    (hside : ∀ t ∈ Icc 0 T, u t (-R) ≤ 0 ∧ u t R ≤ 0) :
    ∀ t ∈ Icc 0 T, ∀ x ∈ Icc (-R) R, u t x ≤ 0 := by
  intro t htm x hxm
  by_contra hn
  have hpos : 0 < u t x := lt_of_not_ge hn
  obtain ⟨p, hp, hmax⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
    ⟨(t, x), htm, hxm⟩ hc
  have hqt : u t x ≤ u p.1 p.2 :=
    hmax (show (t, x) ∈ Icc 0 T ×ˢ Icc (-R) R from ⟨htm, hxm⟩)
  have hpx : 0 < u p.1 p.2 := hpos.trans_le hqt
  have hp0 : 0 < p.1 := lt_of_le_of_ne hp.1.1 (by
    intro he; apply (not_lt_of_ge (h₀ p.2 hp.2)); simpa only [← he] using hpx)
  have hpl : -R < p.2 := lt_of_le_of_ne hp.2.1 (by
    intro he; have hh := (hside p.1 hp.1).1; rw [he] at hh; exact (not_lt_of_ge hh) hpx)
  have hpr : p.2 < R := lt_of_le_of_ne hp.2.2 (by
    intro he; have hh := (hside p.1 hp.1).2; rw [← he] at hh; exact (not_lt_of_ge hh) hpx)
  have hspace : IsLocalMax (u p.1) p.2 := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hpl, hpr⟩] with y hy
    exact hmax (show (p.1, y) ∈ Icc 0 T ×ˢ Icc (-R) R from ⟨hp.1, hy.1.le, hy.2.le⟩)
  have hd2 : iteratedDeriv 2 (u p.1) p.2 ≤ 0 := by
    simpa only [laplacian_eq_iteratedDeriv_real] using
      laplacian_nonpos_of_isLocalMax (hx p.1 ⟨hp0, hp.1.2⟩ p.2 ⟨hpl, hpr⟩) hspace
  have htime : IsMaxOn (fun s => u s p.2) (Icc 0 p.1) p.1 := by
    intro s hs
    exact hmax (show (s, p.2) ∈ Icc 0 T ×ˢ Icc (-R) R from
      ⟨⟨hs.1, hs.2.trans hp.1.2⟩, hp.2⟩)
  have hdt := time_derivative_nonneg hp0 htime (ht p.1 ⟨hp0, hp.1.2⟩ p.2 ⟨hpl, hpr⟩)
  have hmul := mul_nonpos_of_nonneg_of_nonpos hν hd2
  linarith [hpde p.1 ⟨hp0, hp.1.2⟩ p.2 ⟨hpl, hpr⟩]

private noncomputable def barrier (ν k t x : ℝ) : ℝ :=
  exp ((ν * k ^ 2 + 1) * t) * (exp (k * x) + exp (-k * x))

private theorem barrier_pos (ν k t x : ℝ) : 0 < barrier ν k t x := by
  unfold barrier
  positivity

private theorem barrier_contDiff (ν k t : ℝ) : ContDiff ℝ 2 (barrier ν k t) := by
  unfold barrier
  fun_prop

private theorem barrier_time (ν k t x : ℝ) :
    HasDerivAt (fun s => barrier ν k s x) ((ν * k ^ 2 + 1) * barrier ν k t x) t := by
  convert (((hasDerivAt_id' t).const_mul (ν * k ^ 2 + 1)).exp.mul_const
    (exp (k * x) + exp (-k * x))) using 1
  · rfl
  · dsimp [barrier]; ring

private theorem barrier_space (ν k t x : ℝ) :
    iteratedDeriv 2 (barrier ν k t) x = k ^ 2 * barrier ν k t x := by
  unfold barrier
  rw [show (fun x => exp ((ν * k ^ 2 + 1) * t) * (exp (k * x) + exp (-k * x))) =
    (fun x => exp ((ν * k ^ 2 + 1) * t) • (exp (k * x) + exp (-k * x))) from rfl,
    iteratedDeriv_fun_const_smul_field,
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop)]
  simp only [iteratedDeriv_exp_const_mul, smul_eq_mul, neg_sq]
  ring

private theorem barrier_lower {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (k x : ℝ) :
    exp (k * |x|) ≤ barrier ν k t x := by
  have he : exp (k * |x|) ≤ exp (k * x) + exp (-k * x) := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]; exact le_add_of_nonneg_right (exp_pos _).le
    · rw [abs_of_nonpos hx, mul_neg, neg_mul]
      exact le_add_of_nonneg_left (exp_pos _).le
  exact he.trans (le_mul_of_one_le_left (by positivity)
    (one_le_exp_iff.mpr (mul_nonneg (by positivity) ht)))

/-- A whole-line heat subsolution with a uniform one-sided exponential strip bound
and nonpositive initial data is nonpositive throughout the closed strip. -/
theorem nonpos_of_heat_subsolution_of_le_exp {u ut : ℝ → ℝ → ℝ} {ν T : ℝ}
    (hν : 0 ≤ ν) (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hx : ∀ t ∈ Ioc 0 T, ∀ x, ContDiffAt ℝ 2 (u t) x)
    (ht : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => u s x) (ut t x) (Iic t) t)
    (hsub : ∀ t ∈ Ioc 0 T, ∀ x, ut t x - ν * iteratedDeriv 2 (u t) x ≤ 0)
    (hg : ∃ M c : ℝ, 0 ≤ M ∧ 0 ≤ c ∧
      ∀ t ∈ Icc 0 T, ∀ x, u t x ≤ M * exp (c * |x|))
    (h₀ : ∀ x, u 0 x ≤ 0) : ∀ t ∈ Icc 0 T, ∀ x, u t x ≤ 0 := by
  obtain ⟨M, c, hM, hc0, hg⟩ := hg
  intro t htm x
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε := δ / barrier ν (c + 1) t x
  have hε : 0 < ε := div_pos hδ (barrier_pos _ _ _ _)
  let R := |x| + M / ε + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hRx : x ∈ Icc (-R) R := by
    have hh : |x| ≤ R := by dsimp [R]; linarith [div_nonneg hM hε.le]
    exact abs_le.mp hh
  let v := fun s y => u s y - ε * barrier ν (c + 1) s y
  let vt := fun s y => ut s y - ε * ((ν * (c + 1) ^ 2 + 1) * barrier ν (c + 1) s y)
  have hbc : Continuous (fun p : ℝ × ℝ => barrier ν (c + 1) p.1 p.2) := by
    unfold barrier; fun_prop
  have hvc : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ Icc (-R) R) :=
    (hc.sub (continuousOn_const.mul hbc.continuousOn)).mono (fun _ hp => ⟨hp.1, mem_univ _⟩)
  have hvd (s : ℝ) (hs : s ∈ Ioc 0 T) (y : ℝ) :
      iteratedDeriv 2 (v s) y = iteratedDeriv 2 (u s) y -
        ε * ((c + 1) ^ 2 * barrier ν (c + 1) s y) := by
    change iteratedDeriv 2 (fun y => u s y - ε • barrier ν (c + 1) s y) y = _
    rw [iteratedDeriv_fun_sub (hx s hs y) (by
      exact contDiffAt_const.mul (barrier_contDiff ν (c + 1) s).contDiffAt),
      iteratedDeriv_fun_const_smul_field, barrier_space]
    rfl
  have hvsub (s : ℝ) (hs : s ∈ Ioc 0 T) (y : ℝ) :
      vt s y - ν * iteratedDeriv 2 (v s) y < 0 := by
    rw [hvd s hs y]
    dsimp [vt]
    have hb := mul_pos hε (barrier_pos ν (c + 1) s y)
    nlinarith [hsub s hs y]
  have hbnd (s y : ℝ) (hs : s ∈ Icc 0 T) (hy : |y| = R) : v s y ≤ 0 := by
    have hMe : M ≤ ε * exp R := by
      have hr : M / ε ≤ R := by dsimp [R]; linarith [abs_nonneg x]
      exact ((div_le_iff₀ hε).mp hr).trans
        (by simpa only [mul_comm] using
          (mul_le_mul_of_nonneg_left (by linarith [add_one_le_exp R] : R ≤ exp R) hε.le))
    have hb : M * exp (c * |y|) ≤ ε * barrier ν (c + 1) s y := by
      calc
        _ ≤ (ε * exp R) * exp (c * |y|) :=
          mul_le_mul_of_nonneg_right hMe (exp_pos _).le
        _ = ε * exp ((c + 1) * |y|) := by rw [hy, mul_assoc, ← exp_add]; congr 2; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (barrier_lower hν hs.1 (c + 1) y) hε.le
    exact sub_nonpos.mpr ((hg s hs y).trans hb)
  have hvle := nonpos_on_rectangle (u := v) (ut := vt) hν hvc
    (fun s hs y _ => (hx s hs y).sub
      (contDiffAt_const.mul (barrier_contDiff ν (c + 1) s).contDiffAt))
    (fun s hs y _ => (ht s hs y).sub ((barrier_time ν (c + 1) s y).const_mul ε).hasDerivWithinAt)
    (fun s hs y _ => hvsub s hs y)
    (fun y _ => sub_nonpos.mpr ((h₀ y).trans (mul_pos hε (barrier_pos _ _ _ _)).le))
    (fun s hs => ⟨hbnd s (-R) hs (by rw [abs_neg, abs_of_pos hR]),
      hbnd s R hs (abs_of_pos hR)⟩) t htm x hRx
  have heq : ε * barrier ν (c + 1) t x = δ := div_mul_cancel₀ _ (ne_of_gt (barrier_pos _ _ _ _))
  dsimp [v] at hvle
  linarith

/-- Maximum principle in the two-sided exponential-growth class. -/
theorem nonpos_of_heat_subsolution {u ut : ℝ → ℝ → ℝ} {ν T : ℝ} (hν : 0 ≤ ν)
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hx : ∀ t ∈ Ioc 0 T, ∀ x, ContDiffAt ℝ 2 (u t) x)
    (ht : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => u s x) (ut t x) (Iic t) t)
    (hsub : ∀ t ∈ Ioc 0 T, ∀ x, ut t x - ν * iteratedDeriv 2 (u t) x ≤ 0)
    (hg : HasExpGrowthOnStrip u T) (h₀ : ∀ x, u 0 x ≤ 0) :
    ∀ t ∈ Icc 0 T, ∀ x, u t x ≤ 0 := by
  obtain ⟨M, c, hM, hc0, hg⟩ := hg
  exact nonpos_of_heat_subsolution_of_le_exp hν hc hx ht hsub
    ⟨M, c, hM, hc0, fun t ht x => (le_abs_self _).trans (hg t ht x)⟩ h₀

/-- Whole-line comparison for ordered heat residuals and ordered initial data.
Both fields have uniform exponential growth on the strip; their source terms need
not vanish or be equal. -/
theorem le_of_heat_residual_le {u v ut vt : ℝ → ℝ → ℝ} {ν T : ℝ} (hν : 0 ≤ ν)
    (hcu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hcv : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ univ))
    (hxu : ∀ t ∈ Ioc 0 T, ∀ x, ContDiffAt ℝ 2 (u t) x)
    (hxv : ∀ t ∈ Ioc 0 T, ∀ x, ContDiffAt ℝ 2 (v t) x)
    (htu : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => u s x) (ut t x) (Iic t) t)
    (htv : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => v s x) (vt t x) (Iic t) t)
    (hres : ∀ t ∈ Ioc 0 T, ∀ x,
      ut t x - ν * iteratedDeriv 2 (u t) x ≤ vt t x - ν * iteratedDeriv 2 (v t) x)
    (hgu : HasExpGrowthOnStrip u T) (hgv : HasExpGrowthOnStrip v T)
    (h₀ : ∀ x, u 0 x ≤ v 0 x) : ∀ t ∈ Icc 0 T, ∀ x, u t x ≤ v t x := by
  have hw := nonpos_of_heat_subsolution (u := fun t x => u t x - v t x)
    (ut := fun t x => ut t x - vt t x) hν (hcu.sub hcv)
    (fun t ht x => (hxu t ht x).sub (hxv t ht x))
    (fun t ht x => (htu t ht x).sub (htv t ht x))
    (fun t ht x => by
      rw [iteratedDeriv_fun_sub (hxu t ht x) (hxv t ht x)]
      linarith [hres t ht x]) (hgu.sub hgv) (fun x => sub_nonpos.mpr (h₀ x))
  exact fun t ht x => sub_nonpos.mp (hw t ht x)

/-- The whole-line initial-value problem with a fixed heat source has at most one
classical solution in the uniform exponential-growth class on each finite strip. -/
theorem eq_of_heat_equation {u v ut vt f : ℝ → ℝ → ℝ} {ν T : ℝ} (hν : 0 ≤ ν)
    (hcu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hcv : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ univ))
    (hxu : ∀ t ∈ Ioc 0 T, ∀ x, ContDiffAt ℝ 2 (u t) x)
    (hxv : ∀ t ∈ Ioc 0 T, ∀ x, ContDiffAt ℝ 2 (v t) x)
    (htu : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => u s x) (ut t x) (Iic t) t)
    (htv : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => v s x) (vt t x) (Iic t) t)
    (heu : ∀ t ∈ Ioc 0 T, ∀ x, ut t x - ν * iteratedDeriv 2 (u t) x = f t x)
    (hev : ∀ t ∈ Ioc 0 T, ∀ x, vt t x - ν * iteratedDeriv 2 (v t) x = f t x)
    (hgu : HasExpGrowthOnStrip u T) (hgv : HasExpGrowthOnStrip v T)
    (h₀ : ∀ x, u 0 x = v 0 x) : ∀ t ∈ Icc 0 T, ∀ x, u t x = v t x := by
  have huv := le_of_heat_residual_le hν hcu hcv hxu hxv htu htv
    (fun t ht x => (heu t ht x).trans (hev t ht x).symm |>.le) hgu hgv (fun x => (h₀ x).le)
  have hvu := le_of_heat_residual_le hν hcv hcu hxv hxu htv htu
    (fun t ht x => (hev t ht x).trans (heu t ht x).symm |>.le) hgv hgu (fun x => (h₀ x).ge)
  exact fun t ht x => le_antisymm (huv t ht x) (hvu t ht x)

/-- In particular, bounded-on-strip classical heat solutions with the same source
and initial values coincide. The bound is uniform in both space and strip time. -/
theorem eq_of_heat_equation_of_bounded {u v ut vt f : ℝ → ℝ → ℝ} {ν T : ℝ} (hν : 0 ≤ ν)
    (hcu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hcv : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ univ))
    (hxu : ∀ t ∈ Ioc 0 T, ∀ x, ContDiffAt ℝ 2 (u t) x)
    (hxv : ∀ t ∈ Ioc 0 T, ∀ x, ContDiffAt ℝ 2 (v t) x)
    (htu : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => u s x) (ut t x) (Iic t) t)
    (htv : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => v s x) (vt t x) (Iic t) t)
    (heu : ∀ t ∈ Ioc 0 T, ∀ x, ut t x - ν * iteratedDeriv 2 (u t) x = f t x)
    (hev : ∀ t ∈ Ioc 0 T, ∀ x, vt t x - ν * iteratedDeriv 2 (v t) x = f t x)
    (hbu : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M)
    (hbv : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |v t x| ≤ M)
    (h₀ : ∀ x, u 0 x = v 0 x) : ∀ t ∈ Icc 0 T, ∀ x, u t x = v t x :=
  eq_of_heat_equation hν hcu hcv hxu hxv htu htv heu hev
    (HasExpGrowthOnStrip.of_bounded hbu) (HasExpGrowthOnStrip.of_bounded hbv) h₀

end MathlibExt.Analysis.PDE.HeatWholeLine
