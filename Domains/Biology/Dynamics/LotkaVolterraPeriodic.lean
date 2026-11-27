/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Domains.Biology.Dynamics.LotkaVolterra
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Positive solutions and periodic orbits of the Lotka–Volterra system

The predator–prey equations are `x' = α x - β x y` and `y' = δ x y - γ y`, with positive
parameters and positive initial populations. The coexistence equilibrium is `(γ / δ, α / β)`.

## Main results

* `pos_of_pos`: populations remain positive at every nonnegative time.
* `exists_global_solution`: a positive solution with prescribed positive initial populations
  exists on all of `ℝ`.
* `eq_of_initial`: two solutions with the same positive initial populations agree at every
  nonnegative time.
* `exists_minimal_period`: a non-equilibrium solution has a simultaneous positive period and
  no earlier positive return to its initial pair. This proves the least positive return time,
  a stronger conclusion than plain periodicity.

## Implementation notes

Positivity follows from scalar ODE uniqueness. A smooth compactly supported cut-off of the
polynomial vector field gives global existence; conservation of the native `firstIntegral`
confines the solution to a bounded positive energy level where the cut-off is one. Local
Lipschitz bounds give uniqueness. Scaled offsets from the equilibrium have angular speed
bounded away from zero, giving a finite return to the initial ray. Convexity of the first
integral turns this into an exact return. The nonzero initial velocity excludes early returns;
compactness gives the least return, and uniqueness gives simultaneous periodicity.

## References

* V. Volterra, *Variations and fluctuations of the number of individuals in animal species
  living together*, J. Cons. Int. Explor. Mer 3 (1928), 3–51, Part I Section 3.
* J. Hofbauer and K. Sigmund, *Evolutionary Games and Population Dynamics*, Cambridge
  University Press (1998), Section 2.2.
-/

open Real Set
open scoped NNReal Topology
open MathlibExt.Biology.Dynamics.LotkaVolterra

namespace Domains.Biology.Dynamics.LotkaVolterra

private theorem scalar_pos {f c : ℝ → ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivAt f (c t * f t) t)
    (hc : ContinuousOn c (Ici 0)) (hf0 : 0 < f 0) {t : ℝ} (ht : 0 ≤ t) :
    0 < f t := by
  have hfc : ContinuousOn f (Icc 0 t) :=
    fun s hs => (hf s hs.1).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.mono (fun _ hs => hs.1))
  have hCn : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, ht⟩)
  let K : ℝ≥0 := ⟨C, hCn⟩
  have hn : ∀ r ∈ Icc 0 t, f r ≠ 0 := by
    intro r hr hfr
    have hu : EqOn f (fun _ => (0 : ℝ)) (Icc 0 r) := by
      apply ODE_solution_unique_of_mem_Icc_left
        (v := fun s z => c s * z) (s := fun _ => univ) (K := K)
      · intro s hs
        apply LipschitzOnWith.of_dist_le_mul
        intro a _ b _
        calc
          dist (c s * a) (c s * b) = ‖c s‖ * dist a b := by
            simp [dist_eq_norm, ← mul_sub, norm_mul]
          _ ≤ (K : ℝ) * dist a b :=
            mul_le_mul_of_nonneg_right (hC s ⟨hs.1.le, hs.2.trans hr.2⟩)
              dist_nonneg
      · exact fun s hs => (hf s hs.1).continuousAt.continuousWithinAt
      · exact fun s hs => (hf s hs.1.le).hasDerivWithinAt
      · exact fun _ _ => mem_univ _
      · exact continuousOn_const
      · intro s _
        simpa using (hasDerivAt_const s (0 : ℝ)).hasDerivWithinAt
      · exact fun _ _ => mem_univ _
      · exact hfr
    have := hu ⟨le_rfl, hr.1⟩
    exact hf0.ne' this
  by_contra hpos
  obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc' ht hfc ⟨le_of_not_gt hpos, hf0.le⟩
  exact hn r hr hfr

/-- **Positivity.** Let `α, β, γ, δ > 0`, and let `x, y : ℝ → ℝ` have two-sided derivatives at every
`t ≥ 0` with `x' = α x - β x y` and `y' = δ x y - γ y` there. If `x 0 > 0` and `y 0 > 0`, then
`x t > 0` and `y t > 0` for every `t ≥ 0`. -/
public theorem pos_of_pos {α β γ δ : ℝ} (_hα : 0 < α) (_hβ : 0 < β)
    (_hγ : 0 < γ) (_hδ : 0 < δ) {x y : ℝ → ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (α * x t - β * x t * y t) t)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (δ * x t * y t - γ * y t) t)
    (hx0 : 0 < x 0) (hy0 : 0 < y 0) :
    ∀ t, 0 ≤ t → 0 < x t ∧ 0 < y t := by
  have hxc : ContinuousOn x (Ici 0) := fun t ht =>
    (hx t ht).continuousAt.continuousWithinAt
  have hyc : ContinuousOn y (Ici 0) := fun t ht =>
    (hy t ht).continuousAt.continuousWithinAt
  intro t ht
  constructor
  · apply scalar_pos (c := fun s => α - β * y s) _
      (continuousOn_const.sub (continuousOn_const.mul hyc)) hx0 ht
    intro s hs
    convert hx s hs using 1
    ring
  · apply scalar_pos (c := fun s => δ * x s - γ) _
      ((continuousOn_const.mul hxc).sub continuousOn_const) hy0 ht
    intro s hs
    convert hy s hs using 1
    ring

private theorem global_bounded_field {F : (ℝ × ℝ) → ℝ × ℝ} {K L : ℝ≥0}
    (hF : LipschitzWith K F) (hL : ∀ p, ‖F p‖ ≤ L) (p : ℝ × ℝ) :
    ∃ f : ℝ → ℝ × ℝ, f 0 = p ∧ ∀ t, HasDerivAt f (F (f t)) t := by
  have hlocal (n : ℕ) : ∃ f : ℝ → ℝ × ℝ, f 0 = p ∧
      ∀ t ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1), HasDerivAt f (F (f t)) t := by
    let t₀ : Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) := ⟨0, by
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      constructor <;> linarith⟩
    have hpl : IsPicardLindelof (fun _ => F) t₀ p (L * ((n : ℝ≥0) + 1)) 0 L K := by
      constructor
      · exact fun _ _ => hF.lipschitzOnWith
      · exact fun _ _ => continuousOn_const
      · exact fun _ _ q _ => hL q
      · simp [t₀]
    obtain ⟨f, hf0, hf⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    exact ⟨f, hf0, fun t ht => (hf t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)⟩
  choose g hg0 hg using hlocal
  have compat (n m : ℕ) (t : ℝ)
      (hn : t ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1))
      (hm : t ∈ Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1)) : g n t = g m t := by
    let r := min ((n : ℝ) + 1) ((m : ℝ) + 1)
    have hr : 0 < r := by dsimp [r]; positivity
    have hn' : Ioo (-r) r ⊆ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
      intro s hs
      have := min_le_left ((n : ℝ) + 1) ((m : ℝ) + 1)
      constructor <;> dsimp [r] at * <;> linarith [hs.1, hs.2]
    have hm' : Ioo (-r) r ⊆ Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1) := by
      intro s hs
      have := min_le_right ((n : ℝ) + 1) ((m : ℝ) + 1)
      constructor <;> dsimp [r] at * <;> linarith [hs.1, hs.2]
    have hu := ODE_solution_unique_of_mem_Ioo (v := fun _ => F)
      (s := fun _ => univ) (fun _ _ => hF.lipschitzOnWith)
      (show (0 : ℝ) ∈ Ioo (-r) r by constructor <;> linarith)
      (fun s hs => ⟨hg n s (hn' hs), mem_univ _⟩)
      (fun s hs => ⟨hg m s (hm' hs), mem_univ _⟩) ((hg0 n).trans (hg0 m).symm)
    apply hu
    change -min ((n : ℝ) + 1) ((m : ℝ) + 1) < t ∧
      t < min ((n : ℝ) + 1) ((m : ℝ) + 1)
    rw [neg_lt, lt_min_iff, lt_min_iff]
    exact ⟨⟨by linarith [hn.1], by linarith [hm.1]⟩, hn.2, hm.2⟩
  have hn (t : ℝ) : ∃ n : ℕ, t ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
    obtain ⟨n, hn⟩ := exists_nat_gt |t|
    refine ⟨n, ?_⟩
    have := (abs_lt.mp hn)
    constructor <;> linarith [this.1, this.2]
  choose idx hidx using hn
  let f := fun t => g (idx t) t
  refine ⟨f, hg0 (idx 0), ?_⟩
  intro t
  let n := idx t
  have hn := hidx t
  have he : f =ᶠ[𝓝 t] g n := by
    filter_upwards [Ioo_mem_nhds hn.1 hn.2] with s hs
    exact compat (idx s) n s (hidx s) hs
  have hd := (hg n t hn).congr_of_eventuallyEq he
  have heq : f t = g n t := compat (idx t) n t (hidx t) hn
  simpa only [heq] using hd

private def vectorField (α β γ δ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (α * p.1 - β * p.1 * p.2, δ * p.1 * p.2 - γ * p.2)

private theorem vectorField_contDiff (α β γ δ : ℝ) :
    ContDiff ℝ 1 (vectorField α β γ δ) := by
  unfold vectorField
  fun_prop

private theorem scalar_pos_univ {f c : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (c t * f t) t) (hc : Continuous c) (hf0 : 0 < f 0) :
    ∀ t, 0 < f t := by
  intro t
  by_cases ht : 0 ≤ t
  · exact scalar_pos (fun s _ => hf s) hc.continuousOn hf0 ht
  · have hrev : ∀ s, 0 ≤ s →
        HasDerivAt (fun r => f (-r)) ((-c (-s)) * f (-s)) s := by
      intro s _
      convert (hf (-s)).comp s (hasDerivAt_neg s) using 1
      · rfl
      · ring
    have h := scalar_pos hrev (hc.comp continuous_neg).neg.continuousOn
      (by simpa using hf0) (neg_nonneg.mpr (le_of_not_ge ht))
    simpa using h

private theorem conserved_scaled {α β γ δ : ℝ} {x y k : ℝ → ℝ}
    (hx : ∀ t, HasDerivAt x (k t * (α * x t - β * x t * y t)) t)
    (hy : ∀ t, HasDerivAt y (k t * (δ * x t * y t - γ * y t)) t)
    (hxp : ∀ t, 0 < x t) (hyp : ∀ t, 0 < y t) :
    ∀ t, firstIntegral α β γ δ (x t) (y t) = firstIntegral α β γ δ (x 0) (y 0) := by
  have hd (t : ℝ) : HasDerivAt (fun s => firstIntegral α β γ δ (x s) (y s)) 0 t := by
    have h := (((hx t).const_mul δ).sub (((hx t).log (hxp t).ne').const_mul γ)).add
      ((hy t).const_mul β) |>.sub (((hy t).log (hyp t).ne').const_mul α)
    convert h using 1
    · funext s
      simp only [firstIntegral, Pi.sub_apply, Pi.add_apply]
    · field_simp [(hxp t).ne', (hyp t).ne']
      ring
  exact fun t => is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) t 0

private theorem level_bounded {α β γ δ E : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ) :
    ∃ R > (0 : ℝ), ∀ x y : ℝ, 0 < x → 0 < y →
      firstIntegral α β γ δ x y = E → ‖(x, y)‖ ≤ R := by
  let m := firstIntegral α (β / 2) γ (δ / 2) (γ / (δ / 2)) (α / (β / 2))
  let R := max 0 (max (2 * (E - m) / δ) (2 * (E - m) / β)) + 1
  refine ⟨R, by dsimp [R]; positivity, ?_⟩
  intro x y hx hy hE
  have hm := firstIntegral_equilibrium_le hα (half_pos hβ) hγ (half_pos hδ) hx hy
  have hb : δ / 2 * x + β / 2 * y ≤ E - m := by
    dsimp [m, firstIntegral] at hm hE ⊢
    linarith
  have hxb : x ≤ 2 * (E - m) / δ := by
    apply (le_div_iff₀ hδ).mpr
    nlinarith [mul_pos hβ hy]
  have hyb : y ≤ 2 * (E - m) / β := by
    apply (le_div_iff₀ hβ).mpr
    nlinarith [mul_pos hδ hx]
  have hmax : max (2 * (E - m) / δ) (2 * (E - m) / β) ≤ R := by
    dsimp [R]
    linarith [le_max_right 0 (max (2 * (E - m) / δ) (2 * (E - m) / β))]
  have hxR : x ≤ R := hxb.trans ((le_max_left _ _).trans hmax)
  have hyR : y ≤ R := hyb.trans ((le_max_right _ _).trans hmax)
  simpa only [Prod.norm_def, Real.norm_eq_abs, abs_of_pos hx, abs_of_pos hy,
    max_le_iff] using And.intro hxR hyR

/-- **Global positive solution.** For `α, β, γ, δ > 0` and `x₀, y₀ > 0` there are `x, y : ℝ → ℝ`
with `x 0 = x₀` and `y 0 = y₀`, differentiable at every real `t` with `x' = α x - β x y` and
`y' = δ x y - γ y`, and with `x t > 0` and `y t > 0` for every real `t`, negative times included. -/
public theorem exists_global_solution {α β γ δ x₀ y₀ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ)
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀) :
    ∃ x y : ℝ → ℝ, x 0 = x₀ ∧ y 0 = y₀ ∧
      (∀ t, HasDerivAt x (α * x t - β * x t * y t) t ∧
        HasDerivAt y (δ * x t * y t - γ * y t) t) ∧
      (∀ t, 0 < x t ∧ 0 < y t) := by
  obtain ⟨R, hR, hbound⟩ := level_bounded (E := firstIntegral α β γ δ x₀ y₀)
    hα hβ hγ hδ
  let b : ContDiffBump (0 : ℝ × ℝ) :=
    { rIn := R, rOut := R + 1, rIn_pos := hR, rIn_lt_rOut := by linarith }
  let F := fun p : ℝ × ℝ => b p • vectorField α β γ δ p
  have hFs : HasCompactSupport F := b.hasCompactSupport.smul_right
  have hFc : ContDiff ℝ 1 F := b.contDiff.smul (vectorField_contDiff α β γ δ)
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hFs hFc (by norm_num)
  obtain ⟨L, hL⟩ := hFs.exists_bound_of_continuous hFc.continuous
  let L' : ℝ≥0 := ⟨max L 0, le_max_right L 0⟩
  obtain ⟨f, hf0, hf⟩ := global_bounded_field (L := L') hK
    (fun p => (hL p).trans (le_max_left L 0)) (x₀, y₀)
  let x := fun t => (f t).1
  let y := fun t => (f t).2
  let k := fun t => b (f t)
  have hx : ∀ t, HasDerivAt x (k t * (α * x t - β * x t * y t)) t :=
    fun t => (hf t).fst
  have hy : ∀ t, HasDerivAt y (k t * (δ * x t * y t - γ * y t)) t :=
    fun t => (hf t).snd
  have hxc : Continuous x := continuous_iff_continuousAt.mpr (fun t => (hx t).continuousAt)
  have hyc : Continuous y := continuous_iff_continuousAt.mpr (fun t => (hy t).continuousAt)
  have hkc : Continuous k := b.continuous.comp
    (show Continuous f from continuous_iff_continuousAt.mpr (fun t => (hf t).continuousAt))
  have hx0 : x 0 = x₀ := congrArg Prod.fst hf0
  have hy0 : y 0 = y₀ := congrArg Prod.snd hf0
  have hxp : ∀ t, 0 < x t := scalar_pos_univ (c := fun t => k t * (α - β * y t))
    (by intro t; convert hx t using 1; ring)
    (hkc.mul (continuous_const.sub (continuous_const.mul hyc))) (hx0.symm ▸ hx₀)
  have hyp : ∀ t, 0 < y t := scalar_pos_univ (c := fun t => k t * (δ * x t - γ))
    (by intro t; convert hy t using 1; ring)
    (hkc.mul ((continuous_const.mul hxc).sub continuous_const)) (hy0.symm ▸ hy₀)
  have hE := conserved_scaled hx hy hxp hyp
  have hk (t : ℝ) : k t = 1 := by
    apply b.one_of_mem_closedBall
    apply Metric.mem_closedBall.mpr
    rw [dist_zero_right]
    apply hbound (x t) (y t) (hxp t) (hyp t)
    simpa only [hx0, hy0] using hE t
  refine ⟨x, y, hx0, hy0, ?_, fun t => ⟨hxp t, hyp t⟩⟩
  intro t
  exact ⟨by simpa only [hk t, one_mul] using hx t,
    by simpa only [hk t, one_mul] using hy t⟩

/-- **Uniqueness.** Let `α, β, γ, δ > 0`, and let `(x, y)` and `(u, v)` have two-sided derivatives
at every `t ≥ 0` solving there `x' = α x - β x y` and `y' = δ x y - γ y` and the same equations for
`(u, v)`. If `x 0 > 0`, `y 0 > 0`, `u 0 = x 0` and `v 0 = y 0`, then `x t = u t` and `y t = v t` for
every `t ≥ 0`. -/
public theorem eq_of_initial {α β γ δ : ℝ} (_hα : 0 < α) (_hβ : 0 < β)
    (_hγ : 0 < γ) (_hδ : 0 < δ) {x y u v : ℝ → ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (α * x t - β * x t * y t) t)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (δ * x t * y t - γ * y t) t)
    (hu : ∀ t, 0 ≤ t → HasDerivAt u (α * u t - β * u t * v t) t)
    (hv : ∀ t, 0 ≤ t → HasDerivAt v (δ * u t * v t - γ * v t) t)
    (_hx0 : 0 < x 0) (_hy0 : 0 < y 0) (hxu : x 0 = u 0) (hyv : y 0 = v 0) :
    ∀ t, 0 ≤ t → x t = u t ∧ y t = v t := by
  let f := fun t => (x t, y t)
  let g := fun t => (u t, v t)
  have hf : ∀ t, 0 ≤ t → HasDerivAt f (vectorField α β γ δ (f t)) t :=
    fun t ht => (hx t ht).prodMk (hy t ht)
  have hg : ∀ t, 0 ≤ t → HasDerivAt g (vectorField α β γ δ (g t)) t :=
    fun t ht => (hu t ht).prodMk (hv t ht)
  intro t ht
  have hfc : ContinuousOn f (Icc 0 t) :=
    fun s hs => (hf s hs.1).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Icc 0 t) :=
    fun s hs => (hg s hs.1).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  let S := Metric.closedBall (0 : ℝ × ℝ) (max C D)
  have hfs : ∀ s ∈ Ico 0 t, f s ∈ S := by
    intro s hs
    exact Metric.mem_closedBall.mpr (by
      simpa only [dist_zero_right] using (hC s ⟨hs.1, hs.2.le⟩).trans (le_max_left C D))
  have hgs : ∀ s ∈ Ico 0 t, g s ∈ S := by
    intro s hs
    exact Metric.mem_closedBall.mpr (by
      simpa only [dist_zero_right] using (hD s ⟨hs.1, hs.2.le⟩).trans (le_max_right C D))
  obtain ⟨K, hK⟩ := (vectorField_contDiff α β γ δ).contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_closedBall (0 : ℝ × ℝ) (max C D)) (isCompact_closedBall _ _)
  have hfg := ODE_solution_unique_of_mem_Icc_right (v := fun _ => vectorField α β γ δ)
    (s := fun _ => S) (fun _ _ => hK) hfc
    (fun s hs => (hf s hs.1).hasDerivWithinAt) hfs hgc
    (fun s hs => (hg s hs.1).hasDerivWithinAt) hgs
    (show f 0 = g 0 by exact Prod.ext hxu hyv)
  exact Prod.mk.inj (hfg ⟨ht, le_rfl⟩)

private theorem component_strict_min {a b z : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hz : 0 < z) (hne : z ≠ b / a) :
    a * (b / a) - b * log (b / a) < a * z - b * log z := by
  have hq : 0 < a * z / b := by positivity
  have hq1 : a * z / b ≠ 1 := by
    intro h
    apply hne
    apply (eq_div_iff ha.ne').mpr
    have := (div_eq_iff hb.ne').mp h
    nlinarith
  have hlog := log_lt_sub_one_of_pos hq hq1
  rw [log_div (by positivity) hb.ne', log_mul ha.ne' hz.ne'] at hlog
  rw [log_div hb.ne' ha.ne', mul_div_cancel₀ _ ha.ne']
  have hm := mul_lt_mul_of_pos_left hlog hb
  rw [mul_sub b (a * z / b), mul_div_cancel₀ _ hb.ne'] at hm
  linarith

private theorem firstIntegral_strict_min {α β γ δ x y : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ)
    (hx : 0 < x) (hy : 0 < y) (hne : (x, y) ≠ (γ / δ, α / β)) :
    firstIntegral α β γ δ (γ / δ) (α / β) < firstIntegral α β γ δ x y := by
  by_cases hxe : x = γ / δ
  · have hye : y ≠ α / β := by intro hye; exact hne (Prod.ext hxe hye)
    have h := component_strict_min hβ hα hy hye
    subst x
    unfold firstIntegral
    linarith
  · have h := component_strict_min hδ hγ hx hxe
    have hymin := firstIntegral_equilibrium_le hα hβ hγ hδ
      (div_pos hγ hδ) hy
    unfold firstIntegral at *
    linarith

private theorem non_equilibrium_along {α β γ δ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ) {x y : ℝ → ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (α * x t - β * x t * y t) t)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (δ * x t * y t - γ * y t) t)
    (hx0 : 0 < x 0) (hy0 : 0 < y 0)
    (hne : (x 0, y 0) ≠ (γ / δ, α / β)) :
    ∀ t, 0 ≤ t → (x t, y t) ≠ (γ / δ, α / β) := by
  have hp := pos_of_pos hα hβ hγ hδ hx hy hx0 hy0
  have hmin := firstIntegral_strict_min hα hβ hγ hδ hx0 hy0 hne
  intro t ht heq
  have hE := firstIntegral_eq hx hy (fun s hs => (hp s hs).1)
    (fun s hs => (hp s hs).2) ht
  have hxe : x t = γ / δ := congrArg Prod.fst heq
  have hye : y t = α / β := congrArg Prod.snd heq
  rw [hxe, hye] at hE
  linarith

private theorem periodic_of_return {α β γ δ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ) {x y : ℝ → ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (α * x t - β * x t * y t) t)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (δ * x t * y t - γ * y t) t)
    (hx0 : 0 < x 0) (hy0 : 0 < y 0) {T : ℝ} (hT : 0 ≤ T)
    (hr : (x T, y T) = (x 0, y 0)) :
    ∀ t, 0 ≤ t → x (t + T) = x t ∧ y (t + T) = y t := by
  have hp := pos_of_pos hα hβ hγ hδ hx hy hx0 hy0
  apply eq_of_initial hα hβ hγ hδ
    (x := fun t => x (t + T)) (y := fun t => y (t + T)) (u := x) (v := y)
  · intro t ht
    convert (hx (t + T) (add_nonneg ht hT)).comp t ((hasDerivAt_id t).add_const T) using 1
    · rfl
    · simp
  · intro t ht
    convert (hy (t + T) (add_nonneg ht hT)).comp t ((hasDerivAt_id t).add_const T) using 1
    · rfl
    · simp
  · exact hx
  · exact hy
  · simpa using (hp T hT).1
  · simpa using (hp T hT).2
  · simpa using congrArg Prod.fst hr
  · simpa using congrArg Prod.snd hr

private theorem initial_velocity_ne_zero {α β γ δ : ℝ}
    (hβ : 0 < β) (hδ : 0 < δ) {x₀ y₀ : ℝ}
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀) (hne : (x₀, y₀) ≠ (γ / δ, α / β)) :
    (α * x₀ - β * x₀ * y₀, δ * x₀ * y₀ - γ * y₀) ≠ (0 : ℝ × ℝ) := by
  intro hzero
  have hx : α * x₀ - β * x₀ * y₀ = 0 := congrArg Prod.fst hzero
  have hy : δ * x₀ * y₀ - γ * y₀ = 0 := congrArg Prod.snd hzero
  have hxf : x₀ * (α - β * y₀) = 0 := by nlinarith [hx]
  have hyf : y₀ * (δ * x₀ - γ) = 0 := by nlinarith [hy]
  have hxe := (mul_eq_zero.mp hyf).resolve_left hy₀.ne'
  have hye := (mul_eq_zero.mp hxf).resolve_left hx₀.ne'
  apply hne
  apply Prod.ext
  · apply (eq_div_iff hδ.ne').mpr
    linarith
  · apply (eq_div_iff hβ.ne').mpr
    linarith

private theorem minimal_return_of_return {f : ℝ → ℝ × ℝ} {d : ℝ × ℝ}
    (hd : HasDerivAt f d 0) (hd0 : d ≠ 0) (hc : ContinuousOn f (Ici 0))
    (hreturn : ∃ S > (0 : ℝ), f S = f 0) :
    ∃ T > (0 : ℝ), f T = f 0 ∧ ∀ s, 0 < s → s < T → f s ≠ f 0 := by
  obtain ⟨ε, hε, hearly⟩ := Metric.mem_nhdsWithin_iff.mp
    (hd.eventually_ne (c := f 0) hd0)
  have hearly' : ∀ s, 0 < s → s < ε → f s ≠ f 0 := by
    intro s hs hsε
    apply hearly
    constructor
    · simpa [Real.dist_eq, abs_of_pos hs] using hsε
    · simpa using hs.ne'
  obtain ⟨S, hS, hret⟩ := hreturn
  have hεS : ε ≤ S := by
    by_contra h
    exact hearly' S hS (lt_of_not_ge h) hret
  let A := Icc ε S ∩ f ⁻¹' {f 0}
  have hAc : IsCompact A := isCompact_Icc.of_isClosed_subset
    ((hc.mono (fun s (hs : s ∈ Icc ε S) => hε.le.trans hs.1)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_singleton) inter_subset_left
  have hAn : A.Nonempty := ⟨S, ⟨⟨hεS, le_rfl⟩, hret⟩⟩
  obtain ⟨T, hTA, hmin⟩ := hAc.exists_isMinOn hAn continuousOn_id
  refine ⟨T, hε.trans_le hTA.1.1, hTA.2, ?_⟩
  intro s hs hsT hsr
  by_cases hsε : s < ε
  · exact hearly' s hs hsε hsr
  · have hsA : s ∈ A := ⟨⟨le_of_not_gt hsε, hsT.le.trans hTA.1.2⟩, hsr⟩
    exact (not_le_of_gt hsT) (hmin hsA)

private theorem level_lower_bound {α β γ δ E : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ) :
    ∃ l > (0 : ℝ), ∀ x y : ℝ, 0 < x → 0 < y →
      firstIntegral α β γ δ x y = E → l ≤ x ∧ l ≤ y := by
  let mx := δ * (γ / δ) - γ * log (γ / δ)
  let my := β * (α / β) - α * log (α / β)
  refine ⟨min (exp ((my - E) / γ)) (exp ((mx - E) / α)),
    lt_min (exp_pos _) (exp_pos _), ?_⟩
  intro x y hx hy hE
  have hx_min := firstIntegral_equilibrium_le hα hβ hγ hδ hx (div_pos hα hβ)
  have hy_min := firstIntegral_equilibrium_le hα hβ hγ hδ (div_pos hγ hδ) hy
  have hxl : (my - E) / γ ≤ log x := by
    apply (div_le_iff₀ hγ).mpr
    dsimp [firstIntegral, my] at *
    nlinarith [mul_pos hδ hx]
  have hyl : (mx - E) / α ≤ log y := by
    apply (div_le_iff₀ hα).mpr
    dsimp [firstIntegral, mx] at *
    nlinarith [mul_pos hβ hy]
  constructor
  · exact (min_le_left _ _).trans (by simpa only [exp_log hx] using exp_le_exp.mpr hxl)
  · exact (min_le_right _ _).trans (by simpa only [exp_log hy] using exp_le_exp.mpr hyl)


private theorem firstIntegral_segment_le {α β γ δ x₁ y₁ x₂ y₂ a b : ℝ}
    (hα : 0 < α) (hγ : 0 < γ) (hx₁ : 0 < x₁) (hy₁ : 0 < y₁)
    (hx₂ : 0 < x₂) (hy₂ : 0 < y₂) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    firstIntegral α β γ δ (a * x₁ + b * x₂) (a * y₁ + b * y₂) ≤
      a * firstIntegral α β γ δ x₁ y₁ + b * firstIntegral α β γ δ x₂ y₂ := by
  have hx := strictConcaveOn_log_Ioi.concaveOn.2 hx₁ hx₂ ha hb hab
  have hy := strictConcaveOn_log_Ioi.concaveOn.2 hy₁ hy₂ ha hb hab
  simp only [smul_eq_mul] at hx hy
  have hx' := mul_le_mul_of_nonneg_left hx hγ.le
  have hy' := mul_le_mul_of_nonneg_left hy hα.le
  unfold firstIntegral
  nlinarith only [hx', hy']

private theorem normalized_deriv {p q : ℝ → ℝ} {a b t : ℝ}
    (hp : HasDerivAt p (-a * q t) t) (hq : HasDerivAt q (b * p t) t)
    (hne : 0 < p t ^ 2 + q t ^ 2) :
    HasDerivAt (fun s => p s / sqrt (p s ^ 2 + q s ^ 2))
      (-((b * p t ^ 2 + a * q t ^ 2) / (p t ^ 2 + q t ^ 2)) *
        (q t / sqrt (p t ^ 2 + q t ^ 2))) t ∧
    HasDerivAt (fun s => q s / sqrt (p s ^ 2 + q s ^ 2))
      (((b * p t ^ 2 + a * q t ^ 2) / (p t ^ 2 + q t ^ 2)) *
        (p t / sqrt (p t ^ 2 + q t ^ 2))) t := by
  let r := sqrt (p t ^ 2 + q t ^ 2)
  have hr : 0 < r := sqrt_pos.mpr hne
  have hr2 : r ^ 2 = p t ^ 2 + q t ^ 2 := sq_sqrt hne.le
  have hd := ((hp.pow 2).add (hq.pow 2)).sqrt hne.ne'
  constructor
  · convert hp.div hd hr.ne' using 1
    norm_num only [Nat.reduceSub, Nat.cast_ofNat, pow_one, Pi.add_apply, Pi.pow_apply]
    change -((b * p t ^ 2 + a * q t ^ 2) / (p t ^ 2 + q t ^ 2)) *
      (q t / r) = (-a * q t * r - p t * ((2 * p t * (-a * q t) +
      2 * q t * (b * p t)) / (2 * r))) / r ^ 2
    rw [← hr2]
    field_simp [hr.ne']
    rw [hr2]
    ring
  · convert hq.div hd hr.ne' using 1
    norm_num only [Nat.reduceSub, Nat.cast_ofNat, pow_one, Pi.add_apply, Pi.pow_apply]
    change ((b * p t ^ 2 + a * q t ^ 2) / (p t ^ 2 + q t ^ 2)) *
      (p t / r) = (b * p t * r - q t * ((2 * p t * (-a * q t) +
      2 * q t * (b * p t)) / (2 * r))) / r ^ 2
    rw [← hr2]
    field_simp [hr.ne']
    rw [hr2]
    ring

private theorem constant_on_halfline {f : ℝ → ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivAt f 0 t) {t : ℝ} (ht : 0 ≤ t) : f t = f 0 := by
  exact constant_of_has_deriv_right_zero (b := t)
    (fun s hs => (hf s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hf s hs.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩

private theorem rotation_return {p q θ w : ℝ → ℝ}
    (hp : ∀ t, 0 ≤ t → HasDerivAt p (-w t * q t) t)
    (hq : ∀ t, 0 ≤ t → HasDerivAt q (w t * p t) t)
    (hθ : ∀ t, 0 ≤ t → HasDerivAt θ (w t) t)
    (hθ0 : θ 0 = 0) {T : ℝ} (hT : 0 ≤ T) (hθT : θ T = 2 * π) :
    p T = p 0 ∧ q T = q 0 := by
  have ha : ∀ t, 0 ≤ t → HasDerivAt
      (fun s => p s * cos (θ s) + q s * sin (θ s)) 0 t := by
    intro t ht
    convert ((hp t ht).mul (hθ t ht).cos).add ((hq t ht).mul (hθ t ht).sin) using 1
    ring
  have hb : ∀ t, 0 ≤ t → HasDerivAt
      (fun s => q s * cos (θ s) - p s * sin (θ s)) 0 t := by
    intro t ht
    convert ((hq t ht).mul (hθ t ht).cos).sub ((hp t ht).mul (hθ t ht).sin) using 1
    ring
  have haT := constant_on_halfline ha hT
  have hbT := constant_on_halfline hb hT
  simpa only [hθ0, hθT, cos_two_pi, sin_two_pi, cos_zero, sin_zero,
    mul_one, mul_zero, add_zero, sub_zero] using And.intro haT hbT

private theorem angle_exists {w : ℝ → ℝ} {c : ℝ}
    (hw : ContinuousOn w (Ici 0)) (hc : 0 < c)
    (hl : ∀ t, 0 ≤ t → c ≤ w t) :
    ∃ θ : ℝ → ℝ, θ 0 = 0 ∧ (∀ t, 0 ≤ t → HasDerivAt θ (w t) t) ∧
      ∃ T > (0 : ℝ), θ T = 2 * π := by
  let W := fun t : ℝ => w (max t 0)
  have hW : Continuous W := hw.comp_continuous (continuous_id.max continuous_const)
    (fun t => le_max_right t 0)
  let θ := fun t => ∫ s in (0 : ℝ)..t, W s
  have hd : ∀ t, HasDerivAt θ (W t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hW.intervalIntegrable 0 t)
      (hW.stronglyMeasurableAtFilter _ _) hW.continuousAt
  have hθ0 : θ 0 = 0 := by simp [θ]
  have hg := mul_sub_le_image_sub_of_le_deriv
    (fun t => (hd t).differentiableAt)
    (fun t => by rw [(hd t).deriv]; exact hl (max t 0) (le_max_right t 0))
    (x := 0) (y := 2 * π / c) (by positivity)
  have hB : 0 < 2 * π / c := by positivity
  have hθB : 2 * π ≤ θ (2 * π / c) := by
    rw [hθ0, sub_zero, sub_zero, mul_div_cancel₀ _ hc.ne'] at hg
    exact hg
  obtain ⟨T, hT, he⟩ := intermediate_value_Icc hB.le
    (fun t _ => (hd t).continuousAt.continuousWithinAt) ⟨by rw [hθ0]; positivity, hθB⟩
  refine ⟨θ, hθ0, fun t ht => ?_, T, ?_, he⟩
  · simpa only [W, max_eq_left ht] using hd t
  · have hne : T ≠ 0 := by intro h; rw [h, hθ0] at he; linarith [pi_pos]
    exact lt_of_le_of_ne hT.1 hne.symm

private theorem firstIntegral_radial_lt {α β γ δ x y r : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ)
    (hx : 0 < x) (hy : 0 < y) (hr : 0 < r) (hr1 : r < 1)
    (hmin : firstIntegral α β γ δ (γ / δ) (α / β) < firstIntegral α β γ δ x y) :
    firstIntegral α β γ δ ((1 - r) * (γ / δ) + r * x)
      ((1 - r) * (α / β) + r * y) < firstIntegral α β γ δ x y := by
  have hseg := firstIntegral_segment_le (β := β) (δ := δ) hα hγ (div_pos hγ hδ) (div_pos hα hβ)
    hx hy (sub_nonneg.mpr hr1.le) hr.le (show 1 - r + r = 1 by ring)
  have hlt := mul_lt_mul_of_pos_left hmin (sub_pos.mpr hr1)
  linarith

private theorem same_ray_energy_eq {α β γ δ x y u v r : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ)
    (hx : 0 < x) (hy : 0 < y) (hu : 0 < u) (hv : 0 < v) (hr : 0 < r)
    (hux : u = (1 - r) * (γ / δ) + r * x)
    (hvy : v = (1 - r) * (α / β) + r * y)
    (hE : firstIntegral α β γ δ u v = firstIntegral α β γ δ x y)
    (hmin : firstIntegral α β γ δ (γ / δ) (α / β) < firstIntegral α β γ δ x y) :
    (u, v) = (x, y) := by
  rcases lt_trichotomy r 1 with hlt | heq | hgt
  · have h := firstIntegral_radial_lt hα hβ hγ hδ hx hy hr hlt hmin
    rw [← hux, ← hvy, hE] at h
    exact (lt_irrefl _ h).elim
  · apply Prod.ext
    · simpa only [heq, sub_self, zero_mul, one_mul, zero_add] using hux
    · simpa only [heq, sub_self, zero_mul, one_mul, zero_add] using hvy
  · have hri : 0 < 1 / r := by positivity
    have hri1 : 1 / r < 1 := (div_lt_one hr).mpr hgt
    have hxback : (1 - 1 / r) * (γ / δ) + (1 / r) * u = x := by
      rw [hux]
      field_simp [hr.ne']
      ring
    have hyback : (1 - 1 / r) * (α / β) + (1 / r) * v = y := by
      rw [hvy]
      field_simp [hr.ne']
      ring
    have h := firstIntegral_radial_lt hα hβ hγ hδ hu hv hri hri1 (hE.symm ▸ hmin)
    rw [hxback, hyback, hE] at h
    exact (lt_irrefl _ h).elim

private theorem exists_ray_return {p q a b : ℝ → ℝ} {c : ℝ}
    (hp : ∀ t, 0 ≤ t → HasDerivAt p (-a t * q t) t)
    (hq : ∀ t, 0 ≤ t → HasDerivAt q (b t * p t) t)
    (ha : ContinuousOn a (Ici 0)) (hb : ContinuousOn b (Ici 0)) (hc : 0 < c)
    (hca : ∀ t, 0 ≤ t → c ≤ a t) (hcb : ∀ t, 0 ≤ t → c ≤ b t)
    (hne : ∀ t, 0 ≤ t → 0 < p t ^ 2 + q t ^ 2) :
    ∃ T > (0 : ℝ), ∃ r > (0 : ℝ), p T = r * p 0 ∧ q T = r * q 0 := by
  have hpc : ContinuousOn p (Ici 0) := fun t ht =>
    (hp t ht).continuousAt.continuousWithinAt
  have hqc : ContinuousOn q (Ici 0) := fun t ht =>
    (hq t ht).continuousAt.continuousWithinAt
  let w := fun t => (b t * p t ^ 2 + a t * q t ^ 2) / (p t ^ 2 + q t ^ 2)
  have hw : ContinuousOn w (Ici 0) :=
    ((hb.mul (hpc.pow 2)).add (ha.mul (hqc.pow 2))).div
      ((hpc.pow 2).add (hqc.pow 2)) (fun t ht => (hne t ht).ne')
  have hcw : ∀ t, 0 ≤ t → c ≤ w t := by
    intro t ht
    apply (le_div_iff₀ (hne t ht)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr (hca t ht)) (sq_nonneg (q t)),
      mul_nonneg (sub_nonneg.mpr (hcb t ht)) (sq_nonneg (p t))]
  obtain ⟨θ, hθ0, hθ, T, hT, he⟩ := angle_exists hw hc hcw
  have hn := fun t ht => normalized_deriv (hp t ht) (hq t ht) (hne t ht)
  have hu := rotation_return (fun t ht => (hn t ht).1) (fun t ht => (hn t ht).2)
    hθ hθ0 hT.le he
  let r := sqrt (p T ^ 2 + q T ^ 2) / sqrt (p 0 ^ 2 + q 0 ^ 2)
  have hR : 0 < sqrt (p T ^ 2 + q T ^ 2) := sqrt_pos.mpr (hne T hT.le)
  have hR0 : 0 < sqrt (p 0 ^ 2 + q 0 ^ 2) := sqrt_pos.mpr (hne 0 le_rfl)
  refine ⟨T, hT, r, div_pos hR hR0, ?_, ?_⟩
  · dsimp [r]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hR0.ne').mpr
    nlinarith only [(div_eq_div_iff hR.ne' hR0.ne').mp hu.1]
  · dsimp [r]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hR0.ne').mpr
    nlinarith only [(div_eq_div_iff hR.ne' hR0.ne').mp hu.2]

/-- **Minimal period.** Let `α, β, γ, δ > 0`, and let `x, y : ℝ → ℝ` have two-sided derivatives at
every `t ≥ 0` with `x' = α x - β x y` and `y' = δ x y - γ y` there, `x 0 > 0`, `y 0 > 0` and
`(x 0, y 0) ≠ (γ / δ, α / β)`, the coexistence equilibrium. Then there is `T > 0` with
`x (t + T) = x t` and `y (t + T) = y t` for every `t ≥ 0`, and `(x s, y s) ≠ (x 0, y 0)` for every
`s` with `0 < s < T`: `T` is the least positive time of return to the initial state, the minimal
period. -/
public theorem exists_minimal_period {α β γ δ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ) {x y : ℝ → ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (α * x t - β * x t * y t) t)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (δ * x t * y t - γ * y t) t)
    (hx0 : 0 < x 0) (hy0 : 0 < y 0)
    (hne : (x 0, y 0) ≠ (γ / δ, α / β)) :
    ∃ T : ℝ, 0 < T ∧
      (∀ t, 0 ≤ t → x (t + T) = x t ∧ y (t + T) = y t) ∧
      (∀ s, 0 < s → s < T → (x s, y s) ≠ (x 0, y 0)) := by
  have hp := pos_of_pos hα hβ hγ hδ hx hy hx0 hy0
  have hE (t : ℝ) (ht : 0 ≤ t) := firstIntegral_eq hx hy
    (fun s hs => (hp s hs).1) (fun s hs => (hp s hs).2) ht
  have hne_all := non_equilibrium_along hα hβ hγ hδ hx hy hx0 hy0 hne
  obtain ⟨R, hR, hbound⟩ := level_bounded (E := firstIntegral α β γ δ (x 0) (y 0))
    hα hβ hγ hδ
  have hbounded : ∀ t, 0 ≤ t → ‖(x t, y t)‖ ≤ R :=
    fun t ht => hbound (x t) (y t) (hp t ht).1 (hp t ht).2 (hE t ht)
  have hreturn : ∃ S > (0 : ℝ), (x S, y S) = (x 0, y 0) := by
    let p := fun t => δ * x t - γ
    let q := fun t => β * y t - α
    let a := fun t => δ * x t
    let b := fun t => β * y t
    have hd_p : ∀ t, 0 ≤ t → HasDerivAt p (-a t * q t) t := by
      intro t ht
      convert ((hx t ht).const_mul δ).sub_const γ using 1
      dsimp [a, q]
      ring
    have hd_q : ∀ t, 0 ≤ t → HasDerivAt q (b t * p t) t := by
      intro t ht
      convert ((hy t ht).const_mul β).sub_const α using 1
      dsimp [b, p]
      ring
    have hn : ∀ t, 0 ≤ t → 0 < p t ^ 2 + q t ^ 2 := by
      intro t ht
      by_contra hn
      have hp0 : p t = 0 := by nlinarith [sq_nonneg (q t)]
      have hq0 : q t = 0 := by nlinarith [sq_nonneg (p t)]
      apply hne_all t ht
      apply Prod.ext
      · apply (eq_div_iff hδ.ne').mpr
        dsimp [p] at hp0
        linarith
      · apply (eq_div_iff hβ.ne').mpr
        dsimp [q] at hq0
        linarith
    obtain ⟨l, hl, hlow⟩ := level_lower_bound
      (E := firstIntegral α β γ δ (x 0) (y 0)) hα hβ hγ hδ
    have hlow_t := fun t ht => hlow (x t) (y t) (hp t ht).1 (hp t ht).2 (hE t ht)
    have ha : ContinuousOn a (Ici 0) := fun t ht =>
      ((hx t ht).const_mul δ).continuousAt.continuousWithinAt
    have hb : ContinuousOn b (Ici 0) := fun t ht =>
      ((hy t ht).const_mul β).continuousAt.continuousWithinAt
    obtain ⟨T, hT, r, hr, hpr, hqr⟩ := exists_ray_return hd_p hd_q ha hb
      (lt_min (mul_pos hδ hl) (mul_pos hβ hl))
      (fun t ht => (min_le_left _ _).trans
        (mul_le_mul_of_nonneg_left (hlow_t t ht).1 hδ.le))
      (fun t ht => (min_le_right _ _).trans
        (mul_le_mul_of_nonneg_left (hlow_t t ht).2 hβ.le)) hn
    refine ⟨T, hT, same_ray_energy_eq hα hβ hγ hδ hx0 hy0
      (hp T hT.le).1 (hp T hT.le).2 hr ?_ ?_ (hE T hT.le)
      (firstIntegral_strict_min hα hβ hγ hδ hx0 hy0 hne)⟩
    · dsimp [p] at hpr
      field_simp
      nlinarith only [hpr]
    · dsimp [q] at hqr
      field_simp
      nlinarith only [hqr]
  obtain ⟨T, hT, hret, hmin⟩ := minimal_return_of_return
    ((hx 0 le_rfl).prodMk (hy 0 le_rfl))
    (initial_velocity_ne_zero hβ hδ hx0 hy0 hne)
    (fun t ht => ((hx t ht).prodMk (hy t ht)).continuousAt.continuousWithinAt) hreturn
  exact ⟨T, hT, periodic_of_return hα hβ hγ hδ hx hy hx0 hy0 hT.le hret, hmin⟩

end Domains.Biology.Dynamics.LotkaVolterra
