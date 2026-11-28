/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Liouville
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import MathlibExt.NumberTheory.ArithmeticFunction.Liouville
import MathlibExt.NumberTheory.LSeries.Landau

/-!
# Constant sign of the summatory Liouville function forces zero-free regions of `ζ`

Let `L(x) = ∑_{n ≤ x} λ(n)` be the summatory function of the Liouville function. Pólya asked
whether `L(x) ≤ 0` for all `x ≥ 2`. Landau's theorem on Dirichlet series with nonnegative
coefficients shows that if `L` has eventually constant sign, then `ζ(s) ≠ 0` for `1 / 2 < re s`,
i.e. the Riemann hypothesis holds.

Along the way we show that `ζ` has no zeros on the real interval `(0, 1)`, using the expansion
`(s - 1) ζ(s) = 1 - ∑_{n ≥ 1} (n ^ (1-s) - (n+1) ^ (1-s) - (s - 1) n ^ (-s))`, valid for
`0 < re s`.

## Main statements

* `riemannZeta_ofReal_ne_zero_of_pos_of_lt_one`: `ζ(σ) ≠ 0` for real `0 < σ < 1`.
* `riemannZeta_ne_zero_of_liouville_sum_constant_sign`: if `∑_{n ≤ N} λ(n)` is eventually
  nonnegative or eventually nonpositive, then `ζ(s) ≠ 0` for `1 / 2 < re s`.
-/

@[expose] public section

open Filter Topology

namespace MetaMathlibExt.LiouvilleSummatory

/-- The second-order remainder `(n+1) ^ (-t) - (n+2) ^ (-t) - t (n+1) ^ (-t-1)` of the
difference of two consecutive powers. -/
private noncomputable def abelRem (n : ℕ) (t : ℂ) : ℂ :=
  ((n + 1 : ℕ) : ℂ) ^ (-t) - ((n + 2 : ℕ) : ℂ) ^ (-t) - t * ((n + 1 : ℕ) : ℂ) ^ (-t - 1)

private theorem hasDerivAt_ofReal_cpow (c : ℂ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => ((y : ℂ)) ^ c) (c * (y : ℂ) ^ (c - 1)) y :=
  (Complex.hasStrictDerivAt_cpow_const (Complex.ofReal_mem_slitPlane.2 hy)).hasDerivAt.comp_ofReal

private theorem norm_cpow_sub_cpow_sub_le {x : ℝ} (hx : 1 ≤ x) {t : ℂ} (ht : -2 ≤ t.re) :
    ‖(x : ℂ) ^ (-t) - ((x + 1 : ℝ) : ℂ) ^ (-t) - t * (x : ℂ) ^ (-t - 1)‖
      ≤ ‖t‖ * ‖t + 1‖ * x ^ (-t.re - 2) := by
  have hx0 : 0 < x := by linarith
  set M := ‖t‖ * ‖t + 1‖ * x ^ (-t.re - 2) with hM
  have h1 : ∀ y ∈ Set.Icc x (x + 1),
      ‖(-t) * (y : ℂ) ^ (-t - 1) - (-t) * (x : ℂ) ^ (-t - 1)‖ ≤ M * (y - x) := by
    refine norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun y : ℝ => (-t) * (y : ℂ) ^ (-t - 1))
      (f' := fun y => (-t) * ((-t - 1) * (y : ℂ) ^ (-t - 1 - 1))) ?_ ?_
    · intro y hy
      exact ((hasDerivAt_ofReal_cpow _ (by linarith [hy.1])).const_mul (-t)).hasDerivWithinAt
    · intro y hy
      have hy0 : 0 < y := by linarith [hy.1]
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0, norm_neg,
        show -t - 1 = -(t + 1) by ring, norm_neg, hM, mul_assoc]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        (norm_nonneg _)
      have : (-(t + 1) - 1).re = -t.re - 2 := by simp; ring
      rw [this]
      exact Real.rpow_le_rpow_of_nonpos hx0 hy.1 (by linarith)
  have h2 := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun y : ℝ => (y : ℂ) ^ (-t) - (y : ℂ) * ((-t) * (x : ℂ) ^ (-t - 1)))
    (f' := fun y => (-t) * (y : ℂ) ^ (-t - 1) - (-t) * (x : ℂ) ^ (-t - 1)) (C := M)
    (a := x) (b := x + 1) ?_ ?_ (x + 1) ⟨by linarith, le_rfl⟩
  · have heq : ((x + 1 : ℝ) : ℂ) ^ (-t) - ((x + 1 : ℝ) : ℂ) * ((-t) * (x : ℂ) ^ (-t - 1))
        - ((x : ℂ) ^ (-t) - (x : ℂ) * ((-t) * (x : ℂ) ^ (-t - 1)))
        = -((x : ℂ) ^ (-t) - ((x + 1 : ℝ) : ℂ) ^ (-t) - t * (x : ℂ) ^ (-t - 1)) := by
      push_cast; ring
    rw [heq, norm_neg] at h2
    simpa using h2
  · intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    have := (hasDerivAt_ofReal_cpow (-t) hy0).sub
      (((hasDerivAt_id y).ofReal_comp).mul_const ((-t) * (x : ℂ) ^ (-t - 1)))
    simp only [id, Complex.ofReal_one, one_mul] at this
    exact this.hasDerivWithinAt
  · intro y hy
    calc _ ≤ M * (y - x) := h1 y ⟨hy.1, hy.2.le⟩
      _ ≤ M * 1 := by
        refine mul_le_mul_of_nonneg_left (by linarith [hy.2]) ?_
        rw [hM]; positivity
      _ = M := mul_one M

private theorem norm_abelRem_le (n : ℕ) {t : ℂ} (ht : -2 ≤ t.re) :
    ‖abelRem n t‖ ≤ ‖t‖ * ‖t + 1‖ * ((n : ℝ) + 1) ^ (-t.re - 2) := by
  have h := norm_cpow_sub_cpow_sub_le (x := (n : ℝ) + 1)
    (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) ht
  have e1 : (((n : ℝ) + 1 : ℝ) : ℂ) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  have e2 : ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
  rw [e1, e2] at h
  exact h

private theorem differentiable_abelRem (n : ℕ) : Differentiable ℂ (abelRem n) := by
  have h1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h2 : ((n + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  intro t
  exact (((differentiableAt_id.neg).const_cpow (Or.inl h1)).sub
    ((differentiableAt_id.neg).const_cpow (Or.inl h2))).sub
    (differentiableAt_id.mul ((differentiableAt_id.neg.sub_const 1).const_cpow (Or.inl h1)))

private theorem summable_add_one_rpow {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-1 - δ)) := by
  have := (summable_nat_add_iff 1).mpr
    (Real.summable_nat_rpow.mpr (by linarith : -1 - δ < -1))
  simpa using this

/-- If `‖c n‖ ≤ K (n + 1) ^ θ`, then `∑ c n abelRem n t` converges and is holomorphic on
`θ - 1 < re t`. -/
private theorem summable_and_differentiableOn_tsum_mul_abelRem (c : ℕ → ℂ) {θ K : ℝ}
    (hθ : 0 ≤ θ) (hc : ∀ n, ‖c n‖ ≤ K * ((n : ℝ) + 1) ^ θ) :
    (∀ t : ℂ, θ - 1 < t.re → Summable (fun n => c n * abelRem n t)) ∧
      DifferentiableOn ℂ (fun t => ∑' n, c n * abelRem n t) {t | θ - 1 < t.re} := by
  have hK : 0 ≤ K := by simpa using (norm_nonneg _).trans (hc 0)
  have hbd : ∀ δ : ℝ, 0 < δ → ∀ R : ℝ, ∀ t : ℂ, θ - 1 + δ ≤ t.re → ‖t‖ ≤ R → ∀ n,
      ‖c n * abelRem n t‖ ≤ K * (R * (R + 1)) * ((n : ℝ) + 1) ^ (-1 - δ) := by
    intro δ hδ R t ht htR n
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hR : 0 ≤ R := (norm_nonneg t).trans htR
    rw [norm_mul]
    have hstep : ‖c n‖ * ‖abelRem n t‖ ≤ (K * ((n : ℝ) + 1) ^ θ) *
        (R * (R + 1) * ((n : ℝ) + 1) ^ (-(θ - 1 + δ) - 2)) := by
      refine mul_le_mul (hc n) ?_ (norm_nonneg _) (by positivity)
      refine (norm_abelRem_le n (by linarith)).trans ?_
      have ht1 : ‖t + 1‖ ≤ R + 1 := (norm_add_le _ _).trans (by simp [htR])
      exact mul_le_mul (mul_le_mul htR ht1 (norm_nonneg _) hR)
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) (by positivity)
        (by positivity)
    have hpow : ((n : ℝ) + 1) ^ θ * ((n : ℝ) + 1) ^ (-(θ - 1 + δ) - 2)
        = ((n : ℝ) + 1) ^ (-1 - δ) := by
      rw [← Real.rpow_add hn0]; ring_nf
    refine hstep.trans (le_of_eq ?_)
    rw [← hpow]; ring
  refine ⟨fun t ht => ?_, fun t0 ht0 => ?_⟩
  · refine Summable.of_norm_bounded
      ((summable_add_one_rpow (by linarith : (0:ℝ) < t.re - (θ - 1))).mul_left
        (K * (‖t‖ * (‖t‖ + 1)))) ?_
    intro n
    exact hbd _ (by linarith) ‖t‖ t (by linarith) le_rfl n
  · have ht0' : θ - 1 < t0.re := ht0
    have hδ : (0 : ℝ) < (t0.re - (θ - 1)) / 2 := by linarith
    set U : Set ℂ := {t : ℂ | θ - 1 + (t0.re - (θ - 1)) / 2 < t.re}
      ∩ Metric.ball 0 (‖t0‖ + 1) with hU
    have hUo : IsOpen U :=
      (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
    have ht0U : t0 ∈ U := by
      refine ⟨?_, ?_⟩
      · change _ < t0.re; linarith
      · rw [Metric.mem_ball, dist_zero_right]; linarith
    have hD := Complex.differentiableOn_tsum_of_summable_norm
      ((summable_add_one_rpow hδ).mul_left (K * ((‖t0‖ + 1) * ((‖t0‖ + 1) + 1))))
      (fun n => ((differentiable_const (c n)).mul (differentiable_abelRem n)).differentiableOn)
      hUo
      (fun n t ht => hbd _ hδ _ t ht.1.le (by
          have := ht.2; rw [Metric.mem_ball, dist_zero_right] at this; exact this.le) n)
    exact (hD.differentiableAt (hUo.mem_nhds ht0U)).differentiableWithinAt

private theorem norm_natCast_add_one_cpow (n : ℕ) (w : ℂ) :
    ‖((n + 1 : ℕ) : ℂ) ^ w‖ = ((n : ℝ) + 1) ^ w.re := by
  rw [Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n) w]
  push_cast; ring_nf

private theorem tendsto_natCast_add_one_cpow_neg {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℂ) ^ (-w)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop hw).comp
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  refine squeeze_zero_norm (fun N => le_of_eq ?_) h
  rw [norm_natCast_add_one_cpow]
  simp

private theorem summable_natCast_add_one_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ (-s)) := by
  refine Summable.of_norm_bounded (summable_add_one_rpow (δ := s.re - 1) (by linarith))
    (fun n => le_of_eq ?_)
  rw [norm_natCast_add_one_cpow]; congr 1; simp only [Complex.neg_re]; ring

private theorem summable_abelRem {t : ℂ} (ht : -1 < t.re) :
    Summable (fun n => abelRem n t) := by
  simpa using (summable_and_differentiableOn_tsum_mul_abelRem (fun _ => 1) le_rfl
    (K := 1) (fun n => by simp)).1 t (by linarith)

private theorem differentiableOn_tsum_abelRem :
    DifferentiableOn ℂ (fun t => ∑' n, abelRem n t) {t | -1 < t.re} := by
  simpa using (summable_and_differentiableOn_tsum_mul_abelRem (fun _ => 1) le_rfl
    (K := 1) (fun n => by simp)).2

private theorem tsum_abelRem_sub_one {s : ℂ} (hs : 1 < s.re) :
    ∑' n, abelRem n (s - 1) = 1 - (s - 1) * riemannZeta s := by
  have hsplit : ∀ n, ((n + 1 : ℕ) : ℂ) ^ (-(s - 1)) - ((n + 1 + 1 : ℕ) : ℂ) ^ (-(s - 1))
      = abelRem n (s - 1) + (s - 1) * ((n + 1 : ℕ) : ℂ) ^ (-s) := by
    intro n
    simp only [abelRem]
    rw [show -(s - 1) - 1 = -s by ring]
    ring
  have hG := summable_abelRem (t := s - 1) (by simp; linarith)
  have hT1 : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ (-(s - 1))
      - ((n + 1 + 1 : ℕ) : ℂ) ^ (-(s - 1))) 1 := by
    have hT : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ (-(s - 1))
        - ((n + 1 + 1 : ℕ) : ℂ) ^ (-(s - 1))) := by
      simp only [hsplit]
      exact hG.add ((summable_natCast_add_one_cpow_neg hs).mul_left _)
    rw [hT.hasSum_iff_tendsto_nat]
    have h1 : Tendsto (fun N : ℕ => (1 : ℂ) - ((N + 1 : ℕ) : ℂ) ^ (-(s - 1))) atTop
        (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_natCast_add_one_cpow_neg (by simp; linarith))
    rw [sub_zero] at h1
    refine h1.congr (fun N => ?_)
    rw [Finset.sum_range_sub' (fun i => ((i + 1 : ℕ) : ℂ) ^ (-(s - 1)))]
    simp
  have hz : riemannZeta s = ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) ^ (-s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    refine tsum_congr fun n => ?_
    rw [Complex.cpow_neg, one_div]; push_cast; ring
  have := hT1.tsum_eq
  simp only [hsplit] at this
  rw [hG.tsum_add ((summable_natCast_add_one_cpow_neg hs).mul_left _), tsum_mul_left,
    ← hz] at this
  linear_combination this

/-- The entire function equal to `(s - 1) ζ(s)` for `s ≠ 1` and to `1` at `s = 1`. -/
private noncomputable def zetaRes : ℂ → ℂ :=
  Function.update (fun s => (s - 1) * riemannZeta s) 1 1

private theorem zetaRes_of_ne_one {s : ℂ} (hs : s ≠ 1) : zetaRes s = (s - 1) * riemannZeta s := by
  rw [zetaRes, Function.update_of_ne hs]

private theorem differentiable_zetaRes : Differentiable ℂ zetaRes := by
  rw [← differentiableOn_univ, ← Complex.differentiableOn_compl_singleton_and_continuousAt_iff
    (c := 1) Filter.univ_mem]
  constructor
  · intro z hz
    have hz1 : z ≠ 1 := hz.2
    have heq : zetaRes =ᶠ[𝓝 z] fun s => (s - 1) * riemannZeta s := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz1] with w hw
      exact zetaRes_of_ne_one hw
    exact (((differentiableAt_id.sub_const 1).mul
      (differentiableAt_riemannZeta hz1)).congr_of_eventuallyEq heq).differentiableWithinAt
  · rw [zetaRes, continuousAt_update_same]
    exact riemannZeta_residue_one

private theorem zetaRes_eq_one_sub_tsum {s : ℂ} (hs : 0 < s.re) :
    zetaRes s = 1 - ∑' n, abelRem n (s - 1) := by
  have hUo : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUc : Convex ℝ {s : ℂ | 0 < s.re} := (convex_Ioi (0:ℝ)).linear_preimage Complex.reLm
  have hdiff : DifferentiableOn ℂ (fun s => 1 - ∑' n, abelRem n (s - 1)) {s | 0 < s.re} := by
    refine (differentiableOn_const 1).sub ?_
    refine differentiableOn_tsum_abelRem.comp (differentiableOn_id.sub_const 1) ?_
    intro z hz
    change -1 < (z - 1).re
    have : 0 < z.re := hz
    simp; linarith
  have hEq := ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
    differentiable_zetaRes).mono (Set.subset_univ _)).eqOn_of_preconnected_of_eventuallyEq
    (hdiff.analyticOnNhd hUo) hUc.isPreconnected (z₀ := 2)
    (by change (0:ℝ) < (2:ℂ).re; norm_num) (by
      have hmem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by change (1:ℝ) < (2:ℂ).re; norm_num
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem]
        with z hz
      have hz1 : z ≠ 1 := by rintro rfl; simp at hz
      rw [zetaRes_of_ne_one hz1, tsum_abelRem_sub_one hz]
      ring)
  exact hEq hs

/-- On the real line, `∑ abelRem n t` is real, at least `-t` for `t > 0` and at most `-t` for
`-1 < t ≤ 0`. -/
private theorem exists_tsum_abelRem_ofReal {t : ℝ} (ht : -1 < t) :
    ∃ g : ℝ, ∑' n, abelRem n (t : ℂ) = (g : ℂ) ∧ (0 < t → -t ≤ g) ∧ (t ≤ 0 → g ≤ -t) := by
  set rr : ℕ → ℝ := fun n : ℕ => ((n : ℝ) + 1) ^ (-t)
      - ((n : ℝ) + 1 + 1) ^ (-t) - t * ((n : ℝ) + 1) ^ (-t - 1) with hrr
  have hrc : ∀ n, abelRem n (t : ℂ) = ((rr n : ℝ) : ℂ) := by
    intro n
    have h1 : (0:ℝ) ≤ (n:ℝ) + 1 := by positivity
    have h2 : (0:ℝ) ≤ (n:ℝ) + 1 + 1 := by positivity
    simp only [abelRem, hrr]
    rw [Complex.ofReal_sub, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_cpow h1,
      Complex.ofReal_cpow h2, Complex.ofReal_cpow h1]
    push_cast
    ring_nf
  have hsumm : Summable rr := by
    rw [← Complex.summable_ofReal]
    exact (summable_abelRem (t := (t : ℂ)) (by simpa using ht)).congr hrc
  have htel : HasSum (fun n : ℕ => ((n : ℝ) + 1) ^ (-t - 1)
      - ((n : ℝ) + 1 + 1) ^ (-t - 1)) 1 := by
    have hnn : ∀ n : ℕ, 0 ≤ ((n : ℝ) + 1) ^ (-t - 1) - ((n : ℝ) + 1 + 1) ^ (-t - 1) := by
      intro n
      exact sub_nonneg.mpr
        (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith))
    rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
    have h0 := (tendsto_rpow_neg_atTop (by linarith : 0 < t + 1)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have h1 := (tendsto_const_nhds (x := (1:ℝ))).sub h0
    rw [sub_zero] at h1
    refine h1.congr (fun N => ?_)
    have hs := Finset.sum_range_sub' (fun i : ℕ => ((i : ℝ) + 1) ^ (-t - 1)) N
    push_cast at hs
    rw [hs]
    simp only [Function.comp, zero_add, Real.one_rpow]
    ring_nf
  have hQ : ∀ n : ℕ,
      (0 < t → 0 ≤ rr n + t * (((n:ℝ)+1) ^ (-t-1) - ((n:ℝ)+1+1) ^ (-t-1))) ∧
      (t ≤ 0 → rr n + t * (((n:ℝ)+1) ^ (-t-1) - ((n:ℝ)+1+1) ^ (-t-1)) ≤ 0) := by
    intro n
    set x : ℝ := (n : ℝ) + 1 with hx
    have hx1 : 1 ≤ x := by rw [hx]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hx10 : 0 < x + 1 := by linarith
    set q : ℝ := x / (x + 1) with hq
    have hq0 : 0 < q := by rw [hq]; positivity
    have hxq : x = q * (x + 1) := by rw [hq]; field_simp
    have hid : rr n + t * (x ^ (-t-1) - (x+1) ^ (-t-1))
        = (x + 1) ^ (-t) * (q ^ (-t) - 1 - t * (1 - q)) := by
      simp only [hrr]
      have e1 : x ^ (-t) = q ^ (-t) * (x + 1) ^ (-t) := by
        conv_lhs => rw [hxq]
        exact Real.mul_rpow hq0.le hx10.le
      have e2 : (x + 1) ^ (-t - 1) = (x + 1) ^ (-t) * (1 - q) := by
        rw [Real.rpow_sub_one hx10.ne', hq]; field_simp; ring
      rw [e1, e2]; ring
    rw [hid]
    have hpos : 0 < (x + 1) ^ (-t) := Real.rpow_pos_of_pos hx10 _
    constructor
    · intro htp
      refine mul_nonneg hpos.le ?_
      have hlog : Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos hq0
      have hexp : q ^ (-t) = Real.exp (Real.log q * (-t)) := Real.rpow_def_of_pos hq0 _
      have h1 := Real.add_one_le_exp (Real.log q * (-t))
      have h2 := mul_le_mul_of_nonneg_left hlog htp.le
      rw [← hexp] at h1
      linarith
    · intro htn
      refine mul_nonpos_of_nonneg_of_nonpos hpos.le ?_
      have := Real.geom_mean_le_arith_mean2_weighted (w₁ := -t) (w₂ := 1 + t) (p₁ := q)
        (p₂ := 1) (by linarith) (by linarith) hq0.le zero_le_one (by ring)
      rw [Real.one_rpow, mul_one] at this
      linarith
  refine ⟨∑' n, rr n, ?_, ?_, ?_⟩
  · rw [Complex.ofReal_tsum]; exact tsum_congr hrc
  · intro htp
    have h := Summable.tsum_le_tsum (fun n : ℕ => (by linarith [(hQ n).1 htp] :
        -t * (((n:ℝ)+1) ^ (-t-1) - ((n:ℝ)+1+1) ^ (-t-1)) ≤ rr n))
      (htel.summable.mul_left (-t)) hsumm
    rw [tsum_mul_left, htel.tsum_eq, mul_one] at h
    exact h
  · intro htn
    have h := Summable.tsum_le_tsum (fun n : ℕ => (by linarith [(hQ n).2 htn] :
        rr n ≤ -t * (((n:ℝ)+1) ^ (-t-1) - ((n:ℝ)+1+1) ^ (-t-1))))
      hsumm (htel.summable.mul_left (-t))
    rw [tsum_mul_left, htel.tsum_eq, mul_one] at h
    exact h

private theorem zetaRes_ofReal_ne_zero {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    zetaRes σ ≠ 0 := by
  obtain ⟨g, hg, -, hg2⟩ := exists_tsum_abelRem_ofReal (t := σ - 1) (by linarith)
  have : zetaRes σ = ((1 - g : ℝ) : ℂ) := by
    rw [zetaRes_eq_one_sub_tsum (by simpa using hσ0),
      show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, hg]
    push_cast; ring
  rw [this, Complex.ofReal_ne_zero]
  linarith [hg2 (by linarith)]

end MetaMathlibExt.LiouvilleSummatory

open MetaMathlibExt.LiouvilleSummatory

/-- The Riemann zeta function has no zeros on the real interval `(0, 1)`. -/
theorem riemannZeta_ofReal_ne_zero_of_pos_of_lt_one {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    riemannZeta σ ≠ 0 := by
  intro h
  apply zetaRes_ofReal_ne_zero hσ0 hσ1.le
  have hne : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ1.ne
  rw [zetaRes_of_ne_one hne, h, mul_zero]

open ArithmeticFunction in
/-- If the summatory function `∑_{n ≤ N} λ(n)` of the Liouville function is eventually
nonnegative or eventually nonpositive, then `ζ(s) ≠ 0` for `1 / 2 < re s`. -/
theorem riemannZeta_ne_zero_of_liouville_sum_constant_sign
    (hsign : (∀ᶠ N : ℕ in atTop, 0 ≤ ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.liouville n) ∨
      (∀ᶠ N : ℕ in atTop, ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.liouville n ≤ 0))
    {s : ℂ} (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
  -- ## The summatory function of `λ` and its eventual sign
  set S : ℕ → ℝ := fun n => ((∑ k ∈ Finset.Icc 1 n, liouville k : ℤ) : ℝ) with hS
  have hSstep : ∀ n : ℕ, S (n + 1) = S n + (liouville (n + 1) : ℝ) := by
    intro n; simp only [hS]; rw [Finset.sum_Icc_succ_top (by omega)]; push_cast; ring
  have hSbd : ∀ n : ℕ, |S n| ≤ n := by
    intro n
    induction n with
    | zero => simp [hS]
    | succ n ih =>
      rw [hSstep]; push_cast
      have : |(liouville (n + 1) : ℝ)| = 1 := by exact_mod_cast abs_liouville (by omega)
      calc |S n + (liouville (n + 1) : ℝ)|
          ≤ |S n| + |(liouville (n + 1) : ℝ)| := abs_add_le _ _
        _ ≤ (n : ℝ) + 1 := by linarith
  obtain ⟨ε, N0, hε, hpos⟩ : ∃ (ε : ℝ) (N0 : ℕ), (ε = 1 ∨ ε = -1) ∧
      ∀ n, N0 ≤ n → 0 ≤ ε * S n := by
    rcases hsign with h | h
    · obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp h
      refine ⟨1, N0, Or.inl rfl, fun n hn => ?_⟩
      simp only [hS, one_mul]
      exact_mod_cast hN0 n hn
    · obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp h
      refine ⟨-1, N0, Or.inr rfl, fun n hn => ?_⟩
      have : (((∑ k ∈ Finset.Icc 1 n, liouville k : ℤ)) : ℝ) ≤ 0 := by exact_mod_cast hN0 n hn
      simp only [hS]
      linarith
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  -- ## Partial summation: `L(λ, s) = s ∑ S(n) n ^ (-s-1) + ∑ S(n) abelRem(n, s)`
  obtain ⟨hGSsum, hGSdiff⟩ := summable_and_differentiableOn_tsum_mul_abelRem
    (fun n => (S (n + 1) : ℂ)) zero_le_one (K := 1) (fun n => by
      rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_one, one_mul]
      have := hSbd (n + 1); push_cast at this; exact this)
  have hAsum : ∀ s : ℂ, 1 < s.re →
      Summable (fun n : ℕ => (S (n + 1) : ℂ) * ((n + 1 : ℕ) : ℂ) ^ (-s - 1)) := by
    intro s hs
    refine Summable.of_norm_bounded (summable_add_one_rpow (δ := s.re - 1) (by linarith))
      (fun n => ?_)
    have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_natCast_add_one_cpow,
      show -1 - (s.re - 1) = 1 + (-s - 1).re by simp; ring, Real.rpow_add hn0, Real.rpow_one]
    have := hSbd (n + 1); push_cast at this
    exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hn0.le _)
  have hAbel : ∀ s : ℂ, 1 < s.re →
      LSeries (fun n => (liouville n : ℂ)) s
        = s * ∑' n : ℕ, (S (n + 1) : ℂ) * ((n + 1 : ℕ) : ℂ) ^ (-s - 1)
          + ∑' n : ℕ, (S (n + 1) : ℂ) * abelRem n s := by
    intro s hs
    have hsplit : ∀ n : ℕ,
        (S (n + 1) : ℂ) * (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s))
          = s * ((S (n + 1) : ℂ) * ((n + 1 : ℕ) : ℂ) ^ (-s - 1))
            + (S (n + 1) : ℂ) * abelRem n s := by
      intro n; simp only [abelRem]; ring
    have hRHS : HasSum (fun n : ℕ => (S (n + 1) : ℂ) *
        (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)))
        (s * ∑' n : ℕ, (S (n + 1) : ℂ) * ((n + 1 : ℕ) : ℂ) ^ (-s - 1)
          + ∑' n : ℕ, (S (n + 1) : ℂ) * abelRem n s) := by
      simp only [hsplit]
      exact ((hAsum s hs).hasSum.mul_left s).add (hGSsum s (by simp; linarith)).hasSum
    have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N,
        (liouville (n + 1) : ℂ) * ((n + 1 : ℕ) : ℂ) ^ (-s)
        = ∑ n ∈ Finset.range N, (S (n + 1) : ℂ) *
            (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s))
          + (S N : ℂ) * ((N + 1 : ℕ) : ℂ) ^ (-s) := by
      intro N
      induction N with
      | zero => simp [hS]
      | succ N ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hSstep N]
        have e : ((N + 1 + 1 : ℕ) : ℂ) = ((N + 2 : ℕ) : ℂ) := by push_cast; ring
        rw [e]; push_cast; ring
    have hL : HasSum (fun n : ℕ => (liouville (n + 1) : ℂ) * ((n + 1 : ℕ) : ℂ) ^ (-s))
        (LSeries (fun n => (liouville n : ℂ)) s) := by
      have h := (LSeriesSummable_liouville hs).hasSum
      rw [← hasSum_nat_add_iff' 1] at h
      simp only [Finset.range_one, Finset.sum_singleton, LSeries.term_zero, sub_zero] at h
      refine h.congr_fun (fun n => ?_)
      rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), Complex.cpow_neg, div_eq_mul_inv]
    have hbnd : Tendsto (fun N : ℕ => (S N : ℂ) * ((N + 1 : ℕ) : ℂ) ^ (-s)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun N : ℕ => ‖((N + 1 : ℕ) : ℂ) ^ (-(s - 1))‖) atTop (𝓝 0) := by
        simpa using (tendsto_natCast_add_one_cpow_neg (w := s - 1) (by simp; linarith)).norm
      refine squeeze_zero_norm (fun N => ?_) h0
      have hn0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_natCast_add_one_cpow,
        norm_natCast_add_one_cpow, show (-(s - 1)).re = 1 + (-s).re by simp; ring,
        Real.rpow_add hn0, Real.rpow_one]
      exact mul_le_mul_of_nonneg_right (by linarith [hSbd N]) (Real.rpow_nonneg hn0.le _)
    have h2 := hRHS.tendsto_sum_nat.add hbnd
    rw [add_zero] at h2
    simp only [← hpart] at h2
    exact tendsto_nhds_unique hL.tendsto_sum_nat h2
  -- ## Subtracting the finitely many terms of the wrong sign
  set b : ℕ → ℝ := fun n => if N0 ≤ n then ε * S n else 0 with hb
  have hb0 : ∀ n, 0 ≤ b n := by
    intro n; simp only [hb]; split_ifs with h
    · exact hpos n h
    · exact le_rfl
  have hbbd : ∀ n, |b n| ≤ n := by
    intro n; simp only [hb]; split_ifs
    · rw [abs_mul]; rcases hε with rfl | rfl <;> simp [hSbd n]
    · simp
  have hbsumm : ∀ w : ℂ, 2 < w.re → LSeriesSummable (fun n => (b n : ℂ)) w := by
    intro w hw
    refine LSeriesSummable_of_le_const_mul_rpow (x := 2) hw ⟨1, fun n hn => ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs]
    norm_num
    exact hbbd n
  set P : ℂ → ℂ := fun w => ∑ n ∈ Finset.range N0,
      ((S (n + 1) - ε * b (n + 1) : ℝ) : ℂ) * ((n + 1 : ℕ) : ℂ) ^ (-w) with hP
  have hPdiff : Differentiable ℂ P := by
    intro w
    refine DifferentiableAt.fun_sum fun n _ => ?_
    exact (differentiableAt_const _).mul ((differentiableAt_id.neg).const_cpow
      (Or.inl (by exact_mod_cast Nat.succ_ne_zero n)))
  have hdec : ∀ w : ℂ, 2 < w.re → ∑' n : ℕ, (S (n + 1) : ℂ) * ((n + 1 : ℕ) : ℂ) ^ (-w)
      = ε * LSeries (fun n => (b n : ℂ)) w + P w := by
    intro w hw
    have hbs : HasSum (fun n : ℕ => (b (n + 1) : ℂ) * ((n + 1 : ℕ) : ℂ) ^ (-w))
        (LSeries (fun n => (b n : ℂ)) w) := by
      have h := (hbsumm w hw).hasSum
      rw [← hasSum_nat_add_iff' 1] at h
      simp only [Finset.range_one, Finset.sum_singleton, LSeries.term_zero, sub_zero] at h
      refine h.congr_fun (fun n => ?_)
      rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), Complex.cpow_neg, div_eq_mul_inv]
    have hfin : HasSum (fun n : ℕ => ((S (n + 1) - ε * b (n + 1) : ℝ) : ℂ)
        * ((n + 1 : ℕ) : ℂ) ^ (-w)) (P w) := by
      refine hasSum_sum_of_ne_finset_zero (fun n hn => ?_)
      have hn' : N0 ≤ n + 1 := by simp at hn; omega
      have : S (n + 1) - ε * b (n + 1) = 0 := by
        simp only [hb]; rw [ite_eq_left hn', ← mul_assoc, hε2, one_mul, sub_self]
      rw [this]; simp
    have h := (hbs.mul_left (ε : ℂ)).add hfin
    rw [← h.tsum_eq]
    refine tsum_congr fun n => ?_
    push_cast; ring
  -- ## The identity `(s - 1) ζ(2s) = Z(s) H(s)` for `1 < re s`
  set H : ℂ → ℂ := fun s => s * (ε * LSeries (fun n => (b n : ℂ)) (s + 1)
      + P (s + 1)) + ∑' n : ℕ, (S (n + 1) : ℂ) * abelRem n s with hH
  have hstar1 : ∀ s : ℂ, 1 < s.re → (s - 1) * riemannZeta (2 * s) = zetaRes s * H s := by
    intro s hs
    have hs1 : s ≠ 1 := by rintro rfl; simp at hs
    rw [zetaRes_of_ne_one hs1, ← riemannZeta_mul_LSeries_liouville hs, hAbel s hs, hH]
    simp only
    rw [show -s - 1 = -(s + 1) by ring, hdec (s + 1) (by simp; linarith)]
    ring
  -- ## Continuing the identity to any half-plane where `L(b, s + 1)` converges
  have hstar : ∀ τ : ℝ, 1 / 2 ≤ τ → (∀ z : ℂ, τ < z.re →
      LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) < ((z + 1).re : EReal)) →
      ∀ z : ℂ, τ < z.re → (z - 1) * riemannZeta (2 * z) = zetaRes z * H z := by
    intro τ hτ hconvb
    have hUo : IsOpen {z : ℂ | τ < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hUc : Convex ℝ {z : ℂ | τ < z.re} := (convex_Ioi τ).linear_preimage Complex.reLm
    have hO1 : IsOpen {t : ℂ | 1 - 1 < t.re} := isOpen_lt continuous_const Complex.continuous_re
    have hLdiff : DifferentiableOn ℂ (fun z => (z - 1) * riemannZeta (2 * z))
        {z | τ < z.re} := by
      intro z hz
      have hz' : τ < z.re := hz
      have h2 : 2 * z ≠ 1 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      exact ((differentiableAt_id.sub_const 1).mul ((differentiableAt_riemannZeta h2).comp z
        (differentiableAt_id.const_mul 2))).differentiableWithinAt
    have hRdiff : DifferentiableOn ℂ (fun z => zetaRes z * H z) {z | τ < z.re} := by
      intro z hz
      have hz' : τ < z.re := hz
      have hz1 : z ∈ {t : ℂ | 1 - 1 < t.re} := by change 1 - 1 < z.re; linarith
      have hGat := (hGSdiff z hz1).differentiableAt (hO1.mem_nhds hz1)
      have hLb := ((LSeries_analyticOnNhd (fun n => (b n : ℂ))) (z + 1)
        (hconvb z hz')).differentiableAt.comp z (differentiableAt_id.add_const 1)
      have hPat := (hPdiff (z + 1)).comp z (differentiableAt_id.add_const 1)
      exact ((differentiable_zetaRes z).mul ((differentiableAt_id.mul
        (((differentiableAt_const _).mul hLb).add hPat)).add hGat)).differentiableWithinAt
    have hτ1 : ((τ + 1 : ℝ) : ℂ) ∈ {z : ℂ | τ < z.re} := by
      change τ < ((τ + 1 : ℝ) : ℂ).re; simp
    have hEq := (hLdiff.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
      (hRdiff.analyticOnNhd hUo) hUc.isPreconnected hτ1 (by
        have hmem : ((τ + 1 : ℝ) : ℂ) ∈ {z : ℂ | 1 < z.re} := by
          change 1 < ((τ + 1 : ℝ) : ℂ).re; simp; linarith
        filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem]
          with z hz
        exact hstar1 z hz)
    intro z hz
    exact hEq hz
  -- ## Conclusion
  intro hzero
  have hs1 : s ≠ 1 := by rintro rfl; exact riemannZeta_one_ne_zero hzero
  have hz2 : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  have hcontra : ∀ τ : ℝ, 1 / 2 ≤ τ → τ < s.re → (∀ z : ℂ, τ < z.re →
      LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) < ((z + 1).re : EReal)) → False := by
    intro τ hτ hτs hconvb
    have h := hstar τ hτ hconvb s hτs
    rw [zetaRes_of_ne_one hs1, hzero, mul_zero, zero_mul] at h
    exact mul_ne_zero (sub_ne_zero.mpr hs1) hz2 h
  set A := LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) with hA
  by_cases hA32 : A ≤ ((3 / 2 : ℝ) : EReal)
  · refine hcontra (1 / 2) le_rfl hs (fun z hz => ?_)
    refine lt_of_le_of_lt hA32 ?_
    have : (3 / 2 : ℝ) < (z + 1).re := by simp; linarith
    exact_mod_cast this
  · rw [not_le] at hA32
    have hA2 : A ≤ ((2 : ℝ) : EReal) := by
      refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
      exact hbsumm y (by simpa using hy)
    have hAtop : A ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top 2) hA2
    have hAbot : A ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hA32.le
    obtain ⟨σA, hσA⟩ : ∃ σA : ℝ, A = (σA : EReal) :=
      ⟨A.toReal, (EReal.coe_toReal hAtop hAbot).symm⟩
    have hσA32 : 3 / 2 < σA := by rw [hσA] at hA32; exact_mod_cast hA32
    set σ0 : ℝ := σA - 1 with hσ0
    have hσA2 : σA ≤ 2 := by rw [hσA] at hA2; exact_mod_cast hA2
    have hZσ0 : zetaRes σ0 ≠ 0 := zetaRes_ofReal_ne_zero (by linarith) (by linarith)
    have hO1 : IsOpen {t : ℂ | 1 - 1 < t.re} := isOpen_lt continuous_const Complex.continuous_re
    obtain ⟨r1, hr1, hr1Z⟩ := Metric.eventually_nhds_iff.mp
      ((differentiable_zetaRes _).continuousAt.eventually_ne hZσ0)
    set ρ : ℝ := min r1 (σ0 - 1 / 2) with hρ
    have hρ0 : 0 < ρ := lt_min hr1 (by linarith)
    have hρ1 : ρ ≤ r1 := min_le_left _ _
    have hρ2 : ρ ≤ σ0 - 1 / 2 := min_le_right _ _
    have hshift : ∀ w ∈ Metric.ball (σA : ℂ) ρ, zetaRes (w - 1) ≠ 0 ∧ 1 / 2 < (w - 1).re := by
      intro w hw
      have hd : dist (w - 1) (σ0 : ℂ) = dist w (σA : ℂ) := by
        rw [Complex.dist_eq, Complex.dist_eq, hσ0]; push_cast; ring_nf
      rw [Metric.mem_ball] at hw
      refine ⟨hr1Z (by rw [hd]; linarith), ?_⟩
      have h1 := Complex.abs_re_le_norm ((w - 1) - (σ0 : ℂ))
      rw [← Complex.dist_eq, hd] at h1
      have h2 : ((w - 1) - (σ0 : ℂ)).re = (w - 1).re - σ0 := by simp
      rw [h2] at h1
      linarith [(abs_le.mp h1).1]
    set g : ℂ → ℂ := fun w => (ε : ℂ) * (((w - 1 - 1) *
        riemannZeta (2 * (w - 1)) / zetaRes (w - 1) - ∑' n : ℕ, (S (n + 1) : ℂ) * abelRem n (w - 1))
        / (w - 1) - P w) with hg
    have hgdiff : DifferentiableOn ℂ g (Metric.ball (σA : ℂ) ρ) := by
      intro w hw
      obtain ⟨hZne, hre⟩ := hshift w hw
      have hne0 : w - 1 ≠ 0 := by intro h; rw [h] at hre; simp at hre; linarith
      have h2 : 2 * (w - 1) ≠ 1 := by
        intro h; have := congrArg Complex.re h; simp at this; simp at hre; linarith
      have hm1 : (w - 1) ∈ {t : ℂ | 1 - 1 < t.re} := by change 1 - 1 < (w - 1).re; linarith
      have hZat := (differentiable_zetaRes (w - 1)).comp w (differentiableAt_id.sub_const 1)
      have hGat := ((hGSdiff _ hm1).differentiableAt (hO1.mem_nhds hm1)).comp w
        (differentiableAt_id.sub_const 1)
      have hζat := (differentiableAt_riemannZeta h2).comp w
        ((differentiableAt_id.sub_const (1 : ℂ)).const_mul (2 : ℂ))
      exact ((differentiableAt_const (ε : ℂ)).mul
        (((((((differentiableAt_id.sub_const 1).sub_const 1).mul hζat).div hZat hZne).sub
          hGat).div (differentiableAt_id.sub_const 1) hne0).sub (hPdiff w))).differentiableWithinAt
    have hgeq : Set.EqOn g (LSeries fun n : ℕ => (b n : ℂ))
        (Metric.ball (σA : ℂ) ρ ∩ {z : ℂ | σA < z.re}) := by
      rintro w ⟨hw, hwre⟩
      have hwre' : σA < w.re := hwre
      obtain ⟨hZne, hre⟩ := hshift w hw
      have hne0 : w - 1 ≠ 0 := by intro h; rw [h] at hre; simp at hre; linarith
      have hconv : ∀ z : ℂ, σ0 < z.re →
          LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) < ((z + 1).re : EReal) := by
        intro z hz
        rw [← hA, hσA]
        have : σA < (z + 1).re := by simp; linarith
        exact_mod_cast this
      have h := hstar σ0 (by linarith) hconv (w - 1) (by simp; linarith)
      have hHval : H (w - 1) = (w - 1 - 1) * riemannZeta (2 * (w - 1)) / zetaRes (w - 1) := by
        rw [h]; field_simp
      simp only [hH] at hHval
      rw [show w - 1 + 1 = w by ring] at hHval
      have hε2' : (ε : ℂ) * ε = 1 := by exact_mod_cast hε2
      simp only [hg]
      rw [← hHval, add_sub_cancel_right, mul_div_cancel_left₀ _ hne0, add_sub_cancel_right,
        ← mul_assoc, hε2', one_mul]
    exact LSeries.not_exists_holomorphic_extension_of_nonneg b hb0 (by rw [← hA, hσA])
      ⟨ρ, g, hρ0, hgdiff, hgeq⟩
