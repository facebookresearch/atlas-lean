/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.SelfConcordant
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The open unit Dikin ellipsoid -/

@[expose] public section

open Set Filter
open scoped ContDiff Topology
namespace MathlibExt.Analysis.Convex.SelfConcordant

private theorem exists_uniform_bound_of_self_concordant_second_deriv {w : ℝ → ℝ} {b : ℝ}
    (hb : 0 < b) (hb₁ : b ≤ 1) (h0 : w 0 < 1)
    (hw : ∀ t ∈ Ico 0 b, DifferentiableAt ℝ w t)
    (hw₀ : ∀ t ∈ Ico 0 b, 0 ≤ w t)
    (hderiv : ∀ t ∈ Ico 0 b, |deriv w t| ≤ 2 * w t ^ (3 / 2 : ℝ)) :
    ∃ C ≥ 0, ∀ t ∈ Ico 0 b, w t ≤ C := by
  let ε := (1 - w 0) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hpos (t : ℝ) (ht : t ∈ Ico 0 b) : 0 < w t + ε := add_pos_of_nonneg_of_pos (hw₀ t ht) hε
  let r (t : ℝ) := (w t + ε) ^ (-1 / 2 : ℝ)
  have hn (t : ℝ) (ht : t ∈ Ico 0 b) : HasDerivAt r
      (deriv w t * ((-1 / 2 : ℝ) * (w t + ε) ^ (-3 / 2 : ℝ))) t := by
    have h := ((hw t ht).hasDerivAt.add_const ε).rpow_const (p := -1 / 2)
      (Or.inl (hpos t ht).ne')
    rw [show (-1 / 2 : ℝ) - 1 = -3 / 2 by norm_num] at h
    simpa only [mul_assoc] using h
  have hnr (t : ℝ) (ht : t ∈ Ico 0 b) :
      ‖deriv w t * ((-1 / 2 : ℝ) * (w t + ε) ^ (-3 / 2 : ℝ))‖ ≤ 1 := by
    let a := (w t + ε) ^ (3 / 2 : ℝ)
    let z := (w t + ε) ^ (-3 / 2 : ℝ)
    have hz : 0 ≤ z := Real.rpow_nonneg (hpos t ht).le _
    have hpow : w t ^ (3 / 2 : ℝ) ≤ a :=
      Real.rpow_le_rpow (hw₀ t ht) (le_add_of_nonneg_right hε.le) (by norm_num)
    have hwz : |deriv w t| ≤ 2 * a :=
      (hderiv t ht).trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
    have habs : |(-1 / 2 : ℝ)| = 1 / 2 := by norm_num
    have haz : a * z = 1 := by
      dsimp only [a, z]
      rw [← Real.rpow_add (hpos t ht), show (3 / 2 : ℝ) + (-3 / 2) = 0 by ring,
        Real.rpow_zero]
    change ‖deriv w t * ((-1 / 2 : ℝ) * z)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_mul, abs_mul, habs, abs_of_nonneg hz]
    calc
      |deriv w t| * (1 / 2 * z) ≤ (2 * a) * (1 / 2 * z) :=
        mul_le_mul_of_nonneg_right hwz (mul_nonneg (by norm_num) hz)
      _ = a * z := by ring
      _ = 1 := haz
  have hr₀ : 1 < r 0 := by
    have hp := hpos 0 ⟨le_rfl, hb⟩
    have hs : w 0 + ε < 1 := by dsimp [ε]; linarith
    calc
      1 = (1 : ℝ) ^ (-1 / 2 : ℝ) := (Real.one_rpow _).symm
      _ < _ := Real.rpow_lt_rpow_of_neg hp hs (by norm_num)
  let δ := r 0 - 1
  have hδ : 0 < δ := sub_pos.mpr hr₀
  refine ⟨(δ ^ 2)⁻¹, by positivity, fun t ht => ?_⟩
  have hsub : Icc 0 t ⊆ Ico 0 b := fun _ hx => ⟨hx.1, hx.2.trans_lt ht.2⟩
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun u hu => (hn u (hsub hu)).hasDerivWithinAt)
    (fun u hu => hnr u (hsub (Ico_subset_Icc_self hu))) t ⟨ht.1, le_rfl⟩
  have hrt : δ ≤ r t := by
    rw [Real.norm_eq_abs, one_mul, sub_zero] at hmv
    have hlow := (abs_le.mp hmv).1
    dsimp [δ]
    linarith [ht.2.trans_le hb₁]
  have hp := hpos t ht
  have hsqrt : r t = (√(w t + ε))⁻¹ := by
    change (w t + ε) ^ (-1 / 2 : ℝ) = _
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hp.le, ← Real.sqrt_eq_rpow]
  have hinv : √(w t + ε) ≤ δ⁻¹ := by
    exact (le_inv_comm₀ (Real.sqrt_pos.2 hp) hδ).2 (hsqrt ▸ hrt)
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hinv 2
  rw [Real.sq_sqrt hp.le, inv_pow] at hsq
  linarith

private theorem exists_first_exit_on_unit_interval {U : Set ℝ} (hU : IsOpen U)
    (hc : Convex ℝ U) (h₀ : (0 : ℝ) ∈ U) (h₁ : (1 : ℝ) ∉ U) :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧ Ico 0 b ⊆ U ∧ b ∉ U := by
  let S := U ∩ Icc (0 : ℝ) 1
  have hs : S.Nonempty := ⟨0, h₀, le_rfl, zero_le_one⟩
  have hbound : BddAbove S := ⟨1, fun _ ht => ht.2.2⟩
  let b := sSup S
  have hb₁ : b ≤ 1 := csSup_le hs fun _ ht => ht.2.2
  have hb₀ : 0 < b := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU 0 h₀
    let r := min (ε / 2) (1 / 2)
    have hr : 0 < r := lt_min (by positivity) (by norm_num)
    have hrε : r < ε := (min_le_left _ _).trans_lt (by linarith)
    have hrU : r ∈ U := hball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr]
      exact hrε)
    exact hr.trans_le (le_csSup hbound ⟨hrU, hr.le, (min_le_right _ _).trans (by norm_num)⟩)
  refine ⟨b, hb₀, hb₁, ?_, ?_⟩
  · intro t ht
    obtain ⟨r, hr, htr⟩ := exists_lt_of_lt_csSup hs ht.2
    exact hc.ordConnected.out h₀ hr.1 ⟨ht.1, htr.le⟩
  · intro hbU
    have hb_lt : b < 1 := lt_of_le_of_ne hb₁ fun he => h₁ (he ▸ hbU)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU b hbU
    let r := b + min (ε / 2) ((1 - b) / 2)
    have hbr : b < r := lt_add_of_pos_right _ (lt_min (by positivity) (by linarith))
    have hr₁ : r ≤ 1 := by
      dsimp [r]
      linarith [min_le_right (ε / 2) ((1 - b) / 2)]
    have hrU : r ∈ U := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hbr)]
      dsimp [r]
      linarith [min_le_left (ε / 2) ((1 - b) / 2)])
    exact (not_le_of_gt hbr) (le_csSup hbound ⟨hrU, hb₀.le.trans hbr.le, hr₁⟩)

/-- **The open unit Dikin ellipsoid lies in the domain.** If `F` is self-concordant on `Q` and
`x ∈ Q`, then every `y` with `|y - x|_x < 1`, i.e. `D²F(x)[y - x, y - x] < 1`, lies in `Q`.
This is item I of Section 2.2 of A. Nemirovski, *Interior Point Polynomial Time Methods in Convex
Programming*, Spring Semester 1996 lecture notes, pp. 20–22 ("the open unit Dikin ellipsoid
`W₁(x)` is contained in `Q`"). -/
public theorem mem_of_dikin_lt_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {F : E → ℝ} {Q : Set E} (hF : IsSelfConcordant F Q) {x y : E}
    (hx : x ∈ Q) (hy : iteratedDeriv 2 (fun t : ℝ => F (x + t • (y - x))) 0 < 1) : y ∈ Q := by
  by_contra hyQ
  obtain ⟨_, hQ, hcQ, hFcd, hFcv, hbar, hsc⟩ := hF
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  have hline (t : ℝ) : line t = x + t • (y - x) := by
    rw [AffineMap.lineMap_apply]
    change t • (y - x) + x = x + t • (y - x)
    exact add_comm _ _
  have hlinecd : ContDiff ℝ 3 (line : ℝ → E) := by
    rw [show (line : ℝ → E) = fun t => x + t • (y - x) from funext hline]
    fun_prop
  let U := line ⁻¹' Q
  have hU : IsOpen U := hQ.preimage hlinecd.continuous
  have hU₀ : (0 : ℝ) ∈ U := by simpa [U, line] using hx
  have hU₁ : (1 : ℝ) ∉ U := by simpa [U, line] using hyQ
  obtain ⟨b, hb, hb₁, hseg, hbU⟩ :=
    exists_first_exit_on_unit_interval hU (hcQ.affine_preimage line) hU₀ hU₁
  let φ := F ∘ line
  have hφcd : ContDiffOn ℝ 3 φ U := hFcd.comp hlinecd.contDiffOn (fun _ ht => ht)
  have hφcv : ConvexOn ℝ U φ := hFcv.comp_affineMap line
  have hφ₁ : ContDiffOn ℝ 2 (deriv φ) U := hφcd.deriv_of_isOpen hU (by norm_num)
  let w := deriv (deriv φ)
  have hw₁ : ContDiffOn ℝ 1 w U := hφ₁.deriv_of_isOpen hU (by norm_num)
  have hdφ (t : ℝ) (ht : t ∈ U) : DifferentiableAt ℝ φ t :=
    ((hφcd t ht).contDiffAt (hU.mem_nhds ht)).differentiableAt (by norm_num)
  have hdφ₁ (t : ℝ) (ht : t ∈ U) : DifferentiableAt ℝ (deriv φ) t :=
    ((hφ₁ t ht).contDiffAt (hU.mem_nhds ht)).differentiableAt (by norm_num)
  have hdw (t : ℝ) (ht : t ∈ U) : DifferentiableAt ℝ w t :=
    ((hw₁ t ht).contDiffAt (hU.mem_nhds ht)).differentiableAt (by norm_num)
  have hw₀ (t : ℝ) (ht : t ∈ U) : 0 ≤ w t := by
    rw [show w t = deriv (deriv φ) t from rfl, ← derivWithin_of_isOpen hU ht]
    exact (hφcv.monotoneOn_deriv hdφ).derivWithin_nonneg
  have hd₂ : iteratedDeriv 2 φ = w := by rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hd₃ : iteratedDeriv 3 φ = deriv w := by rw [iteratedDeriv_succ, hd₂]
  have hwinit : w 0 < 1 := by
    rw [← hd₂]
    simpa only [φ, Function.comp_def, hline] using hy
  have hwd (t : ℝ) (ht : t ∈ U) : |deriv w t| ≤ 2 * w t ^ (3 / 2 : ℝ) := by
    have htranslate : (fun a : ℝ => F (line t + a • (y - x))) = fun a => φ (t + a) := by
      funext a
      change F (line t + a • (y - x)) = F (line (t + a))
      rw [hline t, hline (t + a), add_smul, add_assoc]
    have hh := hsc (line t) ht (y - x)
    rw [htranslate, iteratedDeriv_comp_const_add, iteratedDeriv_comp_const_add] at hh
    simpa only [add_zero, hd₂, hd₃] using hh
  obtain ⟨C, hC, hbound⟩ := exists_uniform_bound_of_self_concordant_second_deriv hb hb₁ hwinit
    (fun t ht => hdw t (hseg ht)) (fun t ht => hw₀ t (hseg ht)) (fun t ht => hwd t (hseg ht))
  have hfirst (t : ℝ) (ht : t ∈ Ico 0 b) : |deriv φ t| ≤ C + |deriv φ 0| := by
    have hsub : Icc 0 t ⊆ Ico 0 b := fun _ hu => ⟨hu.1, hu.2.trans_lt ht.2⟩
    have hh := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun u hu => (hdφ₁ u (hseg (hsub hu))).hasDerivAt.hasDerivWithinAt)
      (fun u hu => by
        have hu' := hsub (Ico_subset_Icc_self hu)
        change ‖w u‖ ≤ C
        rw [Real.norm_eq_abs, abs_of_nonneg (hw₀ u (hseg hu'))]
        exact hbound u hu')
      t ⟨ht.1, le_rfl⟩
    rw [Real.norm_eq_abs, sub_zero] at hh
    calc
      |deriv φ t| = |(deriv φ t - deriv φ 0) + deriv φ 0| := by rw [sub_add_cancel]
      _ ≤ |deriv φ t - deriv φ 0| + |deriv φ 0| := abs_add_le _ _
      _ ≤ C + |deriv φ 0| := add_le_add
        (hh.trans (mul_le_of_le_one_right hC (ht.2.trans_le hb₁).le)) le_rfl
  let M := C + |deriv φ 0|
  have hM : 0 ≤ M := add_nonneg hC (abs_nonneg _)
  have hφbound (t : ℝ) (ht : t ∈ Ico 0 b) : φ t ≤ φ 0 + M := by
    have hsub : Icc 0 t ⊆ Ico 0 b := fun _ hu => ⟨hu.1, hu.2.trans_lt ht.2⟩
    have hh := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun u hu => (hdφ u (hseg (hsub hu))).hasDerivAt.hasDerivWithinAt)
      (fun u hu => by
        rw [Real.norm_eq_abs]
        exact hfirst u (hsub (Ico_subset_Icc_self hu))) t ⟨ht.1, le_rfl⟩
    rw [Real.norm_eq_abs, sub_zero] at hh
    exact (sub_le_iff_le_add.mp ((le_abs_self _).trans
      (hh.trans (mul_le_of_le_one_right hM (ht.2.trans_le hb₁).le)))).trans_eq (add_comm _ _)
  have hnear : ∀ᶠ t in 𝓝[<] b, t ∈ Ico 0 b := Ico_mem_nhdsLT hb
  have hlineNear : ∀ᶠ t in 𝓝[<] b, line t ∈ Q := hnear.mono fun t ht => hseg ht
  have hlineLim : Tendsto line (𝓝[<] b) (𝓝 (line b)) :=
    hlinecd.continuous.continuousAt.continuousWithinAt
  have hbFront : line b ∈ frontier Q := by
    rw [hQ.frontier_eq]
    exact ⟨mem_closure_of_tendsto hlineLim hlineNear, hbU⟩
  have hφtop : Tendsto φ (𝓝[<] b) atTop :=
    (hbar (line b) hbFront).comp (tendsto_nhdsWithin_iff.mpr ⟨hlineLim, hlineNear⟩)
  have hbig := tendsto_atTop.mp hφtop (φ 0 + M + 1)
  obtain ⟨t, ht, hbig'⟩ := (hnear.and hbig).exists
  linarith [hφbound t ht]

end MathlibExt.Analysis.Convex.SelfConcordant
