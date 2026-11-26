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
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Semiboundedness of a self-concordant barrier

If `F` is a `ϑ`-self-concordant barrier for `closure Q` (with interior `Q`), then
`DF(x)[y - x] ≤ ϑ` for every `x ∈ Q` and every `y ∈ closure Q`.

This is (3.6), item I of Section 3.2 of A. Nemirovski, *Interior Point Polynomial Time Methods
in Convex Programming*, lecture notes (2004).
-/

@[expose] public section

open Set Filter
open scoped ContDiff Topology
open MathlibExt.Analysis.Convex.SelfConcordant

namespace WantedExt.Analysis.Convex.SelfConcordantWanted

/-- **Semiboundedness of a self-concordant barrier.** If `F` is a `ϑ`-self-concordant barrier for
`closure Q` (with interior `Q`), then `DF(x)[y - x] ≤ ϑ` for every `x ∈ Q` and every
`y ∈ closure Q`. This is (3.6), item I of Section 3.2 of A. Nemirovski, *Interior Point
Polynomial Time Methods in Convex Programming*, lecture notes (2004); it bounds the duality-type
gap along the central path of path-following methods. -/
theorem deriv_le_of_isSelfConcordantBarrier {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {F : E → ℝ} {Q : Set E} {ϑ : ℝ}
    (hF : IsSelfConcordantBarrier F Q ϑ) {x y : E} (hx : x ∈ Q) (hy : y ∈ closure Q) :
    deriv (fun t : ℝ => F (x + t • (y - x))) 0 ≤ ϑ := by
  obtain ⟨hϑ, hsc, hbar⟩ := hF
  obtain ⟨_, hQ, hcQ, hFcd, hFcv, _, _⟩ := hsc
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  have hline : ∀ t : ℝ, line t = x + t • (y - x) := by
    intro t
    rw [AffineMap.lineMap_apply]
    change t • (y - x) + x = x + t • (y - x)
    exact add_comm _ _
  have hlinecd : ContDiff ℝ 3 (line : ℝ → E) := by
    rw [show (line : ℝ → E) = fun t => x + t • (y - x) from funext hline]
    fun_prop
  let U := line ⁻¹' Q
  have hU : IsOpen U := hQ.preimage hlinecd.continuous
  have hU0 : (0:ℝ) ∈ U := by simpa [U, line, AffineMap.lineMap_apply_zero] using hx
  have hseg : ∀ t ∈ Ico (0:ℝ) 1, line t ∈ Q := by
    intro t ht
    by_cases h0 : t = 0
    · subst h0; simpa [line, AffineMap.lineMap_apply_zero] using hx
    · have hIoo : t ∈ Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), ht.2⟩
      have hmem : line t ∈ openSegment ℝ x y := lineMap_mem_openSegment ℝ x y hIoo
      have hsub : openSegment ℝ x y ⊆ interior Q :=
        hcQ.openSegment_interior_closure_subset_interior (by rwa [hQ.interior_eq]) hy
      have h := hsub hmem
      rw [hQ.interior_eq] at h
      exact h
  have hsegU : Ico (0:ℝ) 1 ⊆ U := fun t ht => hseg t ht
  let φ := F ∘ line
  have hφcd : ContDiffOn ℝ 3 φ U := hFcd.comp hlinecd.contDiffOn (fun _ ht => ht)
  have hφcv : ConvexOn ℝ U φ := hFcv.comp_affineMap line
  have hφ₁ : ContDiffOn ℝ 2 (deriv φ) U := hφcd.deriv_of_isOpen hU (by norm_num)
  have hdφ : ∀ t ∈ U, DifferentiableAt ℝ φ t :=
    fun t ht => ((hφcd t ht).contDiffAt (hU.mem_nhds ht)).differentiableAt (by norm_num)
  have hdφ₁ : ∀ t ∈ U, DifferentiableAt ℝ (deriv φ) t :=
    fun t ht => ((hφ₁ t ht).contDiffAt (hU.mem_nhds ht)).differentiableAt (by norm_num)
  have hmono : MonotoneOn (deriv φ) U := hφcv.monotoneOn_deriv hdφ
  have hnonneg : ∀ t ∈ U, 0 ≤ deriv (deriv φ) t := by
    intro t ht
    rw [← derivWithin_of_isOpen hU ht]
    exact (hmono.derivWithin_nonneg)
  have htrans : ∀ t : ℝ, (fun a : ℝ => F (line t + a • (y - x))) = fun a => φ (t + a) := by
    intro t
    funext a
    change F (line t + a • (y - x)) = F (line (t + a))
    rw [hline t, hline (t + a), add_smul, add_assoc]
  have hbar_t : ∀ t ∈ Ico (0:ℝ) 1,
      |deriv φ t| ≤ √ϑ * √(deriv (deriv φ) t) := by
    intro t ht
    have hlt := hseg t ht
    have hh := hbar (line t) hlt (y - x)
    rw [htrans t, deriv_comp_const_add, iteratedDeriv_comp_const_add] at hh
    simpa only [add_zero, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_zero] using hh
  have hgoal : (fun t : ℝ => F (x + t • (y - x))) = φ := by
    funext t; simp [φ, hline t]
  rw [hgoal]
  by_cases hle : deriv φ 0 ≤ 0
  · exact hle.trans hϑ
  · have hle_pos : 0 < deriv φ 0 := not_le.mp hle
    have hϑpos : 0 < ϑ := by
      by_contra hcon
      have hle0' : ϑ ≤ 0 := le_of_not_gt hcon
      have hϑ0 : ϑ = 0 := le_antisymm hle0' hϑ
      subst hϑ0
      have h0 := hbar_t 0 ⟨le_rfl, zero_lt_one⟩
      rw [Real.sqrt_zero, zero_mul] at h0
      have hle0 : deriv φ 0 ≤ 0 := (le_abs_self _).trans h0
      linarith
    have hpos : ∀ t ∈ Ico (0:ℝ) 1, 0 < deriv φ t := by
      intro t ht
      have hmono' := hmono hU0 (hsegU ht) ht.1
      linarith
    have hne : ∀ t ∈ Ico (0:ℝ) 1, deriv φ t ≠ 0 := fun t ht => (hpos t ht).ne'
    have hsq : ∀ t ∈ Ico (0:ℝ) 1, (deriv φ t) ^ 2 ≤ ϑ * deriv (deriv φ) t := by
      intro t ht
      have h1 := hbar_t t ht
      have hw := hnonneg t (hsegU ht)
      have h2 : (deriv φ t) ^ 2 ≤ (√ϑ * √(deriv (deriv φ) t)) ^ 2 := by
        have hab := abs_le.mp h1
        exact sq_le_sq' hab.1 hab.2
      have h3 : (√ϑ * √(deriv (deriv φ) t)) ^ 2 = ϑ * deriv (deriv φ) t := by
        rw [mul_pow, Real.sq_sqrt hϑ, Real.sq_sqrt hw]
      linarith
    have hpsi_deriv : ∀ t ∈ Ico (0:ℝ) 1,
        deriv (deriv φ)⁻¹ t = -(deriv (deriv φ) t) / (deriv φ t) ^ 2 := by
      intro t ht
      have h := ((hdφ₁ t (hsegU ht)).hasDerivAt.inv (hne t ht)).deriv
      simpa using h
    have hpsi_le : ∀ t ∈ Ico (0:ℝ) 1, deriv (deriv φ)⁻¹ t ≤ -1 / ϑ := by
      intro t ht
      rw [hpsi_deriv t ht]
      have hpow : 0 < (deriv φ t) ^ 2 := pow_pos (hpos t ht) 2
      have hdiv : 1 / ϑ ≤ deriv (deriv φ) t / (deriv φ t) ^ 2 := by
        rw [div_le_div_iff₀ hϑpos hpow]
        have h := hsq t ht
        linarith
      have hneg : -(deriv (deriv φ) t / (deriv φ t) ^ 2) ≤ -(1 / ϑ) := neg_le_neg hdiv
      simpa [neg_div] using hneg
    have hmvt : ∀ s ∈ Ico (0:ℝ) 1, s / ϑ < ((deriv φ)⁻¹) 0 := by
      intro s hs
      have hIcc_sub : Icc 0 s ⊆ Ico (0:ℝ) 1 := by
        intro u hu
        exact ⟨hu.1, hu.2.trans_lt hs.2⟩
      have hIccU : Icc 0 s ⊆ U := hIcc_sub.trans hsegU
      have hcont : ContinuousOn ((deriv φ)⁻¹) (Icc 0 s) := by
        have hc := hφ₁.continuousOn.mono hIccU
        apply hc.inv₀
        intro u hu
        exact hne u (hIcc_sub hu)
      have hdiff : DifferentiableOn ℝ ((deriv φ)⁻¹) (interior (Icc 0 s)) := by
        intro u hu
        rw [interior_Icc] at hu
        have huIco : u ∈ Ico (0:ℝ) 1 := ⟨hu.1.le, lt_trans hu.2 hs.2⟩
        have h := ((hdφ₁ u (hsegU huIco)).hasDerivAt.inv (hne u huIco)).differentiableAt
        exact h.differentiableWithinAt
      have hbound : ∀ u ∈ interior (Icc 0 s), deriv ((deriv φ)⁻¹) u ≤ -1 / ϑ := by
        intro u hu
        rw [interior_Icc] at hu
        have huIco : u ∈ Ico (0:ℝ) 1 := ⟨hu.1.le, lt_trans hu.2 hs.2⟩
        exact hpsi_le u huIco
      have h0mem : (0:ℝ) ∈ Icc 0 s := ⟨le_rfl, hs.1⟩
      have hsmem : s ∈ Icc 0 s := ⟨hs.1, le_rfl⟩
      have h := (convex_Icc 0 s).image_sub_le_mul_sub_of_deriv_le hcont hdiff hbound 0 h0mem s
        hsmem hs.1
      have hpos_s : 0 < ((deriv φ)⁻¹) s := inv_pos.mpr (hpos s hs)
      have hrhs : (-1 / ϑ) * (s - 0) = -(s / ϑ) := by ring
      rw [hrhs] at h
      have hle : ((deriv φ)⁻¹) s ≤ ((deriv φ)⁻¹) 0 - s / ϑ := by linarith
      have hlt : 0 < ((deriv φ)⁻¹) 0 - s / ϑ := lt_of_lt_of_le hpos_s hle
      linarith
    have hlt_s : ∀ s ∈ Ico (0:ℝ) 1, s < ϑ / deriv φ 0 := by
      intro s hs
      have h := hmvt s hs
      have hiff := (div_lt_iff₀ hϑpos).mp h
      have heq : ((deriv φ)⁻¹) 0 * ϑ = ϑ / deriv φ 0 := by
        rw [div_eq_mul_inv, mul_comm]; rfl
      rwa [heq] at hiff
    by_contra hcon
    have hgt : ϑ < deriv φ 0 := not_le.mp hcon
    have hratio_lt : ϑ / deriv φ 0 < 1 := (div_lt_one hle_pos).mpr hgt
    have hratio_nonneg : 0 ≤ ϑ / deriv φ 0 := div_nonneg hϑ hle_pos.le
    let s0 := (ϑ / deriv φ 0 + 1) / 2
    have hs0_gt : ϑ / deriv φ 0 < s0 := by simp [s0]; linarith
    have hs0_lt : s0 < 1 := by simp [s0]; linarith
    have hs0_nonneg : 0 ≤ s0 := by simp [s0]; linarith [hratio_nonneg]
    have hs0_mem : s0 ∈ Ico (0:ℝ) 1 := ⟨hs0_nonneg, hs0_lt⟩
    have hfinal := hlt_s s0 hs0_mem
    linarith

end WantedExt.Analysis.Convex.SelfConcordantWanted
