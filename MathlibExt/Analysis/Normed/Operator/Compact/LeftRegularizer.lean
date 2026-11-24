/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.Order.IsLUB

/-!
# Injective operators with a compact left-parametrix error

An injective continuous linear map with a continuous left regularizer modulo
actual compact operators is a closed topological embedding. The scalar field
and both normed spaces may be incomplete, and zero spaces are allowed.

The lower-bound argument uses the bounded-shell pattern from Mathlib's compact
Fredholm alternative, but uses injectivity of the original map, not a
non-eigenvalue or injectivity assumption on the composite. Both compactness
arguments produce limits in the original domain rather than in a completion.
-/

@[expose] public section

open Filter Function Set Topology

universe u𝕜 uE uF

namespace ContinuousLinearMap

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- An injective map with compact left-parametrix error has a positive norm
lower bound, without a completeness or nontrivial-space assumption. -/
private theorem exists_pos_mul_norm_le_of_injective_compact_left_parametrix
    (S : E →L[𝕜] F) (V : F →L[𝕜] E) (hS : Function.Injective S)
    (hCompact : IsCompactOperator (V.comp S - (1 : E →L[𝕜] E))) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : E, c * ‖z‖ ≤ ‖S z‖ := by
  classical
  by_contra hNot
  have hFail (ε : ℝ) (hε : 0 < ε) : ∃ z : E, ‖S z‖ < ε * ‖z‖ := by
    by_contra hNo
    have hBound (z : E) : ε * ‖z‖ ≤ ‖S z‖ :=
      le_of_not_gt fun hz => hNo ⟨z, hz⟩
    exact hNot ⟨ε, hε, hBound⟩
  obtain ⟨ν, hν⟩ := NormedField.exists_one_lt_norm 𝕜
  let a : ℝ := ‖ν‖⁻¹
  have ha : 0 < a := inv_pos.mpr (zero_lt_one.trans hν)
  have hSmall (ε : ℝ) (hε : 0 < ε) :
      ∃ z : E, ‖z‖ ≤ 1 ∧ a ≤ ‖z‖ ∧ ‖S z‖ < ε := by
    obtain ⟨z, hz⟩ := hFail ε hε
    have hzNe : z ≠ 0 := by
      intro hzZero
      subst z
      have hFalse : (0 : ℝ) < 0 := by
        simpa only [map_zero, norm_zero, mul_zero] using hz
      exact (lt_irrefl (0 : ℝ)) hFalse
    obtain ⟨d, hd, hUpper, hLower, _hInv⟩ :=
      rescale_to_shell (c := ν) (ε := (1 : ℝ)) (x := z)
        hν zero_lt_one hzNe
    refine ⟨d • z, hUpper.le, ?_, ?_⟩
    · simpa only [a, one_div] using hLower
    · calc
        ‖S (d • z)‖ = ‖d‖ * ‖S z‖ := by rw [map_smul, norm_smul]
        _ < ‖d‖ * (ε * ‖z‖) :=
          mul_lt_mul_of_pos_left hz (norm_pos_iff.mpr hd)
        _ = ε * ‖d • z‖ := by
          rw [norm_smul]
          exact mul_left_comm _ _ _
        _ ≤ ε := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hUpper.le hε.le
  obtain ⟨δ, _hδanti, hδpos, hδlim⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  let x : ℕ → E := fun n => Classical.choose (hSmall (δ n) (hδpos n))
  have hx (n : ℕ) : ‖x n‖ ≤ 1 ∧ a ≤ ‖x n‖ ∧ ‖S (x n)‖ < δ n :=
    Classical.choose_spec (hSmall (δ n) (hδpos n))
  have hS0 : Tendsto (fun n : ℕ => S (x n)) atTop (𝓝 (0 : F)) :=
    squeeze_zero_norm (fun n => (hx n).2.2.le) hδlim
  let C : E →L[𝕜] E := V.comp S - 1
  have hC : IsCompactOperator C := hCompact
  obtain ⟨K, hK, hKimage⟩ :=
    IsCompactOperator.image_closedBall_subset_compact
      (f := C.toLinearMap) hC (1 : ℝ)
  have hKmem (n : ℕ) : C (x n) ∈ K :=
    hKimage ⟨x n, mem_closedBall_zero_iff.mpr (hx n).1, rfl⟩
  obtain ⟨k, _hkK, ψ, hψ, hCxψ⟩ :=
    hK.tendsto_subseq (x := fun n : ℕ => C (x n)) hKmem
  have hIdentity (z : E) : V (S z) - C z = z := by
    change V (S z) - (V (S z) - z) = z
    exact sub_sub_cancel _ _
  have hVSψ0 : Tendsto (fun n : ℕ => V (S (x (ψ n)))) atTop (𝓝 (0 : E)) := by
    simpa only [map_zero, Function.comp_def] using
      (V.continuous.tendsto (0 : F)).comp (hS0.comp hψ.tendsto_atTop)
  have hXlim : Tendsto (fun n : ℕ => x (ψ n)) atTop (𝓝 (-k)) := by
    simpa only [Function.comp_def, hIdentity, zero_sub] using hVSψ0.sub hCxψ
  have hSk : S (-k) = 0 :=
    tendsto_nhds_unique
      ((S.continuous.tendsto (-k)).comp hXlim)
      (hS0.comp hψ.tendsto_atTop)
  have hNeg : -k = (0 : E) := hS (by simpa only [map_zero] using hSk)
  have hkZero : k = 0 := neg_eq_zero.mp hNeg
  have hX0 : Tendsto (fun n : ℕ => x (ψ n)) atTop (𝓝 (0 : E)) := by
    simpa only [hkZero, neg_zero] using hXlim
  rw [NormedAddGroup.tendsto_nhds_zero] at hX0
  have hBad : ∀ᶠ n : ℕ in atTop, False :=
    (hX0 a ha).mono fun n hn => (not_lt_of_ge (hx (ψ n)).2.1) hn
  simp only [Filter.eventually_const] at hBad

/-- An injective continuous linear map with an actual compact left-parametrix
error is a closed topological embedding. Neither ambient space nor the scalar
field need be complete, and the left regularizer need not be injective. -/
theorem isClosedEmbedding_of_injective_compact_left_parametrix
    (S : E →L[𝕜] F) (V : F →L[𝕜] E) (hS : Function.Injective S)
    (hCompact : IsCompactOperator (V.comp S - (1 : E →L[𝕜] E))) :
    Topology.IsClosedEmbedding S := by
  classical
  obtain ⟨c, hc, hBound⟩ :=
    exists_pos_mul_norm_le_of_injective_compact_left_parametrix S V hS hCompact
  obtain ⟨A, hA⟩ : ∃ A : NNReal, AntilipschitzWith A S :=
    antilipschitzWith_iff_exists_mul_le_norm.mpr ⟨c, hc, hBound⟩
  have hEmbed : Topology.IsEmbedding S := hA.isEmbedding S.continuous
  refine { hEmbed with isClosed_range := ?_ }
  apply isClosed_of_closure_subset
  intro y hy
  obtain ⟨z, hzRange, hzlim⟩ := mem_closure_iff_seq_limit.mp hy
  let x : ℕ → E := fun n => Classical.choose (hzRange n)
  have hx (n : ℕ) : S (x n) = z n := Classical.choose_spec (hzRange n)
  have hSx : Tendsto (fun n : ℕ => S (x n)) atTop (𝓝 y) := by
    simpa only [hx] using hzlim
  have hSbound : ∀ᶠ n : ℕ in atTop, ‖S (x n)‖ ≤ ‖y‖ + 1 :=
    hSx.norm.eventually_le_const (lt_add_of_pos_right _ zero_lt_one)
  let r : ℝ := (‖y‖ + 1) / c
  have hxBall : ∀ᶠ n : ℕ in atTop, x n ∈ Metric.closedBall (0 : E) r := by
    refine hSbound.mono ?_
    intro n hn
    apply mem_closedBall_zero_iff.mpr
    dsimp only [r]
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm] using (hBound (x n)).trans hn
  let C : E →L[𝕜] E := V.comp S - 1
  have hC : IsCompactOperator C := hCompact
  obtain ⟨K, hK, hKimage⟩ :=
    IsCompactOperator.image_closedBall_subset_compact (f := C.toLinearMap) hC r
  have hCK : ∀ᶠ n : ℕ in atTop, C (x n) ∈ K :=
    hxBall.mono fun n hn => hKimage ⟨x n, hn, rfl⟩
  obtain ⟨k, _hkK, ψ, hψ, hCxψ⟩ := hK.tendsto_subseq' hCK.frequently
  have hIdentity (t : E) : V (S t) - C t = t := by
    change V (S t) - (V (S t) - t) = t
    exact sub_sub_cancel _ _
  have hXlim : Tendsto (fun n : ℕ => x (ψ n)) atTop (𝓝 (V y - k)) := by
    simpa only [Function.comp_def, hIdentity] using
      ((V.continuous.tendsto y).comp (hSx.comp hψ.tendsto_atTop)).sub hCxψ
  have hPreimage : S (V y - k) = y :=
    tendsto_nhds_unique
      ((S.continuous.tendsto (V y - k)).comp hXlim)
      (hSx.comp hψ.tendsto_atTop)
  exact ⟨V y - k, hPreimage⟩

end ContinuousLinearMap
