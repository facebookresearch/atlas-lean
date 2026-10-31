/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.FluxBalanceValue

/-! Tests for the FBA value function: the one-reaction problem `max v` subject to `v = b`,
`0 ≤ v ≤ 2` has value `b` on `[0, 2]`, unique optimal dual price `1` at `b = 1`, hence
derivative `1` there; piecewise linearity on the two-reaction pathway of the core tests; and the
junk value just outside the feasible interval. -/

open Matrix

namespace MathlibExtTest.Biology.Dynamics.FluxBalanceValue

open MathlibExt.Biology.Dynamics.SystemsBiology

/-- One metabolite produced by one reaction: `S = [1]`. -/
def sOne : Matrix (Fin 1) (Fin 1) ℝ := !![1]

theorem mulVec_sOne (v : Fin 1 → ℝ) : sOne *ᵥ v = v := by
  funext i
  fin_cases i
  simp [sOne, Matrix.mulVec, dotProduct]

theorem fbaFeasible_sOne_iff (b : Fin 1 → ℝ) :
    (fbaFeasible sOne 0 ![2] b).Nonempty ↔ 0 ≤ b 0 ∧ b 0 ≤ 2 := by
  constructor
  · rintro ⟨v, hS, hl, hu⟩
    rw [mulVec_sOne] at hS
    subst hS
    exact ⟨by simpa using hl 0, by simpa using hu 0⟩
  · rintro ⟨h0, h2⟩
    refine ⟨b, mulVec_sOne b, fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> simpa

/-- The optimal value is `b` on the feasible interval. -/
theorem fbaValue_sOne {b : Fin 1 → ℝ} (h0 : 0 ≤ b 0) (h2 : b 0 ≤ 2) :
    fbaValue sOne 0 ![2] ![1] b = b 0 := by
  obtain ⟨v, hv, hV, -⟩ := exists_fbaValue_eq (c := ![1])
    ((fbaFeasible_sOne_iff b).2 ⟨h0, h2⟩)
  rw [hV, ← mulVec_sOne v, hv.1]
  simp [dotProduct]

/-- Junk value: just above the interval the problem is infeasible and `fbaValue = sSup ∅ = 0`,
so the value function jumps at the boundary `b = 2`; the derivative theorem needs an interior
point. -/
example : fbaValue sOne 0 ![2] ![1] ![3] = 0 := by
  have : fbaFeasible sOne 0 ![2] ![3] = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty, fbaFeasible_sOne_iff]
    norm_num
  simp [fbaValue, this]

/-- `b = 1` is an interior feasible right-hand side. -/
theorem one_mem_interior :
    ![(1 : ℝ)] ∈ interior {b' : Fin 1 → ℝ | (fbaFeasible sOne 0 ![2] b').Nonempty} := by
  refine mem_interior.2 ⟨{b' | 0 < b' 0 ∧ b' 0 < 2}, fun b' hb' => ?_, ?_, ?_⟩
  · exact (fbaFeasible_sOne_iff b').2 ⟨hb'.1.le, hb'.2.le⟩
  · exact (isOpen_lt continuous_const (continuous_apply 0)).inter
      (isOpen_lt (continuous_apply 0) continuous_const)
  · norm_num

/-- At `b = 1` the only optimal dual price is `1`: dual feasibility is `y + α - β = 1` and the
dual objective is `y + 2 α = 1 + α + β`. -/
theorem optimal_dual_sOne (y' : Fin 1 → ℝ) :
    (∃ α β, fbaDualFeasible sOne ![1] y' α β ∧
        ∀ y'' α'' β'', fbaDualFeasible sOne ![1] y'' α'' β'' →
          fbaDualValue 0 ![2] ![1] y' α β ≤ fbaDualValue 0 ![2] ![1] y'' α'' β'') ↔
      y' = ![1] := by
  have hT : ∀ y : Fin 1 → ℝ, sOneᵀ *ᵥ y = y := fun y => by
    funext i
    fin_cases i
    simp [sOne, Matrix.mulVec, dotProduct]
  have hfeas : ∀ y α β : Fin 1 → ℝ, fbaDualFeasible sOne ![1] y α β ↔
      0 ≤ α 0 ∧ 0 ≤ β 0 ∧ y 0 + α 0 - β 0 = 1 := fun y α β => by
    simp only [fbaDualFeasible, hT]
    constructor
    · rintro ⟨hα, hβ, h⟩
      exact ⟨hα 0, hβ 0, by simpa using congrFun h 0⟩
    · rintro ⟨hα, hβ, h⟩
      refine ⟨fun i => ?_, fun i => ?_, funext fun i => ?_⟩ <;> fin_cases i <;> simpa
  have hval : ∀ y α β : Fin 1 → ℝ, fbaDualValue 0 ![2] ![1] y α β = y 0 + 2 * α 0 :=
    fun y α β => by simp [fbaDualValue, dotProduct]
  constructor
  · rintro ⟨α, β, hd, hopt⟩
    obtain ⟨hα, hβ, h⟩ := (hfeas _ _ _).1 hd
    have := hopt ![1] 0 0 ((hfeas _ _ _).2 ⟨le_rfl, le_rfl, by simp⟩)
    rw [hval, hval] at this
    simp only [Matrix.cons_val_zero, Pi.zero_apply, mul_zero, add_zero] at this
    funext i
    rw [Subsingleton.elim i 0, Matrix.cons_val_zero]
    linarith
  · rintro rfl
    refine ⟨0, 0, (hfeas _ _ _).2 ⟨le_rfl, le_rfl, by simp⟩, fun y'' α'' β'' hd => ?_⟩
    obtain ⟨hα, hβ, h⟩ := (hfeas _ _ _).1 hd
    rw [hval, hval]
    simp only [Matrix.cons_val_zero, Pi.zero_apply, mul_zero, add_zero]
    linarith

/-- The shadow price of the metabolite at `b = 1` is the derivative `1`. -/
example : HasFDerivAt (fbaValue sOne 0 ![2] ![1])
    (∑ i, (![1] : Fin 1 → ℝ) i • ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 1 => ℝ) i) ![1] :=
  hasFDerivAt_fbaValue_of_unique one_mem_interior optimal_dual_sOne

/-- Piecewise linearity of the value of `max v₁` subject to `v₀ - v₁ = b`, `0 ≤ v ≤ (1, 2)`:
finitely many affine pieces whose minimum is the value at every feasible `b`. -/
example : ∃ T : Finset ((Fin 1 → ℝ) × ℝ), ∀ b : Fin 1 → ℝ,
    (fbaFeasible !![1, -1] 0 ![1, 2] b).Nonempty →
      IsLeast ((fun p : (Fin 1 → ℝ) × ℝ => p.1 ⬝ᵥ b + p.2) '' (T : Set _))
        (fbaValue !![1, -1] 0 ![1, 2] ![0, 1] b) :=
  exists_finset_isLeast_fbaValue _ _ _ _

/-- At a feasible `b` the finite family of dual solutions is nonempty (it contains an optimal
one). -/
example : ∃ T : Finset ((Fin 1 → ℝ) × ℝ), T.Nonempty := by
  obtain ⟨T, -, hT⟩ := exists_finset_optimal_fbaDual sOne 0 ![2] ![1]
  obtain ⟨p, hp, -⟩ := hT ![1] ((fbaFeasible_sOne_iff _).2 ⟨by norm_num, by norm_num⟩)
  exact ⟨T, p, hp⟩

#print axioms exists_finset_optimal_fbaDual
#print axioms exists_finset_isLeast_fbaValue
#print axioms hasFDerivAt_fbaValue_of_unique

end MathlibExtTest.Biology.Dynamics.FluxBalanceValue
