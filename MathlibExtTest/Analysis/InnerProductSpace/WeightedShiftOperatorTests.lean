/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.WeightedShiftCompact
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Tests for weighted unilateral shifts on `ℓ²(ℕ, 𝕜)`

Concrete weights pin down the main statements:

* constant weights `2` over `ℝ`: norm `2`, and `B ∘ S` is multiplication
  by `4`;
* constant weights `1` over `ℝ`: `B ∘ S = 1`, and the shift is not
  compact;
* constant weights `-1` over `ℝ`: the shift is an isometry;
* constant weights `i` over `ℂ`: the adjoint is the backward shift with
  weight `conj i = -i`;
* weights `1 / (n + 1)` over `ℝ`: the shift is compact (weights tend to
  `0`) and injective (no weight vanishes);
* a weight vanishing at `0` only: the shift is not injective;
* the shift is additive in the weights, on constant weights `3` and `1`.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.InnerProductSpace.WeightedShiftOperatorTests

open Filter Topology
open scoped _root_.lp ENNReal ComplexConjugate
open MathlibExt.Analysis.InnerProductSpace.WeightedShiftOperator
open MathlibExt.Analysis.InnerProductSpace.WeightedShiftCompact

/-- A constant weight sequence is bounded, by its own modulus. -/
theorem bddAbove_const {𝕜 : Type*} [RCLike 𝕜] (c : 𝕜) :
    BddAbove (Set.range fun _ : ℕ => ‖c‖) :=
  ⟨‖c‖, by rintro y ⟨n, rfl⟩; exact le_refl _⟩

/-- With constant weights `2` over `ℝ`, the shift has norm `2`. -/
example : ‖weightedShiftCLM (fun _ : ℕ => (2 : ℝ)) (bddAbove_const 2)‖ = 2 := by
  rw [norm_weightedShiftCLM]
  simp

/-- With constant weights `2` over `ℝ`, the composite `B ∘ S` multiplies
by `4`. -/
example (x : ℓ²(ℕ, ℝ)) (i : ℕ) :
    (weightedBackwardCLM (fun _ : ℕ => (2 : ℝ)) (bddAbove_const 2) ∘L
      weightedShiftCLM (fun _ : ℕ => (2 : ℝ)) (bddAbove_const 2)) x i =
    (4 : ℝ) * (x : ℕ → ℝ) i := by
  rw [backward_comp_shift_apply]
  norm_num

/-- With constant weights `1` over `ℝ`, the backward shift is a left
inverse of the forward shift. -/
example : weightedBackwardCLM (fun _ : ℕ => (1 : ℝ)) (bddAbove_const 1) ∘L
      weightedShiftCLM (fun _ : ℕ => (1 : ℝ)) (bddAbove_const 1) =
    (1 : ℓ²(ℕ, ℝ) →L[ℝ] ℓ²(ℕ, ℝ)) :=
  backward_comp_shift_eq_one _ _ (fun n => by simp)

/-- With constant weights `1` over `ℝ`, the shift is not compact: its
weights do not tend to `0`. -/
example : ¬ IsCompactOperator
    (weightedShiftCLM (fun _ : ℕ => (1 : ℝ)) (bddAbove_const 1)) := by
  intro h
  have hlim := (isCompactOperator_weightedShiftCLM_iff (bddAbove_const (1 : ℝ))).mp h
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  exact one_ne_zero h10

/-- With constant weights `-1` over `ℝ`, the shift is an isometry. -/
example : Isometry
    (weightedShiftCLM (fun _ : ℕ => (-1 : ℝ)) (bddAbove_const (-1))) :=
  (isometry_weightedShiftCLM_iff _ _).mpr (fun n => by simp)

/-- With constant weights `2` over `ℝ`, the shift is not an isometry. -/
example : ¬ Isometry
    (weightedShiftCLM (fun _ : ℕ => (2 : ℝ)) (bddAbove_const 2)) := by
  intro h
  have h0 := (isometry_weightedShiftCLM_iff _ _).mp h 0
  norm_num at h0

/-- With constant weights `i` over `ℂ`, the backward shift sends `e₁` to
`-i • e₀`: the adjoint uses conjugated weights. -/
example : weightedBackwardCLM (fun _ : ℕ => Complex.I) (bddAbove_const Complex.I)
      (lp.single 2 1 (1 : ℂ)) = lp.single 2 0 (-Complex.I) := by
  rw [weightedBackwardCLM_single_succ]
  congr 1
  exact Complex.conj_I

/-- With constant weights `i` over `ℂ`, the backward shift has norm `1`. -/
example : ‖weightedBackwardCLM (fun _ : ℕ => Complex.I) (bddAbove_const Complex.I)‖ = 1 := by
  rw [norm_weightedBackwardCLM]
  simp

/-- The shift is additive in the weights, on constant weights `3` and `1`. -/
example : weightedShiftCLM ((fun _ : ℕ => (3 : ℝ)) - (fun _ : ℕ => (1 : ℝ)))
      (bddAbove_sub (bddAbove_const 3) (bddAbove_const 1)) =
    weightedShiftCLM (fun _ : ℕ => (3 : ℝ)) (bddAbove_const 3) -
      weightedShiftCLM (fun _ : ℕ => (1 : ℝ)) (bddAbove_const 1) :=
  weightedShiftCLM_sub _ _ _

/-- The weights `1 / (n + 1)` over `ℝ` are bounded by `1`. -/
theorem bddAbove_inv_succ :
    BddAbove (Set.range fun (n : ℕ) => ‖(1 : ℝ) / ((n : ℝ) + 1)‖) := by
  refine ⟨1, ?_⟩
  rintro y ⟨n, rfl⟩
  show ‖(1 : ℝ) / ((n : ℝ) + 1)‖ ≤ 1
  rw [Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1))]
  rw [div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- The weights `1 / (n + 1)` tend to `0`. -/
theorem tendsto_inv_succ :
    Tendsto (fun (n : ℕ) => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- With weights `1 / (n + 1)`, the shift is compact. -/
example : IsCompactOperator
    (weightedShiftCLM (fun (n : ℕ) => (1 : ℝ) / ((n : ℝ) + 1)) bddAbove_inv_succ) :=
  (isCompactOperator_weightedShiftCLM_iff bddAbove_inv_succ).mpr tendsto_inv_succ

/-- With weights `1 / (n + 1)`, the shift is injective: no weight
vanishes. -/
example : Function.Injective
    (weightedShiftCLM (fun (n : ℕ) => (1 : ℝ) / ((n : ℝ) + 1)) bddAbove_inv_succ) :=
  injective_weightedShiftCLM _ _
    (fun n => div_ne_zero one_ne_zero (ne_of_gt (by positivity)))

/-- With weights vanishing only at `0`, the shift is not injective. -/
example : ¬ Function.Injective
    (weightedShiftCLM (fun n => if n = 0 then (0 : ℝ) else 1)
      ⟨1, by rintro y ⟨n, rfl⟩; by_cases h : n = 0 <;> simp [h]⟩) :=
  not_injective_weightedShiftCLM _ _ 0 (by simp)

end MathlibExtTest.Analysis.InnerProductSpace.WeightedShiftOperatorTests
