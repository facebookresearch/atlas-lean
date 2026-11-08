/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.LpDiagonalOperator
public import MathlibExt.Analysis.InnerProductSpace.LpShiftOperator

/-!
# Weighted unilateral shifts on `ℓ²(ℕ, 𝕜)`

For bounded weights `w : ℕ → 𝕜`, the weighted forward shift inserts zero
at coordinate `0` and sends input coordinate `n` to output coordinate
`n + 1`, multiplied by `w n`. Its weighted backward shift uses conjugated
weights: output coordinate `i` is `conj (w i) * x (i + 1)`.

The construction uses the canonical operators in `LpShiftOperator` and
`LpDiagonalOperator`. The forward operator is diagonal multiplication
followed by the plain forward shift. The backward operator is the plain
backward shift followed by diagonal multiplication with conjugated weights.
The linear-map interfaces are projections of these continuous linear maps.
The shared diagonal construction specializes the Hilbert-basis operator in
`HilbertBasisDiagonal` to the identity coordinates of `ℓ²`.

Both operator norms equal the supremum `⨆ n, ‖w n‖`. The backward operator
is the adjoint of the forward operator. Their two composites act diagonally
by squared weight moduli, with the forward-after-backward composite killing
coordinate `0`. The forward operator is an isometry exactly when every
weight has modulus `1`; it is injective when no weight vanishes and is not
injective when a weight vanishes. The companion `WeightedShiftCompact`
module proves compactness exactly when the weights tend to zero and contains
subtraction and prefix-truncation results.

These are derived supporting results using the canonical lp factors.
The archived Hilbert-space and spectral material in
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean` provides
related source context; it is not an exact source proof for the weighted results.

## Main declarations

* `weightedShiftFun` / `weightedBackwardFun`: the pointwise shift functions.
* `weightedShiftCLM` / `weightedBackwardCLM`: the canonical bounded compositions.
* `weightedShiftLinMap` / `weightedBackwardLinMap`: their linear-map projections.
* `norm_weightedShiftCLM` / `norm_weightedBackwardCLM`: norms as the weight supremum.
* `adjoint_weightedShiftCLM`: the adjoint is the conjugated backward operator.
* `backward_comp_shift_apply` / `shift_comp_backward_apply`: squared-modulus composites.
* `isometry_weightedShiftCLM_iff`: isometry exactly for unit-modulus weights.
* `injective_weightedShiftCLM` / `not_injective_weightedShiftCLM`: the zero-weight boundary.
* `weightedShiftCLM_one` / `weightedBackwardCLM_one`: equalities to the canonical plain shifts.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.WeightedShiftOperator

open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal ComplexConjugate
open MathlibExt.Analysis.InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The weighted forward-shift function: insert `0` at `0`, and multiply
coordinate `n` by `w n` while shifting it to `n + 1`. -/
def weightedShiftFun (w : ℕ → 𝕜) (x : ℕ → 𝕜) : ℕ → 𝕜
  | 0 => 0
  | n + 1 => w n * x n

/-- The weighted backward-shift function, with conjugated weights so that
it is exactly the adjoint of the weighted forward shift: coordinate `i`
is `conj (w i) * x (i + 1)`. -/
def weightedBackwardFun (w : ℕ → 𝕜) (x : ℕ → 𝕜) (i : ℕ) : 𝕜 :=
  conj (w i) * x (i + 1)

/-- The weighted forward-shift function inserts zero at coordinate `0`. -/
@[simp] theorem weightedShiftFun_zero (w : ℕ → 𝕜) (x : ℕ → 𝕜) :
    weightedShiftFun w x 0 = 0 := rfl

/-- At coordinate `n + 1`, the forward-shift function multiplies input `n` by `w n`. -/
@[simp] theorem weightedShiftFun_succ (w : ℕ → 𝕜) (x : ℕ → 𝕜) (n : ℕ) :
    weightedShiftFun w x (n + 1) = w n * x n := rfl

/-- At coordinate `i`, the backward-shift function uses `conj (w i)` and input `i + 1`. -/
@[simp] theorem weightedBackwardFun_apply (w : ℕ → 𝕜) (x : ℕ → 𝕜) (i : ℕ) :
    weightedBackwardFun w x i = conj (w i) * x (i + 1) := rfl

/-- Convert bounded weight norms to the uniform bound expected by the diagonal API. -/
private theorem exists_uniform_bound {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) : ∃ C, ∀ n, ‖w n‖ ≤ C := by
  simpa only [bddAbove_def, Set.forall_mem_range] using hw

/-- The weighted forward shift as a bounded operator on `ℓ²(ℕ, 𝕜)`: canonical diagonal
multiplication followed by the canonical forward shift. -/
noncomputable def weightedShiftCLM (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜) :=
  LpShiftOperator.shiftCLM ∘L LpDiagonalOperator.diagonalCLM w (by
    exact exists_uniform_bound hw)

/-- The weighted backward shift as a bounded operator on `ℓ²(ℕ, 𝕜)`: the canonical
backward shift followed by diagonal multiplication with conjugated weights. -/
noncomputable def weightedBackwardCLM (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜) :=
  LpDiagonalOperator.diagonalCLM (fun n => star (w n)) (by
    simpa only [norm_star] using exists_uniform_bound hw) ∘L
    LpShiftOperator.backwardCLM

/-- The linear-map projection of the weighted forward bounded operator. -/
noncomputable abbrev weightedShiftLinMap (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜) :=
  (weightedShiftCLM w hw).toLinearMap

/-- The linear-map projection of the weighted backward bounded operator. -/
noncomputable abbrev weightedBackwardLinMap (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜) :=
  (weightedBackwardCLM w hw).toLinearMap

/-- Pointwise action of the weighted forward shift. -/
theorem weightedShiftCLM_apply (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    weightedShiftCLM w hw x i = weightedShiftFun w (x : ℕ → 𝕜) i := by
  cases i <;> simp [weightedShiftCLM, weightedShiftFun,
    LpShiftOperator.shiftCLM_apply, LpDiagonalOperator.diagonalCLM_apply,
    LpShiftOperator.shiftFun]

/-- Pointwise action of the weighted backward shift. -/
theorem weightedBackwardCLM_apply (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    weightedBackwardCLM w hw x i = weightedBackwardFun w (x : ℕ → 𝕜) i := by
  simp [weightedBackwardCLM, weightedBackwardFun,
    LpDiagonalOperator.diagonalCLM_apply, LpShiftOperator.backwardCLM_apply,
    LpShiftOperator.backwardFun, RCLike.star_def]

/-- The coercion of the weighted forward shift is the pointwise weighted
shift function. -/
theorem weightedShiftCLM_apply_coe (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (x : ℓ²(ℕ, 𝕜)) :
    ⇑(weightedShiftCLM w hw x) = weightedShiftFun w (x : ℕ → 𝕜) := by
  funext i; exact weightedShiftCLM_apply w hw x i

/-- The coercion of the weighted forward shift linear map is the pointwise
weighted shift function. -/
theorem weightedShiftLinMap_apply_coe (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (x : ℓ²(ℕ, 𝕜)) :
    ⇑(weightedShiftLinMap w hw x) = weightedShiftFun w (x : ℕ → 𝕜) :=
  weightedShiftCLM_apply_coe w hw x

/-- The coercion of the weighted backward shift linear map is the pointwise
weighted backward shift function. -/
theorem weightedBackwardLinMap_apply_coe (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (x : ℓ²(ℕ, 𝕜)) :
    ⇑(weightedBackwardLinMap w hw x) = weightedBackwardFun w (x : ℕ → 𝕜) := by
  funext i; exact weightedBackwardCLM_apply w hw x i

/-- The weighted-shifted sequence is in `ℓ²` when the weights are bounded. -/
theorem memℓp_weightedShiftFun {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) {x : ℓ²(ℕ, 𝕜)} :
    Memℓp (weightedShiftFun w (x : ℕ → 𝕜)) 2 := by
  rw [← weightedShiftCLM_apply_coe w hw x]
  exact lp.memℓp _

/-- The weighted-backward-shifted sequence is in `ℓ²` when the weights
are bounded. -/
theorem memℓp_weightedBackwardFun {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) {x : ℓ²(ℕ, 𝕜)} :
    Memℓp (weightedBackwardFun w (x : ℕ → 𝕜)) 2 := by
  rw [← weightedBackwardLinMap_apply_coe w hw x]
  exact lp.memℓp _

/-- The weighted forward shift sends the `n`-th standard basis vector to
the `(n + 1)`-st one, scaled by `w n`. -/
theorem weightedShiftCLM_single (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (n : ℕ) :
    weightedShiftCLM w hw (lp.single 2 n (1 : 𝕜)) = lp.single 2 (n + 1) (w n) := by
  apply lp.ext; funext i
  cases i with
  | zero => simp [weightedShiftCLM_apply]
  | succ m => by_cases h : m = n <;> simp [weightedShiftCLM_apply, h]

/-- The weighted backward shift sends the `(n + 1)`-st standard basis vector
to the `n`-th one, scaled by `conj (w n)`. -/
theorem weightedBackwardCLM_single_succ (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (n : ℕ) :
    weightedBackwardCLM w hw (lp.single 2 (n + 1) (1 : 𝕜)) =
      lp.single 2 n (conj (w n)) := by
  apply lp.ext; funext i
  by_cases h : i = n <;> simp [weightedBackwardCLM_apply, h]

/-- The norm of the weighted forward shift is at most any uniform bound on
the moduli of the weights. -/
theorem norm_weightedShiftCLM_le_of_forall_le {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) {C : ℝ} (hC : ∀ n, ‖w n‖ ≤ C) :
    ‖weightedShiftCLM w hw‖ ≤ C := by
  rw [weightedShiftCLM]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    rw [LpShiftOperator.norm_shiftCLM, one_mul]
    exact LpDiagonalOperator.norm_diagonalCLM_le w (exists_uniform_bound hw)
      (le_trans (norm_nonneg (w 0)) (hC 0)) hC)

/-- The operator norm of the weighted forward shift is the supremum of the
moduli of the weights. -/
theorem norm_weightedShiftCLM {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) :
    ‖weightedShiftCLM w hw‖ = ⨆ n, ‖w n‖ := by
  apply le_antisymm
  · rw [weightedShiftCLM]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (by
      rw [LpShiftOperator.norm_shiftCLM, one_mul,
        LpDiagonalOperator.norm_diagonalCLM])
  · apply ciSup_le
    intro n
    have h1 := ContinuousLinearMap.le_opNorm (σ₁₂ := RingHom.id 𝕜)
      (f := weightedShiftCLM w hw) (x := lp.single 2 n (1 : 𝕜))
    rw [weightedShiftCLM_single, lp.norm_single (by norm_num),
      lp.norm_single (by norm_num), norm_one, mul_one] at h1
    exact h1

/-- The adjoint of the weighted forward shift is the weighted backward
shift (whose weights are already conjugated in its definition). -/
theorem adjoint_weightedShiftCLM {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) :
    (weightedShiftCLM w hw)† = weightedBackwardCLM w hw := by
  rw [weightedShiftCLM, ContinuousLinearMap.adjoint_comp,
    LpShiftOperator.adjoint_shiftCLM, LpDiagonalOperator.adjoint_diagonalCLM]
  rfl

/-- The operator norm of the weighted backward shift is the supremum of the
moduli of the weights. -/
theorem norm_weightedBackwardCLM {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) :
    ‖weightedBackwardCLM w hw‖ = ⨆ n, ‖w n‖ := by
  apply le_antisymm
  · rw [weightedBackwardCLM]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left LpShiftOperator.norm_backwardCLM_le (norm_nonneg _)).trans_eq
        (by rw [LpDiagonalOperator.norm_diagonalCLM, mul_one]; simp only [norm_star]))
  · apply ciSup_le
    intro n
    have h1 := ContinuousLinearMap.le_opNorm (σ₁₂ := RingHom.id 𝕜)
      (f := weightedBackwardCLM w hw) (x := lp.single 2 (n + 1) (1 : 𝕜))
    rw [weightedBackwardCLM_single_succ, lp.norm_single (by norm_num), RCLike.norm_conj,
      lp.norm_single (by norm_num), norm_one, mul_one] at h1
    exact h1

/-- The weighted forward shift does not increase norms by more than the
supremum of the moduli of the weights. -/
theorem norm_weightedShiftLinMap_apply_le {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (x : ℓ²(ℕ, 𝕜)) :
    ‖weightedShiftLinMap w hw x‖ ≤ (⨆ n, ‖w n‖) * ‖x‖ := by
  exact (weightedShiftCLM w hw).le_opNorm x |>.trans_eq (by rw [norm_weightedShiftCLM])

/-- The weighted backward shift does not increase norms by more than the
supremum of the moduli of the weights. -/
theorem norm_weightedBackwardLinMap_apply_le {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (x : ℓ²(ℕ, 𝕜)) :
    ‖weightedBackwardLinMap w hw x‖ ≤ (⨆ n, ‖w n‖) * ‖x‖ := by
  exact (weightedBackwardCLM w hw).le_opNorm x |>.trans_eq (by rw [norm_weightedBackwardCLM])

/-- The composite `B ∘ S` acts diagonally by `‖w i‖ ^ 2`. -/
theorem backward_comp_shift_apply (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    (weightedBackwardCLM w hw ∘L weightedShiftCLM w hw) x i =
      (‖w i‖ ^ 2 : 𝕜) * (x : ℕ → 𝕜) i := by
  rw [ContinuousLinearMap.comp_apply, weightedBackwardCLM_apply,
    weightedBackwardFun_apply, weightedShiftCLM_apply, weightedShiftFun_succ,
    ← mul_assoc, RCLike.conj_mul]

/-- The composite `S ∘ B` kills coordinate `0` and acts diagonally by
`‖w (i - 1)‖ ^ 2` on coordinate `i > 0`. -/
theorem shift_comp_backward_apply (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    (weightedShiftCLM w hw ∘L weightedBackwardCLM w hw) x i =
      if i = 0 then 0 else (‖w (i - 1)‖ ^ 2 : 𝕜) * (x : ℕ → 𝕜) i := by
  cases i with
  | zero => simp [weightedShiftCLM_apply]
  | succ n => simp [weightedShiftCLM_apply, weightedBackwardCLM_apply,
      ← mul_assoc, RCLike.mul_conj]

/-- If every weight has modulus `1`, the backward shift is a left inverse
of the forward shift. -/
theorem backward_comp_shift_eq_one (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (h : ∀ n, ‖w n‖ = 1) :
    weightedBackwardCLM w hw ∘L weightedShiftCLM w hw =
      (1 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  rw [backward_comp_shift_apply, h]
  simp

/-- The weighted forward shift is injective when no weight vanishes: the
coordinates of `x` are recovered from `S x` one by one. -/
theorem injective_weightedShiftCLM (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (h : ∀ n, w n ≠ 0) :
    Function.Injective (weightedShiftCLM w hw) := by
  intro a b hab; apply lp.ext; funext i
  have h2 := congr_fun (congr_arg (fun z : ℓ²(ℕ, 𝕜) => (z : ℕ → 𝕜)) hab) (i + 1)
  simp only [weightedShiftCLM_apply, weightedShiftFun_succ] at h2
  exact mul_left_cancel₀ (h i) h2

/-- The weighted forward shift is not injective when some weight vanishes:
it kills the corresponding standard basis vector. -/
theorem not_injective_weightedShiftCLM (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (n : ℕ) (hn : w n = 0) :
    ¬ Function.Injective (weightedShiftCLM w hw) := by
  intro hinj
  have h0 : weightedShiftCLM w hw (lp.single 2 n (1 : 𝕜)) = 0 := by
    rw [weightedShiftCLM_single, hn]; simp
  have hne : (lp.single 2 n (1 : 𝕜) : ℓ²(ℕ, 𝕜)) ≠ 0 := by
    intro h; have := congr_fun (congr_arg (fun z : ℓ²(ℕ, 𝕜) => (z : ℕ → 𝕜)) h) n; simp at this
  exact hne (hinj (by rw [h0, map_zero]))

/-- With every weight of modulus `1`, the weighted forward shift
preserves norms. -/
theorem norm_weightedShiftCLM_apply_of_forall_norm_eq_one (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (h : ∀ n, ‖w n‖ = 1)
    (x : ℓ²(ℕ, 𝕜)) : ‖weightedShiftCLM w hw x‖ = ‖x‖ := by
  have hS : ‖weightedShiftCLM w hw‖ = 1 := by
    rw [norm_weightedShiftCLM]
    simp [h]
  have hB : ‖weightedBackwardCLM w hw‖ = 1 := by
    rw [norm_weightedBackwardCLM]
    simp [h]
  apply le_antisymm
  · exact (ContinuousLinearMap.le_opNorm _ _).trans_eq (by rw [hS, one_mul])
  · have hx := ContinuousLinearMap.le_opNorm (weightedBackwardCLM w hw)
        (weightedShiftCLM w hw x)
    rw [← ContinuousLinearMap.comp_apply, backward_comp_shift_eq_one w hw h,
      one_apply_eq_self, hB, one_mul] at hx
    exact hx

/-- The weighted forward shift is an isometry exactly when every weight
has modulus `1`. -/
theorem isometry_weightedShiftCLM_iff (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) :
    Isometry (weightedShiftCLM w hw) ↔ ∀ n, ‖w n‖ = 1 := by
  constructor
  · intro h n
    have h1 := (isometry_iff_dist_eq.mp h) (lp.single 2 n (1 : 𝕜)) 0
    rw [map_zero, dist_zero_right, dist_zero_right, weightedShiftCLM_single,
      lp.norm_single (by norm_num), lp.norm_single (by norm_num), norm_one] at h1
    exact h1
  · intro h; rw [isometry_iff_dist_eq]; intro x y
    rw [dist_eq_norm, dist_eq_norm, ← map_sub,
      norm_weightedShiftCLM_apply_of_forall_norm_eq_one w hw h]

/-- With every weight equal to `1`, the weighted forward operator is the canonical forward shift. -/
theorem weightedShiftCLM_one {𝕜 : Type*} [RCLike 𝕜]
    (hw : BddAbove (Set.range fun _ : ℕ => ‖(1 : 𝕜)‖)) :
    weightedShiftCLM (fun _ : ℕ => (1 : 𝕜)) hw = LpShiftOperator.shiftCLM := by
  ext x i; cases i <;> simp [weightedShiftCLM_apply, LpShiftOperator.shiftCLM_apply]

/-- With every weight equal to `1`, the weighted backward operator is the canonical
backward shift. -/
theorem weightedBackwardCLM_one {𝕜 : Type*} [RCLike 𝕜]
    (hw : BddAbove (Set.range fun _ : ℕ => ‖(1 : 𝕜)‖)) :
    weightedBackwardCLM (fun _ : ℕ => (1 : 𝕜)) hw = LpShiftOperator.backwardCLM := by
  ext x i; simp [weightedBackwardCLM_apply, LpShiftOperator.backwardCLM_apply]

end MathlibExt.Analysis.InnerProductSpace.WeightedShiftOperator
