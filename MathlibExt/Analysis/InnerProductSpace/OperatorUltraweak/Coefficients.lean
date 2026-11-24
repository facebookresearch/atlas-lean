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

public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Actual square-summable rank-one operator coefficients

The two original square-summable vector sequences define the actual
absolutely convergent sum of matrix coefficients. Diagonal operator action
on l-two and its computed norm bound make that sum a bounded complex-linear
functional of the actual operator. No trace-class duality, topology model,
norm certificate, nontriviality or separability input is supplied.
-/

@[expose] public section
noncomputable section
open scoped ENNReal InnerProductSpace
namespace OperatorUltraweak
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Actual square-summable vector sequences, including the zero Hilbert space. -/
abbrev VectorSequence (H : Type u) [NormedAddCommGroup H] := lp (fun _ : ℕ => H) 2

/-- The actual bounded operator acts on every source vector coordinate. -/
def diagonal (T : H →L[ℂ] H) : VectorSequence H →L[ℂ] VectorSequence H :=
  lp.mapCLM 2 (fun _ : ℕ => T) (norm_nonneg T) (fun _ => le_rfl)

/-- The diagonal operator has exactly the actual original coordinate values. -/
theorem diagonal_apply (T : H →L[ℂ] H) (x : VectorSequence H) (n : ℕ) :
    diagonal T x n = T (x n) := rfl

/-- The diagonal action has the source operator's genuine norm bound. -/
theorem diagonal_norm_le (T : H →L[ℂ] H) : ‖diagonal T‖ ≤ ‖T‖ :=
  lp.norm_mapCLM_le 2 (fun _ : ℕ => T) (norm_nonneg T) (fun _ => le_rfl)

/-- Coordinate action on a fixed square-summable source vector is additive in the actual operator. -/
theorem action_add (x : VectorSequence H) (T U : H →L[ℂ] H) :
    diagonal (T + U) x = diagonal T x + diagonal U x := by
  apply lp.ext
  funext n
  change (T + U) (x n) = T (x n) + U (x n)
  rfl

/-- Coordinate action preserves the actual complex scalar action on operators. -/
theorem action_smul (x : VectorSequence H) (c : ℂ) (T : H →L[ℂ] H) :
    diagonal (c • T) x = c • diagonal T x := by
  apply lp.ext
  funext n
  change (c • T) (x n) = c • T (x n)
  rfl

/-- The fixed-sequence operator action has its computed finite norm bound. -/
theorem action_norm_le (x : VectorSequence H) (T : H →L[ℂ] H) :
    ‖diagonal T x‖ ≤ ‖x‖ * ‖T‖ := by
  have h := ((diagonal T).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (diagonal_norm_le T) (norm_nonneg x))
  exact h.trans_eq (mul_comm _ _)

/-- The actual complex-linear map from bounded operators to their action on one source l-two vector. -/
def action (x : VectorSequence H) : (H →L[ℂ] H) →L[ℂ] VectorSequence H :=
  ({ toFun := fun T => diagonal T x
     map_add' := action_add x
     map_smul' := action_smul x } : (H →L[ℂ] H) →ₗ[ℂ] VectorSequence H).mkContinuous
    ‖x‖ (action_norm_le x)

/-- The bounded action map retains every actual source coordinate. -/
theorem action_apply (x : VectorSequence H) (T : H →L[ℂ] H) (n : ℕ) :
    action x T n = T (x n) := rfl

/-- The original rank-one coefficient sum is an actual bounded complex-linear operator functional. -/
def coefficient (x y : VectorSequence H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ y).comp (action x)

/-- The actual infinite matrix-coefficient series is summable, rather than a chosen trace model. -/
theorem coefficient_summable (x y : VectorSequence H) (T : H →L[ℂ] H) :
    Summable (fun n : ℕ => ⟪y n, T (x n)⟫_ℂ) := by
  simpa only [diagonal_apply] using (lp.summable_inner y (diagonal T x))

/-- The actual bounded functional equals the full original rank-one matrix-coefficient series. -/
theorem coefficient_apply (x y : VectorSequence H) (T : H →L[ℂ] H) :
    coefficient x y T = ∑' n : ℕ, ⟪y n, T (x n)⟫_ℂ := by
  change ⟪y, diagonal T x⟫_ℂ = _
  exact (lp.inner_eq_tsum y (diagonal T x)).trans (tsum_congr (fun n => rfl))

/-- The infinite-sum coefficient has the genuine finite source norm bound. -/
theorem coefficient_bound (x y : VectorSequence H) (T : H →L[ℂ] H) :
    ‖coefficient x y T‖ ≤ ‖y‖ * ‖x‖ * ‖T‖ := by
  change ‖⟪y, diagonal T x⟫_ℂ‖ ≤ _
  exact (norm_inner_le_norm y (diagonal T x)).trans
    ((mul_le_mul_of_nonneg_left (action_norm_le x T) (norm_nonneg y)).trans_eq (mul_assoc _ _ _).symm)

end OperatorUltraweak
