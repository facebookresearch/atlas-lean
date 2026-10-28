/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Covariance of both short-times-short output sums under the actual local action.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortProductCovariance

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative

noncomputable def conwayShortShortProduct (x y : GriessShortIndex → ℝ)
    (u : GriessShortIndex) : ℝ :=
  ∑ r, ∑ s, if (griessShortQ r * griessShortQ s).base = (griessShortQ u).base then
    qSign (toAdd (griessShortQ r * griessShortQ s).coeff) * x r * y s else 0

theorem conwayShortShortProduct_covariant (f : localFiberSubgroup)
    (x y : GriessShortIndex → ℝ) :
    localShortRepresentation f (conwayShortShortProduct x y) =
      conwayShortShortProduct (localShortRepresentation f x) (localShortRepresentation f y) := by
  funext u
  obtain ⟨u, rfl⟩ := (griessShortPermutation f.val.2).surjective u
  change localShortOperator f (conwayShortShortProduct x y)
    (griessShortPermutation f.val.2 u) = _
  rw [localShortOperator_image]
  unfold conwayShortShortProduct
  conv_rhs => rw [← Equiv.sum_comp (griessShortPermutation f.val.2)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  conv_rhs => rw [← Equiv.sum_comp (griessShortPermutation f.val.2)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [← griessShortQ_product_base_covariant f]
  by_cases h : (griessShortQ r * griessShortQ s).base = (griessShortQ u).base
  · simp only [h, ite_true]
    change _ = qSign _ * localShortOperator f x (griessShortPermutation f.val.2 r) *
      localShortOperator f y (griessShortPermutation f.val.2 s)
    rw [localShortOperator_image, localShortOperator_image]
    have hp := griessShortQ_product_phase_covariant f r s u h
    calc
      _ = (qSign (toAdd (griessShortQ r * griessShortQ s).coeff) *
          qSign (localShortPhase f u)) * x r * y s := by ring
      _ = _ := by rw [hp]; ring
  · simp [h]

noncomputable def conwayShortShortMatrix (x y : GriessShortIndex → ℝ) :
    Matrix (Fin 24) (Fin 24) ℝ :=
  ∑ r, ∑ s, if (griessShortQ r * griessShortQ s).base = 1 then
    (qSign (toAdd (griessShortQ r * griessShortQ s).coeff) * x r * y s) •
      Matrix.vecMulVec (griessShortVector r) (griessShortVector r) else 0

theorem conwayShortShortMatrix_apply (x y : GriessShortIndex → ℝ) (i j : Fin 24) :
    conwayShortShortMatrix x y i j =
      ∑ r, ∑ s, if (griessShortQ r * griessShortQ s).base = 1 then
        qSign (toAdd (griessShortQ r * griessShortQ s).coeff) * x r * y s *
          griessShortVector r i * griessShortVector r j else 0 := by
  simp only [conwayShortShortMatrix, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  split <;> simp [Matrix.smul_apply, Matrix.vecMulVec, mul_assoc]

theorem conwayShortShortMatrix_covariant (f : localFiberSubgroup)
    (x y : GriessShortIndex → ℝ) :
    conwayMatrixAction f.val.2 (conwayShortShortMatrix x y) =
      conwayShortShortMatrix (localShortRepresentation f x) (localShortRepresentation f y) := by
  unfold conwayShortShortMatrix
  rw [map_sum]
  conv_rhs => rw [← Equiv.sum_comp (griessShortPermutation f.val.2)]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_sum]
  conv_rhs => rw [← Equiv.sum_comp (griessShortPermutation f.val.2)]
  apply Finset.sum_congr rfl
  intro s _
  simp only [← griessShortQ_product_base_one_covariant f]
  by_cases h : (griessShortQ r * griessShortQ s).base = 1
  · simp only [h, ite_true, map_smul, conwayMatrixAction_short_outer]
    change _ = (qSign _ * localShortOperator f x (griessShortPermutation f.val.2 r) *
      localShortOperator f y (griessShortPermutation f.val.2 s)) • _
    rw [localShortOperator_image, localShortOperator_image]
    apply congrArg (fun c : ℝ => c •
      Matrix.vecMulVec (griessShortVector (griessShortPermutation f.val.2 r))
        (griessShortVector (griessShortPermutation f.val.2 r)))
    rw [griessShortQ_product_phase_one_covariant f r s h]
    ring
  · simp [h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
