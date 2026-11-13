/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.DetLoopExpansion
import Code.Onsager.TracePowWalk
import Code.Onsager.ShermanLoop

namespace StatMech.Onsager

open BigOperators

noncomputable def ons_detWalkRoot {E : Type*} [Fintype E] [DecidableEq E]
    (Λ : Matrix E E ℂ) : ℂ :=
  Complex.exp (-(∑' n : ℕ,
    (∑ v : Fin (n + 1) → E,
      ∏ k : Fin (n + 1), Λ (v k) (v (k + 1))) / (n + 1)) / 2)

def ons_maskMatrix {E : Type*} [DecidableEq E]
    (forbidden : Finset E) (Λ : Matrix E E ℂ) : Matrix E E ℂ :=
  fun i j => if i ∈ forbidden ∨ j ∈ forbidden then 0 else Λ i j

theorem ons_maskMatrix_union {E : Type*} [DecidableEq E]
    (S T : Finset E) (Λ : Matrix E E ℂ) :
    ons_maskMatrix S (ons_maskMatrix T Λ) =
      ons_maskMatrix (S ∪ T) Λ := by
  ext i j
  simp only [ons_maskMatrix, Finset.mem_union]
  aesop

theorem ons_loopWeight_maskMatrix {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n] (forbidden : Finset E) (Λ : Matrix E E ℂ)
    (d : Fin n → E) :
    ons_loopWeight (ons_maskMatrix forbidden Λ) d =
      if ∃ k, d k ∈ forbidden then 0 else ons_loopWeight Λ d := by
  by_cases hhit : ∃ k, d k ∈ forbidden
  · rw [if_pos hhit]
    obtain ⟨k, hk⟩ := hhit
    unfold ons_loopWeight
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp [ons_maskMatrix, hk]
  · rw [if_neg hhit]
    unfold ons_loopWeight
    apply Finset.prod_congr rfl
    intro k _
    have hk : d k ∉ forbidden := fun h => hhit ⟨k, h⟩
    have hk1 : d (k + 1) ∉ forbidden := fun h => hhit ⟨k + 1, h⟩
    simp [ons_maskMatrix, hk, hk1]

theorem ons_loopSum_maskMatrix {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n] (forbidden : Finset E) (Λ : Matrix E E ℂ) :
    (∑ d : Fin n → E, ons_loopWeight (ons_maskMatrix forbidden Λ) d) =
      ∑ d ∈ Finset.univ.filter (fun d : Fin n → E =>
        ¬ ∃ k, d k ∈ forbidden), ons_loopWeight Λ d := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  rw [ons_loopWeight_maskMatrix]
  by_cases hhit : ∃ k, d k ∈ forbidden
  · simp [hhit]
  · simp [hhit]

theorem ons_det_eq_walk_exp {E : Type*} [Fintype E] [DecidableEq E]
    (Λ : Matrix E E ℂ) (hspec : ∀ α ∈ Λ.charpoly.roots, ‖α‖ < 1) :
    (1 - Λ).det
      = Complex.exp (- ∑' n : ℕ,
          (∑ v : Fin (n + 1) → E, ∏ k : Fin (n + 1), Λ (v k) (v (k + 1))) / (n + 1)) := by
  rw [ons_det_loop_expansion Λ hspec]
  refine congrArg Complex.exp (congrArg Neg.neg (tsum_congr (fun n => ?_)))
  exact congrArg (· / ((n : ℂ) + 1)) (ons_trace_pow_eq_walk_sum Λ (n + 1) (Nat.succ_pos n))



theorem ons_detWalkRoot_sq {E : Type*} [Fintype E] [DecidableEq E]
    (Λ : Matrix E E ℂ) (hspec : ∀ α ∈ Λ.charpoly.roots, ‖α‖ < 1) :
    ons_detWalkRoot Λ ^ 2 = (1 - Λ).det := by
  rw [ons_det_eq_walk_exp Λ hspec]
  unfold ons_detWalkRoot
  rw [pow_two, ← Complex.exp_add]
  congr 1
  ring

@[simp] theorem ons_detWalkRoot_zero {E : Type*} [Fintype E] [DecidableEq E] :
    ons_detWalkRoot (0 : Matrix E E ℂ) = 1 := by
  unfold ons_detWalkRoot
  simp

end StatMech.Onsager
