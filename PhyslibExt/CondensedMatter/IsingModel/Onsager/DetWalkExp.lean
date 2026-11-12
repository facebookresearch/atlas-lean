/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.DetLoopExpansion
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanLoop

/-!

# Determinants as walk exponentials

The Kac-Ward determinant as the exponential of a closed-walk series, its square root, and masked
matrices.

## i. Overview

Combining the trace-series identity with the walk expansion of `tr (Λ ^ n)` gives
`det (1 - Λ) = exp (-∑ₙ (∑_{closed walks of length n + 1} weight) / (n + 1))`. The function
`ons_detWalkRoot Λ` is the exponential of half that series, so it is a canonical square root of
`det (1 - Λ)`. Masking a set of states (setting all entries in their rows and columns to zero)
removes exactly the closed walks that meet them.

## ii. Key results

- `ons_detWalkRoot` : the square root `exp (-(walk series) / 2)` of `det (1 - Λ)`
- `ons_maskMatrix` : the matrix with the rows and columns of forbidden states set to zero
- `ons_det_eq_walk_exp` : `det (1 - Λ)` as the exponential of the closed-walk series
- `ons_detWalkRoot_sq` : `ons_detWalkRoot Λ ^ 2 = det (1 - Λ)`

## iii. Table of contents

- A. The walk-series square root
- B. Masked matrices
- C. Determinant identities

## iv. References

- M. Kac and J. C. Ward, *A combinatorial solution of the two-dimensional Ising model*, Phys. Rev.
  88 (1952) 1332-1337
- S. Sherman, *Combinatorial aspects of the Ising model for ferromagnetism. I. A conjecture of
  Feynman on paths and graphs*, J. Math. Phys. 1 (1960) 202-217

-/

@[expose] public section

namespace StatMech.Onsager

open BigOperators

/-! ## A. The walk-series square root -/

/-- The walk-series square root of `det (1 - Λ)`: the exponential of minus one half of
`∑ₙ (∑ over closed walks of length n + 1 of their weight) / (n + 1)`. -/
noncomputable def ons_detWalkRoot {E : Type*} [Fintype E] [DecidableEq E]
    (Λ : Matrix E E ℂ) : ℂ :=
  Complex.exp (-(∑' n : ℕ,
    (∑ v : Fin (n + 1) → E,
      ∏ k : Fin (n + 1), Λ (v k) (v (k + 1))) / (n + 1)) / 2)

/-! ## B. Masked matrices -/

/-- The matrix `Λ` with every row and column indexed by a state of `forbidden` set to zero. -/
def ons_maskMatrix {E : Type*} [DecidableEq E]
    (forbidden : Finset E) (Λ : Matrix E E ℂ) : Matrix E E ℂ :=
  fun i j => if i ∈ forbidden ∨ j ∈ forbidden then 0 else Λ i j

lemma ons_maskMatrix_union {E : Type*} [DecidableEq E]
    (S T : Finset E) (Λ : Matrix E E ℂ) :
    ons_maskMatrix S (ons_maskMatrix T Λ) =
      ons_maskMatrix (S ∪ T) Λ := by
  ext i j
  simp only [ons_maskMatrix, Finset.mem_union]
  aesop

lemma ons_loopWeight_maskMatrix {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n] (forbidden : Finset E) (Λ : Matrix E E ℂ)
    (d : Fin n → E) :
    ons_loopWeight (ons_maskMatrix forbidden Λ) d =
      if ∃ k, d k ∈ forbidden then 0 else ons_loopWeight Λ d := by
  by_cases hhit : ∃ k, d k ∈ forbidden
  · rw [ite_eq_left hhit]
    obtain ⟨k, hk⟩ := hhit
    unfold ons_loopWeight
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp [ons_maskMatrix, hk]
  · rw [ite_eq_right hhit]
    unfold ons_loopWeight
    apply Finset.prod_congr rfl
    intro k _
    have hk : d k ∉ forbidden := fun h => hhit ⟨k, h⟩
    have hk1 : d (k + 1) ∉ forbidden := fun h => hhit ⟨k + 1, h⟩
    simp [ons_maskMatrix, hk, hk1]

lemma ons_loopSum_maskMatrix {E : Type*} [Fintype E] [DecidableEq E]
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

/-! ## C. Determinant identities -/

lemma ons_det_eq_walk_exp {E : Type*} [Fintype E] [DecidableEq E]
    (Λ : Matrix E E ℂ) (hspec : ∀ α ∈ Λ.charpoly.roots, ‖α‖ < 1) :
    (1 - Λ).det
      = Complex.exp (- ∑' n : ℕ,
          (∑ v : Fin (n + 1) → E, ∏ k : Fin (n + 1), Λ (v k) (v (k + 1))) / (n + 1)) := by
  rw [ons_det_loop_expansion Λ hspec]
  refine congrArg Complex.exp (congrArg Neg.neg (tsum_congr (fun n => ?_)))
  exact congrArg (· / ((n : ℂ) + 1)) (ons_trace_pow_eq_walk_sum Λ (n + 1) (Nat.succ_pos n))

lemma ons_detWalkRoot_sq {E : Type*} [Fintype E] [DecidableEq E]
    (Λ : Matrix E E ℂ) (hspec : ∀ α ∈ Λ.charpoly.roots, ‖α‖ < 1) :
    ons_detWalkRoot Λ ^ 2 = (1 - Λ).det := by
  rw [ons_det_eq_walk_exp Λ hspec]
  unfold ons_detWalkRoot
  rw [pow_two, ← Complex.exp_add]
  congr 1
  ring

@[simp] lemma ons_detWalkRoot_zero {E : Type*} [Fintype E] [DecidableEq E] :
    ons_detWalkRoot (0 : Matrix E E ℂ) = 1 := by
  unfold ons_detWalkRoot
  simp

end StatMech.Onsager
