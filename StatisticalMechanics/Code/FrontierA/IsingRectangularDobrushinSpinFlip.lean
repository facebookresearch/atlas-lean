/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingRectangularDobrushin

open scoped BigOperators
open Finset

namespace StatMech.Ising

noncomputable section

local instance rectangularPrismInteractionDecidableEq' (m n h : Nat) :
    DecidableEq (RectangularPrismInteraction m n h) := Classical.decEq _


def rectangularPrismUpperHalfFlip {m n h : Nat}
    (sigma : RectangularPrismConfig m n h) :
    RectangularPrismConfig m n h :=
  fun v => if h < v.z.val then !sigma v else sigma v


def rectangularPrismUpperHalfFlipEquiv (m n h : Nat) :
    RectangularPrismConfig m n h ≃ RectangularPrismConfig m n h where
  toFun := rectangularPrismUpperHalfFlip
  invFun := rectangularPrismUpperHalfFlip
  left_inv sigma := by
    funext v
    by_cases hz : h < v.z.val <;>
      simp [rectangularPrismUpperHalfFlip, hz]
  right_inv sigma := by
    funext v
    by_cases hz : h < v.z.val <;>
      simp [rectangularPrismUpperHalfFlip, hz]

theorem rectangularPrismSpin_upperHalfFlip {m n h : Nat}
    (sigma : RectangularPrismConfig m n h)
    (x : Fin m) (y : Fin n) (z : Fin (2 * h + 1)) :
    rectangularPrismSpin (rectangularPrismUpperHalfFlip sigma) x y z =
      if h < z.val then -rectangularPrismSpin sigma x y z
      else rectangularPrismSpin sigma x y z := by
  by_cases hz : h < z.val <;>
    by_cases hs : sigma ⟨x, y, z⟩ <;>
      simp [rectangularPrismSpin, rectangularPrismUpperHalfFlip, spin, hz, hs]




def rectangularPrismDobrushinCoupling
    (J beta : Real) {m n h : Nat} :
    RectangularPrismInteraction m n h -> Real
  | .inl _ => beta * J
  | .inr (.inl _) => beta * J
  | .inr (.inr (.inl _)) => beta * J
  | .inr (.inr (.inr v)) =>
      (if h < v.z.val then -1 else 1) *
        (beta * J * rectangularPrismBoundaryDegree v)

@[simp] theorem rectangularPrismDisorderSheet_not_mem_x
    {m n h : Nat} (q : Fin (m - 1) × Fin n × Fin (2 * h + 1)) :
    Sum.inl q ∉ rectangularPrismDisorderSheet m n h := by
  simp [rectangularPrismDisorderSheet]

@[simp] theorem rectangularPrismDisorderSheet_not_mem_y
    {m n h : Nat} (q : Fin m × Fin (n - 1) × Fin (2 * h + 1)) :
    Sum.inr (Sum.inl q) ∉ rectangularPrismDisorderSheet m n h := by
  simp [rectangularPrismDisorderSheet]

@[simp] theorem rectangularPrismDisorderSheet_mem_z_iff
    {m n h : Nat} (q : Fin m × Fin n × Fin (2 * h)) :
    Sum.inr (Sum.inr (Sum.inl q)) ∈
        rectangularPrismDisorderSheet m n h <-> q.2.2.val = h := by
  simp [rectangularPrismDisorderSheet]

@[simp] theorem rectangularPrismDisorderSheet_not_mem_boundary
    {m n h : Nat} (v : RectangularPrismSite m n h) :
    Sum.inr (Sum.inr (Sum.inr v)) ∉
      rectangularPrismDisorderSheet m n h := by
  simp [rectangularPrismDisorderSheet]



theorem reverseSheet_mul_monomial_upperHalfFlip
    (J beta : Real) {m n h : Nat}
    (q : RectangularPrismInteraction m n h)
    (sigma : RectangularPrismConfig m n h) :
    reverseInteractionCoupling
          (rectangularPrismInteractionCoupling J beta)
          (rectangularPrismDisorderSheet m n h) q *
        rectangularPrismInteractionMonomial q
          (rectangularPrismUpperHalfFlip sigma) =
      rectangularPrismDobrushinCoupling J beta q *
        rectangularPrismInteractionMonomial q sigma := by
  rcases q with q | q
  · rcases q with ⟨x, y, z⟩
    by_cases hz : h < z.val <;>
      simp [reverseInteractionCoupling,
        rectangularPrismInteractionCoupling,
        rectangularPrismDobrushinCoupling,
        rectangularPrismInteractionMonomial,
        rectangularPrismSpin_upperHalfFlip, hz]
  · rcases q with q | q
    · rcases q with ⟨x, y, z⟩
      by_cases hz : h < z.val <;>
        simp [reverseInteractionCoupling,
          rectangularPrismInteractionCoupling,
          rectangularPrismDobrushinCoupling,
          rectangularPrismInteractionMonomial,
          rectangularPrismSpin_upperHalfFlip, hz]
    · rcases q with q | v
      · rcases q with ⟨x, y, z⟩
        by_cases hz : z.val = h
        · simp [reverseInteractionCoupling,
            rectangularPrismInteractionCoupling,
            rectangularPrismDobrushinCoupling,
            rectangularPrismInteractionMonomial,
            rectangularPrismSpin_upperHalfFlip, hz]
        · by_cases hbelow : z.val < h
          · have hz0 : ¬ h < z.val := by omega
            have hz1 : ¬ h < z.val + 1 := by omega
            simp [reverseInteractionCoupling,
              rectangularPrismInteractionCoupling,
              rectangularPrismDobrushinCoupling,
              rectangularPrismInteractionMonomial,
              rectangularPrismSpin_upperHalfFlip, hz, hz0, hz1]
          · have hz0 : h < z.val := by omega
            have hz1 : h < z.val + 1 := by omega
            simp [reverseInteractionCoupling,
              rectangularPrismInteractionCoupling,
              rectangularPrismDobrushinCoupling,
              rectangularPrismInteractionMonomial,
              rectangularPrismSpin_upperHalfFlip, hz, hz0, hz1]
      · by_cases hz : h < v.z.val
        · by_cases hs : sigma v <;>
            simp [reverseInteractionCoupling,
              rectangularPrismInteractionCoupling,
              rectangularPrismDobrushinCoupling,
              rectangularPrismInteractionMonomial,
              rectangularPrismUpperHalfFlip, spin, hz, hs]
        · by_cases hs : sigma v <;>
            simp [reverseInteractionCoupling,
              rectangularPrismInteractionCoupling,
              rectangularPrismDobrushinCoupling,
              rectangularPrismInteractionMonomial,
              rectangularPrismUpperHalfFlip, spin, hz, hs]


def rectangularPrismDobrushinPartition
    (J beta : Real) (m n h : Nat) : Real :=
  monomialInteractionPartition
    (rectangularPrismDobrushinCoupling J beta :
      RectangularPrismInteraction m n h -> Real)
    (rectangularPrismInteractionMonomial :
      RectangularPrismInteraction m n h ->
        RectangularPrismConfig m n h -> Real)



theorem rectangularPrismTwistedPartition_eq_dobrushinPartition
    (J beta : Real) (m n h : Nat) :
    rectangularPrismTwistedPartition J beta m n h =
      rectangularPrismDobrushinPartition J beta m n h := by
  rw [rectangularPrismTwistedPartition_eq_monomialInteractionPartition]
  unfold monomialInteractionPartition rectangularPrismDobrushinPartition
  rw [← (rectangularPrismUpperHalfFlipEquiv m n h).sum_comp]
  apply Finset.sum_congr rfl
  intro sigma _
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  exact reverseSheet_mul_monomial_upperHalfFlip J beta q sigma



theorem rectangularDobrushinFreeEnergy_eq_boundaryRatio
    (J beta : Real) (m n h : Nat) :
    rectangularDobrushinFreeEnergy J beta m n h =
      Real.log (rectangularPrismPlusPartition J beta m n h) -
        Real.log (rectangularPrismDobrushinPartition J beta m n h) := by
  rw [rectangularDobrushinFreeEnergy,
    rectangularPrismTwistedPartition_eq_dobrushinPartition]

end

end StatMech.Ising
