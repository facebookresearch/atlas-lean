/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Ising.PressureBCIndep
import Code.Ising.MonomialDisorder

open scoped BigOperators
open Finset

namespace StatMech.Ising

noncomputable section


structure RectangularPrismSite (m n h : Nat) where
  x : Fin m
  y : Fin n
  z : Fin (2 * h + 1)
  deriving DecidableEq, Fintype

abbrev RectangularPrismConfig (m n h : Nat) :=
  ConfigSpace (RectangularPrismSite m n h)


def rectangularPrismSpin {m n h : Nat}
    (sigma : RectangularPrismConfig m n h)
    (x : Fin m) (y : Fin n) (z : Fin (2 * h + 1)) : Real :=
  spin sigma ⟨x, y, z⟩


def rectangularPrismInternalInteraction {m n h : Nat}
    (sigma : RectangularPrismConfig m n h) : Real :=
  (∑ x : Fin (m - 1), ∑ y : Fin n, ∑ z : Fin (2 * h + 1),
      rectangularPrismSpin sigma
        ⟨x.val, by omega⟩ y z *
      rectangularPrismSpin sigma
        ⟨x.val + 1, by omega⟩ y z) +
  (∑ x : Fin m, ∑ y : Fin (n - 1), ∑ z : Fin (2 * h + 1),
      rectangularPrismSpin sigma x
        ⟨y.val, by omega⟩ z *
      rectangularPrismSpin sigma x
        ⟨y.val + 1, by omega⟩ z) +
  (∑ x : Fin m, ∑ y : Fin n, ∑ z : Fin (2 * h),
      rectangularPrismSpin sigma x y
        ⟨z.val, by omega⟩ *
      rectangularPrismSpin sigma x y
        ⟨z.val + 1, by omega⟩)


def rectangularPrismBoundaryDegree {m n h : Nat}
    (v : RectangularPrismSite m n h) : Nat :=
  (if v.x.val = 0 then 1 else 0) +
  (if v.x.val + 1 = m then 1 else 0) +
  (if v.y.val = 0 then 1 else 0) +
  (if v.y.val + 1 = n then 1 else 0) +
  (if v.z.val = 0 then 1 else 0) +
  (if v.z.val + 1 = 2 * h + 1 then 1 else 0)


def rectangularPrismPlusBoundaryInteraction {m n h : Nat}
    (sigma : RectangularPrismConfig m n h) : Real :=
  ∑ v : RectangularPrismSite m n h,
    rectangularPrismBoundaryDegree v * spin sigma v


def rectangularPrismPlusEnergy (J : Real) {m n h : Nat}
    (sigma : RectangularPrismConfig m n h) : Real :=
  -J * (rectangularPrismInternalInteraction sigma +
    rectangularPrismPlusBoundaryInteraction sigma)



def rectangularPrismInterfaceInteraction {m n h : Nat}
    (sigma : RectangularPrismConfig m n h) : Real :=
  if hh : 0 < h then
    ∑ x : Fin m, ∑ y : Fin n,
      rectangularPrismSpin sigma x y ⟨h, by omega⟩ *
        rectangularPrismSpin sigma x y ⟨h + 1, by omega⟩
  else 0



def rectangularPrismTwistedEnergy (J : Real) {m n h : Nat}
    (sigma : RectangularPrismConfig m n h) : Real :=
  rectangularPrismPlusEnergy J sigma +
    2 * J * rectangularPrismInterfaceInteraction sigma


def rectangularPrismPlusPartition
    (J beta : Real) (m n h : Nat) : Real :=
  Z beta (rectangularPrismPlusEnergy J : RectangularPrismConfig m n h -> Real)


def rectangularPrismTwistedPartition
    (J beta : Real) (m n h : Nat) : Real :=
  Z beta (rectangularPrismTwistedEnergy J : RectangularPrismConfig m n h -> Real)



def rectangularDobrushinFreeEnergy
    (J beta : Real) (m n h : Nat) : Real :=
  Real.log (rectangularPrismPlusPartition J beta m n h) -
    Real.log (rectangularPrismTwistedPartition J beta m n h)


def rectangularDobrushinArray
    (J beta : Real) (m n : Nat) : Real :=
  rectangularDobrushinFreeEnergy J beta m n (max m n)



abbrev RectangularPrismInteraction (m n h : Nat) :=
  (Fin (m - 1) × Fin n × Fin (2 * h + 1)) ⊕
    ((Fin m × Fin (n - 1) × Fin (2 * h + 1)) ⊕
      ((Fin m × Fin n × Fin (2 * h)) ⊕ RectangularPrismSite m n h))

local instance rectangularPrismInteractionDecidableEq (m n h : Nat) :
    DecidableEq (RectangularPrismInteraction m n h) := Classical.decEq _


def rectangularPrismInteractionMonomial {m n h : Nat} :
    RectangularPrismInteraction m n h ->
      RectangularPrismConfig m n h -> Real
  | .inl q, sigma =>
      rectangularPrismSpin sigma ⟨q.1.val, by omega⟩ q.2.1 q.2.2 *
        rectangularPrismSpin sigma ⟨q.1.val + 1, by omega⟩ q.2.1 q.2.2
  | .inr (.inl q), sigma =>
      rectangularPrismSpin sigma q.1 ⟨q.2.1.val, by omega⟩ q.2.2 *
        rectangularPrismSpin sigma q.1 ⟨q.2.1.val + 1, by omega⟩ q.2.2
  | .inr (.inr (.inl q)), sigma =>
      rectangularPrismSpin sigma q.1 q.2.1 ⟨q.2.2.val, by omega⟩ *
        rectangularPrismSpin sigma q.1 q.2.1 ⟨q.2.2.val + 1, by omega⟩
  | .inr (.inr (.inr v)), sigma => spin sigma v


def rectangularPrismInteractionCoupling
    (J beta : Real) {m n h : Nat} :
    RectangularPrismInteraction m n h -> Real
  | .inl _ => beta * J
  | .inr (.inl _) => beta * J
  | .inr (.inr (.inl _)) => beta * J
  | .inr (.inr (.inr v)) => beta * J * rectangularPrismBoundaryDegree v


noncomputable def rectangularPrismDisorderSheet (m n h : Nat) :
    Finset (RectangularPrismInteraction m n h) := by
  classical
  exact Finset.univ.filter fun q => match q with
    | .inr (.inr (.inl z)) => z.2.2.val = h
    | _ => false

theorem rectangularPrismInteractionMonomial_isSpinMonomial
    {m n h : Nat} (q : RectangularPrismInteraction m n h) :
    IsSpinMonomial (rectangularPrismInteractionMonomial q) := by
  rcases q with q | q
  · exact (isSpinMonomial_spin _).mul (isSpinMonomial_spin _)
  · rcases q with q | q
    · exact (isSpinMonomial_spin _).mul (isSpinMonomial_spin _)
    · rcases q with q | v
      · exact (isSpinMonomial_spin _).mul (isSpinMonomial_spin _)
      · exact isSpinMonomial_spin v

theorem rectangularPrismInteractionMonomial_eq_one_or_neg_one
    {m n h : Nat} (q : RectangularPrismInteraction m n h)
    (sigma : RectangularPrismConfig m n h) :
    rectangularPrismInteractionMonomial q sigma = 1 ∨
      rectangularPrismInteractionMonomial q sigma = -1 := by
  have mul_pm {a b : Real} (ha : a = 1 ∨ a = -1)
      (hb : b = 1 ∨ b = -1) : a * b = 1 ∨ a * b = -1 := by
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      rw [ha, hb] <;> norm_num
  rcases q with q | q
  · simp only [rectangularPrismInteractionMonomial, rectangularPrismSpin]
    exact mul_pm (spin_eq_pm sigma _) (spin_eq_pm sigma _)
  · rcases q with q | q
    · simp only [rectangularPrismInteractionMonomial, rectangularPrismSpin]
      exact mul_pm (spin_eq_pm sigma _) (spin_eq_pm sigma _)
    · rcases q with q | v
      · simp only [rectangularPrismInteractionMonomial, rectangularPrismSpin]
        exact mul_pm (spin_eq_pm sigma _) (spin_eq_pm sigma _)
      · exact spin_eq_pm sigma v

theorem rectangularPrismInteractionCoupling_nonneg
    {J beta : Real} (hJ : 0 <= J) (hbeta : 0 <= beta)
    {m n h : Nat} (q : RectangularPrismInteraction m n h) :
    0 <= rectangularPrismInteractionCoupling J beta q := by
  rcases q with q | q
  · exact mul_nonneg hbeta hJ
  · rcases q with q | q
    · exact mul_nonneg hbeta hJ
    · rcases q with q | v
      · exact mul_nonneg hbeta hJ
      · exact mul_nonneg (mul_nonneg hbeta hJ) (Nat.cast_nonneg _)

theorem sum_rectangularPrismInteraction_eq
    (J beta : Real) {m n h : Nat}
    (sigma : RectangularPrismConfig m n h) :
    (∑ q : RectangularPrismInteraction m n h,
        rectangularPrismInteractionCoupling J beta q *
          rectangularPrismInteractionMonomial q sigma) =
      beta * J * (rectangularPrismInternalInteraction sigma +
        rectangularPrismPlusBoundaryInteraction sigma) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [rectangularPrismInteractionCoupling,
    rectangularPrismInteractionMonomial]
  simp_rw [Fintype.sum_prod_type]
  unfold rectangularPrismInternalInteraction
    rectangularPrismPlusBoundaryInteraction rectangularPrismSpin
  simp_rw [← Finset.mul_sum]
  have hboundary :
      (∑ v : RectangularPrismSite m n h,
          beta * J * (rectangularPrismBoundaryDegree v : Real) * spin sigma v) =
        beta * J * ∑ v : RectangularPrismSite m n h,
          (rectangularPrismBoundaryDegree v : Real) * spin sigma v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hboundary]
  ring

theorem sum_rectangularPrismDisorderSheet_eq
    (J beta : Real) {m n h : Nat}
    (sigma : RectangularPrismConfig m n h) :
    (∑ q ∈ rectangularPrismDisorderSheet m n h,
        rectangularPrismInteractionCoupling J beta q *
          rectangularPrismInteractionMonomial q sigma) =
      beta * J * rectangularPrismInterfaceInteraction sigma := by
  classical
  rw [rectangularPrismDisorderSheet, Finset.sum_filter]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [rectangularPrismInteractionCoupling,
    rectangularPrismInteractionMonomial, Bool.false_eq_true, ↓reduceIte]
  rw [rectangularPrismInterfaceInteraction]
  split_ifs with hh
  · simp_rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const_zero, add_zero, zero_add]
    have hz (x : Fin m) (y : Fin n) :
        (∑ z : Fin (2 * h),
          if z.val = h then
            beta * J * (rectangularPrismSpin sigma x y ⟨z.val, by omega⟩ *
              rectangularPrismSpin sigma x y ⟨z.val + 1, by omega⟩)
          else 0) =
        beta * J * (rectangularPrismSpin sigma x y ⟨h, by omega⟩ *
          rectangularPrismSpin sigma x y ⟨h + 1, by omega⟩) := by
      change (∑ z ∈ (Finset.univ : Finset (Fin (2 * h))),
          if z.val = h then
            beta * J * (rectangularPrismSpin sigma x y ⟨z.val, by omega⟩ *
              rectangularPrismSpin sigma x y ⟨z.val + 1, by omega⟩)
          else 0) = _
      let z0 : Fin (2 * h) := ⟨h, by omega⟩
      have hiff (z : Fin (2 * h)) : z.val = h ↔ z = z0 := by
        constructor
        · intro hz_eq
          apply Fin.ext
          simpa [z0] using hz_eq
        · intro hz_eq
          subst z
          rfl
      simp_rw [hiff]
      simp [z0]
    simp_rw [hz]
    simp_rw [← Finset.mul_sum]
  · have hh0 : h = 0 := Nat.eq_zero_of_not_pos hh
    subst h
    simp_rw [Fintype.sum_prod_type]
    simp



theorem rectangularPrismPlusPartition_eq_monomialInteractionPartition
    (J beta : Real) (m n h : Nat) :
    rectangularPrismPlusPartition J beta m n h =
      monomialInteractionPartition
        (rectangularPrismInteractionCoupling J beta :
          RectangularPrismInteraction m n h -> Real)
        (rectangularPrismInteractionMonomial :
          RectangularPrismInteraction m n h ->
            RectangularPrismConfig m n h -> Real) := by
  unfold rectangularPrismPlusPartition monomialInteractionPartition Z
  apply Finset.sum_congr rfl
  intro sigma _
  congr 1
  rw [sum_rectangularPrismInteraction_eq]
  unfold rectangularPrismPlusEnergy
  ring



theorem rectangularPrismTwistedPartition_eq_monomialInteractionPartition
    (J beta : Real) (m n h : Nat) :
    rectangularPrismTwistedPartition J beta m n h =
      monomialInteractionPartition
        (reverseInteractionCoupling
          (rectangularPrismInteractionCoupling J beta :
            RectangularPrismInteraction m n h -> Real)
          (rectangularPrismDisorderSheet m n h))
        (rectangularPrismInteractionMonomial :
          RectangularPrismInteraction m n h ->
            RectangularPrismConfig m n h -> Real) := by
  unfold rectangularPrismTwistedPartition monomialInteractionPartition Z
  apply Finset.sum_congr rfl
  intro sigma _
  congr 1
  rw [sum_reverseInteractionCoupling,
    sum_rectangularPrismInteraction_eq,
    sum_rectangularPrismDisorderSheet_eq]
  unfold rectangularPrismTwistedEnergy rectangularPrismPlusEnergy
  ring



theorem rectangularPrismTwistedPartition_le_plusPartition
    {J beta : Real} (hJ : 0 <= J) (hbeta : 0 <= beta)
    (m n h : Nat) :
    rectangularPrismTwistedPartition J beta m n h <=
      rectangularPrismPlusPartition J beta m n h := by
  rw [rectangularPrismTwistedPartition_eq_monomialInteractionPartition,
    rectangularPrismPlusPartition_eq_monomialInteractionPartition]
  exact monomialInteractionPartition_reverse_le
    (V := RectangularPrismSite m n h)
    (P := RectangularPrismInteraction m n h)
    (rectangularPrismInteractionCoupling J beta)
    rectangularPrismInteractionMonomial
    (rectangularPrismInteractionCoupling_nonneg hJ hbeta)
    rectangularPrismInteractionMonomial_isSpinMonomial
    rectangularPrismInteractionMonomial_eq_one_or_neg_one
    (rectangularPrismDisorderSheet m n h)


theorem rectangularDobrushinFreeEnergy_nonneg
    {J beta : Real} (hJ : 0 <= J) (hbeta : 0 <= beta)
    (m n h : Nat) :
    0 <= rectangularDobrushinFreeEnergy J beta m n h := by
  unfold rectangularDobrushinFreeEnergy
  have htwist_pos : 0 < rectangularPrismTwistedPartition J beta m n h :=
    Z_pos _ _
  have hle := Real.log_le_log htwist_pos
    (rectangularPrismTwistedPartition_le_plusPartition hJ hbeta m n h)
  linarith

theorem rectangularDobrushinArray_nonneg
    {J beta : Real} (hJ : 0 <= J) (hbeta : 0 <= beta)
    (m n : Nat) :
    0 <= rectangularDobrushinArray J beta m n :=
  rectangularDobrushinFreeEnergy_nonneg hJ hbeta m n (max m n)


theorem rectangularPrismInterfaceSummand_abs_le_one
    {m n h : Nat} (sigma : RectangularPrismConfig m n h)
    (hh : 0 < h) (x : Fin m) (y : Fin n) :
    |rectangularPrismSpin sigma x y ⟨h, by omega⟩ *
        rectangularPrismSpin sigma x y ⟨h + 1, by omega⟩| <= 1 := by
  rw [abs_mul]
  exact mul_le_one₀ (abs_spin_le_one _ _) (abs_nonneg _)
    (abs_spin_le_one _ _)


theorem rectangularPrismInterfaceInteraction_abs_le
    {m n h : Nat} (sigma : RectangularPrismConfig m n h) :
    |rectangularPrismInterfaceInteraction sigma| <= (m : Real) * n := by
  rw [rectangularPrismInterfaceInteraction]
  split_ifs with hh
  · calc
      |∑ x : Fin m, ∑ y : Fin n,
          rectangularPrismSpin sigma x y ⟨h, by omega⟩ *
            rectangularPrismSpin sigma x y ⟨h + 1, by omega⟩| <=
          ∑ x : Fin m, |∑ y : Fin n,
            rectangularPrismSpin sigma x y ⟨h, by omega⟩ *
              rectangularPrismSpin sigma x y ⟨h + 1, by omega⟩| := by
        simpa using Finset.abs_sum_le_sum_abs
          (fun x : Fin m => ∑ y : Fin n,
            rectangularPrismSpin sigma x y ⟨h, by omega⟩ *
              rectangularPrismSpin sigma x y ⟨h + 1, by omega⟩)
          Finset.univ
      _ <= ∑ x : Fin m, ∑ y : Fin n,
          |rectangularPrismSpin sigma x y ⟨h, by omega⟩ *
            rectangularPrismSpin sigma x y ⟨h + 1, by omega⟩| := by
        apply Finset.sum_le_sum
        intro x _
        simpa using Finset.abs_sum_le_sum_abs
          (fun y : Fin n =>
            rectangularPrismSpin sigma x y ⟨h, by omega⟩ *
              rectangularPrismSpin sigma x y ⟨h + 1, by omega⟩)
          Finset.univ
      _ <= ∑ _x : Fin m, ∑ _y : Fin n, (1 : Real) := by
        apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro y _
        exact rectangularPrismInterfaceSummand_abs_le_one sigma hh x y
      _ = (m : Real) * n := by simp
  · simpa only [abs_zero] using
      mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)



theorem rectangularPrism_energy_sub_abs_le
    (J : Real) {m n h : Nat} (sigma : RectangularPrismConfig m n h) :
    |rectangularPrismPlusEnergy J sigma -
        rectangularPrismTwistedEnergy J sigma| <=
      2 * |J| * ((m : Real) * n) := by
  rw [rectangularPrismTwistedEnergy]
  have hI := rectangularPrismInterfaceInteraction_abs_le sigma
  calc
    |rectangularPrismPlusEnergy J sigma -
        (rectangularPrismPlusEnergy J sigma +
          2 * J * rectangularPrismInterfaceInteraction sigma)| =
        2 * |J| * |rectangularPrismInterfaceInteraction sigma| := by
      rw [show rectangularPrismPlusEnergy J sigma -
          (rectangularPrismPlusEnergy J sigma +
            2 * J * rectangularPrismInterfaceInteraction sigma) =
          -(2 * J * rectangularPrismInterfaceInteraction sigma) by ring,
        abs_neg, abs_mul, abs_mul]
      norm_num
    _ <= 2 * |J| * ((m : Real) * n) := by gcongr



theorem rectangularDobrushinFreeEnergy_abs_le
    (J beta : Real) (m n h : Nat) :
    |rectangularDobrushinFreeEnergy J beta m n h| <=
      2 * |beta| * |J| * ((m : Real) * n) := by
  have hdist := logZ_dist_le beta
    (rectangularPrismPlusEnergy J : RectangularPrismConfig m n h -> Real)
    (rectangularPrismTwistedEnergy J : RectangularPrismConfig m n h -> Real)
    (2 * |J| * ((m : Real) * n))
    (rectangularPrism_energy_sub_abs_le J)
  simp only [rectangularDobrushinFreeEnergy, rectangularPrismPlusPartition,
    rectangularPrismTwistedPartition]
  convert hdist using 1
  ring



theorem rectangularDobrushinArray_le_area
    (J beta : Real) (m n : Nat) :
    rectangularDobrushinArray J beta m n <=
      (2 * |beta| * |J|) * (m : Real) * n := by
  exact le_trans (le_abs_self _) (by
    simpa [rectangularDobrushinArray, mul_assoc] using
      rectangularDobrushinFreeEnergy_abs_le J beta m n (max m n))

end

end StatMech.Ising
