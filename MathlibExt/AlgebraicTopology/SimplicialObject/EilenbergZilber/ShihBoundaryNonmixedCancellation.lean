/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryMixedCancellation
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryDecomposition
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryLeft.Signs
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryRight.Signs
/-!
# Nonmixed active-face cancellation in the Shih boundary

The interior left- and right-boundary faces of the active shuffle block pair
with lower-boundary terms of the preceding bidegree.  Endpoint terms are kept
separate for the subsequent telescoping argument.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

namespace ShihIndex

/-- The upper Shih index obtained by inserting one left position. -/
def leftBoundaryUpperIndex (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (a : Fin (p + 3)) :
    ShihIndex (p + q + m + 1) where
  p := ⟨p + 1, by omega⟩
  q := ⟨q, by
    change q < p + q + m + 1 - (p + 1)
    omega⟩
  shuffle := Shuffle.leftBoundaryShuffle t a

/-- The upper Shih index obtained by inserting one right position. -/
def rightBoundaryUpperIndex (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (b : Fin (q + 2)) :
    ShihIndex (p + q + m + 1) where
  p := ⟨p, by omega⟩
  q := ⟨q + 1, by
    change q + 1 < p + q + m + 1 - p
    omega⟩
  shuffle := Shuffle.rightBoundaryShuffle t b

@[simp]
theorem leftBoundaryUpperIndex_p (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (a : Fin (p + 3)) :
    ((leftBoundaryUpperIndex p q m hm t a).p : ℕ) = p + 1 := rfl

@[simp]
theorem leftBoundaryUpperIndex_q (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (a : Fin (p + 3)) :
    ((leftBoundaryUpperIndex p q m hm t a).q : ℕ) = q := rfl

@[simp]
theorem rightBoundaryUpperIndex_p (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (b : Fin (q + 2)) :
    ((rightBoundaryUpperIndex p q m hm t b).p : ℕ) = p := rfl

@[simp]
theorem rightBoundaryUpperIndex_q (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (b : Fin (q + 2)) :
    ((rightBoundaryUpperIndex p q m hm t b).q : ℕ) = q + 1 := rfl

@[simp]
theorem gap_leftBoundaryUpperIndex (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (a : Fin (p + 3)) :
    (leftBoundaryUpperIndex p q m hm t a).gap = m := by
  simp [leftBoundaryUpperIndex, gap]
  omega

@[simp]
theorem gap_rightBoundaryUpperIndex (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (b : Fin (q + 2)) :
    (rightBoundaryUpperIndex p q m hm t b).gap = m := by
  simp [rightBoundaryUpperIndex, gap]
  omega

/-- The lower face paired with a nonendpoint inserted left position. -/
def leftBoundaryLowerFace (p q m : ℕ) (hm : 0 < m)
    (a : Fin (p + 3)) (_ha : 0 < a.val) : Fin (p + q + m + 2) :=
  ⟨m - 1 + a.val, by
    have haLt := a.isLt
    change a.val < p + 3 at haLt
    change m - 1 + a.val < p + q + m + 2
    omega⟩

/-- The lower face paired with a noninitial inserted right position. -/
def rightBoundaryLowerFace (p q m : ℕ) (b : Fin (q + 2))
    (_hb : 0 < b.val) : Fin (p + q + m + 2) :=
  ⟨m + p + b.val, by
    have hbLt := b.isLt
    omega⟩

/-- The global active face of an inserted left position. -/
def leftBoundaryUpperFace (p q m : ℕ) (t : Shuffle (p + 1) q)
    (a : Fin (p + 3)) :
    Fin (p + q + m + 3) :=
  ⟨m + (Shuffle.leftBoundaryIndex t a).val,
    by
      have haLt := a.isLt
      omega⟩

def rightBoundaryUpperFace (p q m : ℕ) (t : Shuffle (p + 1) q)
    (b : Fin (q + 2)) : Fin (p + q + m + 3) :=
  ⟨m + (Shuffle.rightBoundaryIndex t b).val, by
      have hbLt := b.isLt
      omega⟩

/-- The local left-boundary face, cast to the active block of its upper
Shih index. -/
def leftBoundaryLocalFace (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (a : Fin (p + 3)) :
    Fin ((leftBoundaryUpperIndex p q m hm t a).p + 1 +
      (leftBoundaryUpperIndex p q m hm t a).q + 1) :=
  Fin.cast (by simp [leftBoundaryUpperIndex]) (Shuffle.leftBoundaryIndex t a)

/-- The local right-boundary face, cast to the active block of its upper
Shih index. -/
def rightBoundaryLocalFace (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (b : Fin (q + 2)) :
    Fin ((rightBoundaryUpperIndex p q m hm t b).p + 1 +
      (rightBoundaryUpperIndex p q m hm t b).q + 1) :=
  Fin.cast (by simp [rightBoundaryUpperIndex]) (Shuffle.rightBoundaryIndex t b)

@[simp]
theorem activeBoundaryFace_leftBoundaryLocalFace (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (a : Fin (p + 3)) :
    (leftBoundaryUpperIndex p q m hm t a).activeBoundaryFace
        (leftBoundaryLocalFace p q m hm t a) =
      leftBoundaryUpperFace p q m t a := by
  apply Fin.ext
  simp [activeBoundaryFace, leftBoundaryLocalFace, leftBoundaryUpperFace]

@[simp]
theorem activeBoundaryFace_rightBoundaryLocalFace (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (b : Fin (q + 2)) :
    (rightBoundaryUpperIndex p q m hm t b).activeBoundaryFace
        (rightBoundaryLocalFace p q m hm t b) =
      rightBoundaryUpperFace p q m t b := by
  apply Fin.ext
  simp [activeBoundaryFace, rightBoundaryLocalFace, rightBoundaryUpperFace]

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient of an inserted-left upper boundary term. -/
def leftUpperCoefficient (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (a : Fin (p + 3)) : ℤ :=
  (-1) ^ (leftBoundaryUpperFace p q m t a).val *
    (leftBoundaryUpperIndex p q m hm t a).sign

/-- The coefficient of its lower-boundary partner. -/
def leftLowerCoefficient (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (a : Fin (p + 3)) (ha : 0 < a.val) : ℤ :=
  (-1) ^ (leftBoundaryLowerFace p q m hm a ha).val *
    (ofGap p q m hm t).sign

/-- The coefficient of an inserted-right upper boundary term. -/
def rightUpperCoefficient (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (b : Fin (q + 2)) : ℤ :=
  (-1) ^ (rightBoundaryUpperFace p q m t b).val *
    (rightBoundaryUpperIndex p q m hm t b).sign

/-- The coefficient of its lower-boundary partner. -/
def rightLowerCoefficient (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (b : Fin (q + 2)) (hb : 0 < b.val) : ℤ :=
  (-1) ^ (rightBoundaryLowerFace p q m b hb).val *
    (ofGap p q m hm t).sign

@[simp]
theorem sign_ofGap (p q m : ℕ) (hm : 0 < m) (t : Shuffle (p + 1) q) :
    (ofGap p q m hm t).sign = (-1 : ℤ) ^ (m + 1) * shuffleSignZ t := by
  rw [sign, gap_ofGap]
  rfl

@[simp]
theorem sign_leftBoundaryUpperIndex (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (a : Fin (p + 3)) :
    (leftBoundaryUpperIndex p q m hm t a).sign =
      (-1 : ℤ) ^ (m + 1) *
        shuffleSignZ (Shuffle.leftBoundaryShuffle t a) := by
  rw [sign, gap_leftBoundaryUpperIndex]
  rfl

@[simp]
theorem sign_rightBoundaryUpperIndex (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (b : Fin (q + 2)) :
    (rightBoundaryUpperIndex p q m hm t b).sign =
      (-1 : ℤ) ^ (m + 1) *
        shuffleSignZ (Shuffle.rightBoundaryShuffle t b) := by
  rw [sign, gap_rightBoundaryUpperIndex]
  rfl

/-- Inserting a positive left position reverses the total Shih boundary
coefficient relative to the corresponding lower coefficient.  The final
position is separated later because its simplex word belongs to the endpoint
telescoping family rather than to the lower-boundary pairing. -/
theorem leftUpperCoefficient_add_lower_eq_zero (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (a : Fin (p + 3)) (ha : 0 < a.val) :
    leftUpperCoefficient p q m hm t a +
        leftLowerCoefficient p q m hm t a ha = 0 := by
  unfold leftUpperCoefficient leftLowerCoefficient leftBoundaryUpperFace
    leftBoundaryLowerFace
  rw [sign_leftBoundaryUpperIndex, sign_ofGap]
  have hs := Shuffle.shuffleSignZ_leftBoundaryShuffle t a
  have hupperParity :
      (-1 : ℤ) ^ m * (-1 : ℤ) ^ (m + 1) = -1 := by
    rw [← pow_add]
    have h : m + (m + 1) = 2 * m + 1 := by omega
    rw [h, pow_succ, pow_mul]
    norm_num
  have hlowerParity :
      (-1 : ℤ) ^ (m - 1) * (-1 : ℤ) ^ (m + 1) = 1 := by
    rw [← pow_add]
    have h : m - 1 + (m + 1) = 2 * m := by omega
    rw [h, pow_mul]
    norm_num
  have hu :
      (-1 : ℤ) ^ (m + (Shuffle.leftBoundaryIndex t a).val) *
          ((-1 : ℤ) ^ (m + 1) *
            shuffleSignZ (Shuffle.leftBoundaryShuffle t a)) =
        -((-1 : ℤ) ^ (Shuffle.leftBoundaryIndex t a).val *
          shuffleSignZ (Shuffle.leftBoundaryShuffle t a)) := by
    rw [pow_add]
    calc
      _ = ((-1 : ℤ) ^ m * (-1 : ℤ) ^ (m + 1)) *
          ((-1 : ℤ) ^ (Shuffle.leftBoundaryIndex t a).val *
            shuffleSignZ (Shuffle.leftBoundaryShuffle t a)) := by ring
      _ = _ := by rw [hupperParity]; ring
  have hl :
      (-1 : ℤ) ^ (m - 1 + a.val) *
          ((-1 : ℤ) ^ (m + 1) * shuffleSignZ t) =
        (-1 : ℤ) ^ a.val * shuffleSignZ t := by
    rw [pow_add]
    calc
      _ = ((-1 : ℤ) ^ (m - 1) * (-1 : ℤ) ^ (m + 1)) *
          ((-1 : ℤ) ^ a.val * shuffleSignZ t) := by ring
      _ = _ := by rw [hlowerParity]; ring
  rw [hu, hl, hs]
  exact neg_add_cancel _

/-- Inserting a noninitial right position reverses the total Shih boundary
coefficient relative to its lower-boundary partner. -/
theorem rightUpperCoefficient_add_lower_eq_zero (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (b : Fin (q + 2)) (hb : 0 < b.val) :
    rightUpperCoefficient p q m hm t b +
        rightLowerCoefficient p q m hm t b hb = 0 := by
  unfold rightUpperCoefficient rightLowerCoefficient rightBoundaryUpperFace
    rightBoundaryLowerFace
  rw [sign_rightBoundaryUpperIndex, sign_ofGap]
  have hs := Shuffle.shuffleSignZ_rightBoundaryShuffle t b
  have hupperParity :
      (-1 : ℤ) ^ m * (-1 : ℤ) ^ (m + 1) = -1 := by
    rw [← pow_add]
    have h : m + (m + 1) = 2 * m + 1 := by omega
    rw [h, pow_succ, pow_mul]
    norm_num
  have hu :
      (-1 : ℤ) ^ (m + (Shuffle.rightBoundaryIndex t b).val) *
          ((-1 : ℤ) ^ (m + 1) *
            shuffleSignZ (Shuffle.rightBoundaryShuffle t b)) =
        -((-1 : ℤ) ^ (Shuffle.rightBoundaryIndex t b).val *
          shuffleSignZ (Shuffle.rightBoundaryShuffle t b)) := by
    rw [pow_add]
    calc
      _ = ((-1 : ℤ) ^ m * (-1 : ℤ) ^ (m + 1)) *
          ((-1 : ℤ) ^ (Shuffle.rightBoundaryIndex t b).val *
            shuffleSignZ (Shuffle.rightBoundaryShuffle t b)) := by ring
      _ = _ := by rw [hupperParity]; ring
  have hl :
      (-1 : ℤ) ^ (m + p + b.val) *
          ((-1 : ℤ) ^ (m + 1) * shuffleSignZ t) =
        -((-1 : ℤ) ^ (p + b.val) * shuffleSignZ t) := by
    rw [show m + p + b.val = m + (p + b.val) by omega, pow_add]
    calc
      _ = ((-1 : ℤ) ^ m * (-1 : ℤ) ^ (m + 1)) *
          ((-1 : ℤ) ^ (p + b.val) * shuffleSignZ t) := by ring
      _ = _ := by rw [hupperParity]; ring
  rw [hu, hl, hs]
  rw [show p + 1 + b.val = p + b.val + 1 by omega, pow_succ]
  ring

end ShihIndex

end AlgebraicTopology.EilenbergZilber
