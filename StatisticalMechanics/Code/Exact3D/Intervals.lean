/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib










namespace StatMech
namespace Exact3D


structure RatInterval where
  lower : ℚ
  upper : ℚ
  lower_le_upper : lower ≤ upper

namespace RatInterval


def MemQ (I : RatInterval) (q : ℚ) : Prop :=
  I.lower ≤ q ∧ q ≤ I.upper


def MemR (I : RatInterval) (x : ℝ) : Prop :=
  (I.lower : ℝ) ≤ x ∧ x ≤ (I.upper : ℝ)

@[simp] theorem memQ_def (I : RatInterval) (q : ℚ) :
    I.MemQ q ↔ I.lower ≤ q ∧ q ≤ I.upper :=
  Iff.rfl

@[simp] theorem memR_def (I : RatInterval) (x : ℝ) :
    I.MemR x ↔ (I.lower : ℝ) ≤ x ∧ x ≤ (I.upper : ℝ) :=
  Iff.rfl


def point (q : ℚ) : RatInterval where
  lower := q
  upper := q
  lower_le_upper := le_rfl


def width (I : RatInterval) : ℚ :=
  I.upper - I.lower

theorem width_nonneg (I : RatInterval) : 0 ≤ I.width := by
  exact sub_nonneg.mpr I.lower_le_upper


def add (I J : RatInterval) : RatInterval where
  lower := I.lower + J.lower
  upper := I.upper + J.upper
  lower_le_upper := add_le_add I.lower_le_upper J.lower_le_upper


def neg (I : RatInterval) : RatInterval where
  lower := -I.upper
  upper := -I.lower
  lower_le_upper := neg_le_neg I.lower_le_upper


def sub (I J : RatInterval) : RatInterval :=
  add I (neg J)


def finsetSum {α : Type*} (s : Finset α) (I : α → RatInterval) : RatInterval where
  lower := s.sum fun a => (I a).lower
  upper := s.sum fun a => (I a).upper
  lower_le_upper := by
    exact Finset.sum_le_sum fun a _ => (I a).lower_le_upper


def Nonnegative (I : RatInterval) : Prop :=
  0 ≤ I.lower



def absUpper (I : RatInterval) : ℚ :=
  max (-I.lower) I.upper

theorem absUpper_nonneg (I : RatInterval) : 0 ≤ I.absUpper := by
  by_cases h : 0 ≤ I.upper
  · exact le_trans h (le_max_right _ _)
  · have hupper : I.upper < 0 := lt_of_not_ge h
    have hlower : I.lower ≤ 0 := le_trans I.lower_le_upper hupper.le
    exact le_trans (neg_nonneg.mpr hlower) (le_max_left _ _)



theorem absUpper_point (q : ℚ) : (point q).absUpper = |q| := by
  rw [abs_eq_max_neg]
  simp [absUpper, point, max_comm]




def mul (I J : RatInterval) : RatInterval where
  lower := -(I.absUpper * J.absUpper)
  upper := I.absUpper * J.absUpper
  lower_le_upper := by
    exact neg_le_self (mul_nonneg I.absUpper_nonneg J.absUpper_nonneg)




def mulNonneg (I J : RatInterval) (hI : I.Nonnegative) (hJ : J.Nonnegative) :
    RatInterval where
  lower := I.lower * J.lower
  upper := I.upper * J.upper
  lower_le_upper :=
    mul_le_mul I.lower_le_upper J.lower_le_upper hJ (le_trans hI I.lower_le_upper)


theorem add_nonnegative {I J : RatInterval}
    (hI : I.Nonnegative) (hJ : J.Nonnegative) :
    (add I J).Nonnegative := by
  simpa [Nonnegative, add] using add_nonneg hI hJ


theorem finsetSum_nonnegative {α : Type*} {s : Finset α}
    {I : α → RatInterval}
    (hI : ∀ a, a ∈ s → (I a).Nonnegative) :
    (finsetSum s I).Nonnegative := by
  simpa [Nonnegative, finsetSum] using
    Finset.sum_nonneg fun a ha => hI a ha


theorem mulNonneg_nonnegative {I J : RatInterval}
    (hI : I.Nonnegative) (hJ : J.Nonnegative) :
    (mulNonneg I J hI hJ).Nonnegative := by
  simpa [Nonnegative, mulNonneg] using mul_nonneg hI hJ

theorem point_memQ (q : ℚ) : (point q).MemQ q := by
  simp [point]

theorem point_memR (q : ℚ) : (point q).MemR (q : ℝ) := by
  simp [point, MemR]


theorem memR_of_memQ {I : RatInterval} {q : ℚ} (hq : I.MemQ q) :
    I.MemR (q : ℝ) := by
  exact ⟨by exact_mod_cast hq.1, by exact_mod_cast hq.2⟩


theorem point_nonnegative {q : ℚ} (hq : 0 ≤ q) : (point q).Nonnegative := by
  simpa [point, Nonnegative] using hq


theorem add_memQ {I J : RatInterval} {x y : ℚ}
    (hx : I.MemQ x) (hy : J.MemQ y) :
    (add I J).MemQ (x + y) := by
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩


theorem add_memR {I J : RatInterval} {x y : ℝ}
    (hx : I.MemR x) (hy : J.MemR y) :
    (add I J).MemR (x + y) := by
  constructor
  · simpa [MemR, add] using add_le_add hx.1 hy.1
  · simpa [MemR, add] using add_le_add hx.2 hy.2


theorem neg_memQ {I : RatInterval} {x : ℚ} (hx : I.MemQ x) :
    (neg I).MemQ (-x) := by
  exact ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩


theorem neg_memR {I : RatInterval} {x : ℝ} (hx : I.MemR x) :
    (neg I).MemR (-x) := by
  constructor
  · simpa [MemR, neg] using neg_le_neg hx.2
  · simpa [MemR, neg] using neg_le_neg hx.1


theorem sub_memQ {I J : RatInterval} {x y : ℚ}
    (hx : I.MemQ x) (hy : J.MemQ y) :
    (sub I J).MemQ (x - y) := by
  simpa [sub, sub_eq_add_neg] using add_memQ hx (neg_memQ hy)


theorem sub_memR {I J : RatInterval} {x y : ℝ}
    (hx : I.MemR x) (hy : J.MemR y) :
    (sub I J).MemR (x - y) := by
  simpa [sub, sub_eq_add_neg] using add_memR hx (neg_memR hy)


theorem finsetSum_memQ {α : Type*} {s : Finset α} {I : α → RatInterval}
    {x : α → ℚ} (hx : ∀ a, a ∈ s → (I a).MemQ (x a)) :
    (finsetSum s I).MemQ (s.sum fun a => x a) := by
  constructor
  · exact Finset.sum_le_sum fun a ha => (hx a ha).1
  · exact Finset.sum_le_sum fun a ha => (hx a ha).2


theorem finsetSum_memR {α : Type*} {s : Finset α} {I : α → RatInterval}
    {x : α → ℝ} (hx : ∀ a, a ∈ s → (I a).MemR (x a)) :
    (finsetSum s I).MemR (s.sum fun a => x a) := by
  constructor
  · simpa [finsetSum, MemR] using Finset.sum_le_sum fun a ha => (hx a ha).1
  · simpa [finsetSum, MemR] using Finset.sum_le_sum fun a ha => (hx a ha).2



theorem abs_le_absUpper_of_memQ {I : RatInterval} {q : ℚ} (hq : I.MemQ q) :
    |q| ≤ I.absUpper := by
  rw [abs_le]
  constructor
  · calc
      -I.absUpper ≤ -(-I.lower) := neg_le_neg (le_max_left (-I.lower) I.upper)
      _ = I.lower := by ring
      _ ≤ q := hq.1
  · exact le_trans hq.2 (le_max_right (-I.lower) I.upper)



theorem abs_le_absUpper_of_memR {I : RatInterval} {x : ℝ} (hx : I.MemR x) :
    |x| ≤ (I.absUpper : ℝ) := by
  rw [abs_le]
  constructor
  · have hleft : (-(I.absUpper) : ℝ) ≤ -(-I.lower : ℚ) := by
      exact neg_le_neg (by exact_mod_cast le_max_left (-I.lower) I.upper)
    have hlower : (-(-I.lower : ℚ) : ℝ) = I.lower := by norm_num
    calc
      (-(I.absUpper) : ℝ) ≤ (-(-I.lower : ℚ) : ℝ) := hleft
      _ = (I.lower : ℝ) := hlower
      _ ≤ x := hx.1
  · exact le_trans hx.2 (by exact_mod_cast le_max_right (-I.lower) I.upper)


theorem mul_memR {I J : RatInterval} {x y : ℝ}
    (hx : I.MemR x) (hy : J.MemR y) :
    (mul I J).MemR (x * y) := by
  have hIx := abs_le_absUpper_of_memR hx
  have hJy := abs_le_absUpper_of_memR hy
  have hprod' : |x * y| ≤ (I.absUpper : ℝ) * (J.absUpper : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul hIx hJy (abs_nonneg y) (by exact_mod_cast I.absUpper_nonneg)
  have hprod : |x * y| ≤ ((I.absUpper * J.absUpper : ℚ) : ℝ) := by
    simpa using hprod'
  rw [abs_le] at hprod
  simpa [MemR, mul] using hprod


theorem mul_memQ {I J : RatInterval} {x y : ℚ}
    (hx : I.MemQ x) (hy : J.MemQ y) :
    (mul I J).MemQ (x * y) := by
  have hIx := abs_le_absUpper_of_memQ hx
  have hJy := abs_le_absUpper_of_memQ hy
  have hprod : |x * y| ≤ I.absUpper * J.absUpper := by
    rw [abs_mul]
    exact mul_le_mul hIx hJy (abs_nonneg y) I.absUpper_nonneg
  rw [abs_le] at hprod
  simpa [MemQ, mul] using hprod


theorem mulNonneg_memQ {I J : RatInterval} {x y : ℚ}
    (hI : I.Nonnegative) (hJ : J.Nonnegative)
    (hx : I.MemQ x) (hy : J.MemQ y) :
    (mulNonneg I J hI hJ).MemQ (x * y) := by
  have hx0 : 0 ≤ x := le_trans hI hx.1
  have hy0 : 0 ≤ y := le_trans hJ hy.1
  constructor
  · exact mul_le_mul hx.1 hy.1 hJ hx0
  · exact mul_le_mul hx.2 hy.2 hy0 (le_trans hI I.lower_le_upper)


theorem mulNonneg_memR {I J : RatInterval} {x y : ℝ}
    (hI : I.Nonnegative) (hJ : J.Nonnegative)
    (hx : I.MemR x) (hy : J.MemR y) :
    (mulNonneg I J hI hJ).MemR (x * y) := by
  have hIℝ : (0 : ℝ) ≤ I.lower := by exact_mod_cast hI
  have hJℝ : (0 : ℝ) ≤ J.lower := by exact_mod_cast hJ
  have hx0 : 0 ≤ x := le_trans hIℝ hx.1
  have hy0 : 0 ≤ y := le_trans hJℝ hy.1
  constructor
  · simpa [MemR, mulNonneg] using mul_le_mul hx.1 hy.1 hJℝ hx0
  · have hIupper : (0 : ℝ) ≤ I.upper := le_trans hIℝ (by exact_mod_cast I.lower_le_upper)
    simpa [MemR, mulNonneg] using mul_le_mul hx.2 hy.2 hy0 hIupper


abbrev IntervalMatrix (m n : ℕ) : Type :=
  Fin m → Fin n → RatInterval



def MatrixMem {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (I : IntervalMatrix m n) : Prop :=
  ∀ i j, (I i j).MemR (A i j)



def MatrixMemQ {m n : ℕ} (A : Fin m → Fin n → ℚ)
    (I : IntervalMatrix m n) : Prop :=
  ∀ i j, (I i j).MemQ (A i j)



def MatrixNonnegative {m n : ℕ} (I : IntervalMatrix m n) : Prop :=
  ∀ i j, (I i j).Nonnegative



theorem MatrixMemQ.memR_coe {m n : ℕ} {A : Fin m → Fin n → ℚ}
    {I : IntervalMatrix m n} (hA : MatrixMemQ A I) :
    MatrixMem (fun i j => (A i j : ℝ)) I := by
  intro i j
  exact memR_of_memQ (hA i j)


def MatrixUpperRowSum {m n : ℕ} (I : IntervalMatrix m n) (i : Fin m) : ℚ :=
  ∑ j, (I i j).upper


def MatrixAbsRowSum {m n : ℕ} (I : IntervalMatrix m n) (i : Fin m) : ℚ :=
  ∑ j, (I i j).absUpper


def MatrixAbsColSum {m n : ℕ} (I : IntervalMatrix m n) (j : Fin n) : ℚ :=
  ∑ i, (I i j).absUpper


abbrev IntervalVector (n : ℕ) : Type :=
  Fin n → RatInterval



def VectorMem {n : ℕ} (x : Fin n → ℝ) (I : IntervalVector n) : Prop :=
  ∀ i, (I i).MemR (x i)



def VectorMemQ {n : ℕ} (x : Fin n → ℚ) (I : IntervalVector n) : Prop :=
  ∀ i, (I i).MemQ (x i)



def VectorNonnegative {n : ℕ} (I : IntervalVector n) : Prop :=
  ∀ i, (I i).Nonnegative



theorem VectorMemQ.memR_coe {n : ℕ} {x : Fin n → ℚ} {I : IntervalVector n}
    (hx : VectorMemQ x I) :
    VectorMem (fun i => (x i : ℝ)) I := by
  intro i
  exact memR_of_memQ (hx i)


def VectorAbsSum {n : ℕ} (I : IntervalVector n) : ℚ :=
  ∑ i, (I i).absUpper


theorem VectorAbsSum_nonneg {n : ℕ} (I : IntervalVector n) :
    0 ≤ VectorAbsSum I := by
  unfold VectorAbsSum
  exact Finset.sum_nonneg fun i _ => (I i).absUpper_nonneg



theorem VectorAbsSum_nonneg_real {n : ℕ} (I : IntervalVector n) :
    0 ≤ (VectorAbsSum I : ℝ) := by
  exact_mod_cast VectorAbsSum_nonneg I



theorem VectorAbsSum_le_of_absUpper_le {n : ℕ}
    {I J : IntervalVector n}
    (h : ∀ i, (I i).absUpper ≤ (J i).absUpper) :
    VectorAbsSum I ≤ VectorAbsSum J := by
  unfold VectorAbsSum
  exact Finset.sum_le_sum fun i _ => h i


def vectorAdd {n : ℕ} (I J : IntervalVector n) : IntervalVector n :=
  fun i => add (I i) (J i)


def vectorNeg {n : ℕ} (I : IntervalVector n) : IntervalVector n :=
  fun i => neg (I i)


def vectorSub {n : ℕ} (I J : IntervalVector n) : IntervalVector n :=
  fun i => sub (I i) (J i)


theorem vectorAdd_nonnegative {n : ℕ} {I J : IntervalVector n}
    (hI : VectorNonnegative I) (hJ : VectorNonnegative J) :
    VectorNonnegative (vectorAdd I J) := by
  intro i
  exact add_nonnegative (hI i) (hJ i)


def pointVector {n : ℕ} (x : Fin n → ℚ) : IntervalVector n :=
  fun i => point (x i)


def pointMatrix {m n : ℕ} (A : Fin m → Fin n → ℚ) : IntervalMatrix m n :=
  fun i j => point (A i j)

@[simp] theorem pointVector_apply {n : ℕ} (x : Fin n → ℚ) (i : Fin n) :
    pointVector x i = point (x i) :=
  rfl

@[simp] theorem pointMatrix_apply {m n : ℕ}
    (A : Fin m → Fin n → ℚ) (i : Fin m) (j : Fin n) :
    pointMatrix A i j = point (A i j) :=
  rfl



theorem pointVector_nonnegative {n : ℕ} {x : Fin n → ℚ}
    (hx : ∀ i, 0 ≤ x i) :
    VectorNonnegative (pointVector x) := by
  intro i
  exact point_nonnegative (hx i)



theorem pointMatrix_nonnegative {m n : ℕ} {A : Fin m → Fin n → ℚ}
    (hA : ∀ i j, 0 ≤ A i j) :
    MatrixNonnegative (pointMatrix A) := by
  intro i j
  exact point_nonnegative (hA i j)



theorem VectorAbsSum_pointVector {n : ℕ} (x : Fin n → ℚ) :
    VectorAbsSum (pointVector x) = ∑ i, |x i| := by
  unfold VectorAbsSum pointVector
  apply Finset.sum_congr rfl
  intro i _
  exact absUpper_point (x i)



theorem MatrixAbsRowSum_pointMatrix {m n : ℕ} (A : Fin m → Fin n → ℚ)
    (i : Fin m) :
    MatrixAbsRowSum (pointMatrix A) i = ∑ j, |A i j| := by
  unfold MatrixAbsRowSum pointMatrix
  apply Finset.sum_congr rfl
  intro j _
  exact absUpper_point (A i j)



theorem MatrixAbsColSum_pointMatrix {m n : ℕ} (A : Fin m → Fin n → ℚ)
    (j : Fin n) :
    MatrixAbsColSum (pointMatrix A) j = ∑ i, |A i j| := by
  unfold MatrixAbsColSum pointMatrix
  apply Finset.sum_congr rfl
  intro i _
  exact absUpper_point (A i j)


def matrixVectorMul {m n : ℕ} (I : IntervalMatrix m n)
    (X : IntervalVector n) : IntervalVector m :=
  fun i => finsetSum Finset.univ fun j => mul (I i j) (X j)



def matrixVectorMulNonneg {m n : ℕ} (I : IntervalMatrix m n)
    (X : IntervalVector n) (hI : MatrixNonnegative I)
    (hX : VectorNonnegative X) : IntervalVector m :=
  fun i => finsetSum Finset.univ fun j =>
    mulNonneg (I i j) (X j) (hI i j) (hX j)


def matrixVectorResidual {n : ℕ} (I : IntervalMatrix n n)
    (X : IntervalVector n) : IntervalVector n :=
  vectorSub (matrixVectorMul I X) X



def matrixVectorResidualNonneg {n : ℕ} (I : IntervalMatrix n n)
    (X : IntervalVector n) (hI : MatrixNonnegative I)
    (hX : VectorNonnegative X) : IntervalVector n :=
  vectorSub (matrixVectorMulNonneg I X hI hX) X


def matrixVectorAffine {m n : ℕ} (I : IntervalMatrix m n)
    (B : IntervalVector m) (X : IntervalVector n) : IntervalVector m :=
  vectorAdd (matrixVectorMul I X) B



def matrixVectorAffineNonneg {m n : ℕ} (I : IntervalMatrix m n)
    (B : IntervalVector m) (X : IntervalVector n)
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X) :
    IntervalVector m :=
  vectorAdd (matrixVectorMulNonneg I X hI hX) B


def matrixVectorAffineResidual {n : ℕ} (I : IntervalMatrix n n)
    (B : IntervalVector n) (X : IntervalVector n) : IntervalVector n :=
  vectorSub (matrixVectorAffine I B X) X



def matrixVectorAffineResidualNonneg {n : ℕ} (I : IntervalMatrix n n)
    (B : IntervalVector n) (X : IntervalVector n)
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X) :
    IntervalVector n :=
  vectorSub (matrixVectorAffineNonneg I B X hI hX) X



theorem MatrixMem.row_sum_le {m n : ℕ} {A : Fin m → Fin n → ℝ}
    {I : IntervalMatrix m n} (hA : MatrixMem A I) (i : Fin m) :
    (∑ j, A i j) ≤ (MatrixUpperRowSum I i : ℝ) := by
  calc
    (∑ j, A i j) ≤ ∑ j, ((I i j).upper : ℝ) := by
      exact Finset.sum_le_sum fun j _ => (hA i j).2
    _ = (MatrixUpperRowSum I i : ℝ) := by
      simp [MatrixUpperRowSum]



theorem MatrixMem.row_abs_sum_le {m n : ℕ} {A : Fin m → Fin n → ℝ}
    {I : IntervalMatrix m n} (hA : MatrixMem A I) (i : Fin m) :
    (∑ j, |A i j|) ≤ (MatrixAbsRowSum I i : ℝ) := by
  calc
    (∑ j, |A i j|) ≤ ∑ j, ((I i j).absUpper : ℝ) := by
      exact Finset.sum_le_sum fun j _ => abs_le_absUpper_of_memR (hA i j)
    _ = (MatrixAbsRowSum I i : ℝ) := by
      simp [MatrixAbsRowSum]



theorem MatrixMem.col_abs_sum_le {m n : ℕ} {A : Fin m → Fin n → ℝ}
    {I : IntervalMatrix m n} (hA : MatrixMem A I) (j : Fin n) :
    (∑ i, |A i j|) ≤ (MatrixAbsColSum I j : ℝ) := by
  calc
    (∑ i, |A i j|) ≤ ∑ i, ((I i j).absUpper : ℝ) := by
      exact Finset.sum_le_sum fun i _ => abs_le_absUpper_of_memR (hA i j)
    _ = (MatrixAbsColSum I j : ℝ) := by
      simp [MatrixAbsColSum]



theorem VectorMem.abs_sum_le {n : ℕ} {x : Fin n → ℝ} {I : IntervalVector n}
    (hx : VectorMem x I) :
    (∑ i, |x i|) ≤ (VectorAbsSum I : ℝ) := by
  calc
    (∑ i, |x i|) ≤ ∑ i, ((I i).absUpper : ℝ) := by
      exact Finset.sum_le_sum fun i _ => abs_le_absUpper_of_memR (hx i)
    _ = (VectorAbsSum I : ℝ) := by
      simp [VectorAbsSum]


theorem vectorAdd_memR {n : ℕ} {x y : Fin n → ℝ}
    {I J : IntervalVector n} (hx : VectorMem x I) (hy : VectorMem y J) :
    VectorMem (fun i => x i + y i) (vectorAdd I J) := by
  intro i
  exact add_memR (hx i) (hy i)


theorem vectorNeg_memR {n : ℕ} {x : Fin n → ℝ} {I : IntervalVector n}
    (hx : VectorMem x I) :
    VectorMem (fun i => -x i) (vectorNeg I) := by
  intro i
  exact neg_memR (hx i)


theorem vectorSub_memR {n : ℕ} {x y : Fin n → ℝ}
    {I J : IntervalVector n} (hx : VectorMem x I) (hy : VectorMem y J) :
    VectorMem (fun i => x i - y i) (vectorSub I J) := by
  intro i
  exact sub_memR (hx i) (hy i)


theorem vectorAdd_memQ {n : ℕ} {x y : Fin n → ℚ}
    {I J : IntervalVector n} (hx : VectorMemQ x I) (hy : VectorMemQ y J) :
    VectorMemQ (fun i => x i + y i) (vectorAdd I J) := by
  intro i
  exact add_memQ (hx i) (hy i)


theorem vectorNeg_memQ {n : ℕ} {x : Fin n → ℚ} {I : IntervalVector n}
    (hx : VectorMemQ x I) :
    VectorMemQ (fun i => -x i) (vectorNeg I) := by
  intro i
  exact neg_memQ (hx i)


theorem vectorSub_memQ {n : ℕ} {x y : Fin n → ℚ}
    {I J : IntervalVector n} (hx : VectorMemQ x I) (hy : VectorMemQ y J) :
    VectorMemQ (fun i => x i - y i) (vectorSub I J) := by
  intro i
  exact sub_memQ (hx i) (hy i)


theorem pointVector_memQ {n : ℕ} (x : Fin n → ℚ) :
    VectorMemQ x (pointVector x) := by
  intro i
  exact point_memQ (x i)


theorem pointVector_memR {n : ℕ} (x : Fin n → ℚ) :
    VectorMem (fun i => (x i : ℝ)) (pointVector x) := by
  exact (pointVector_memQ x).memR_coe


theorem pointMatrix_memQ {m n : ℕ} (A : Fin m → Fin n → ℚ) :
    MatrixMemQ A (pointMatrix A) := by
  intro i j
  exact point_memQ (A i j)


theorem pointMatrix_memR {m n : ℕ} (A : Fin m → Fin n → ℚ) :
    MatrixMem (fun i j => (A i j : ℝ)) (pointMatrix A) :=
  (pointMatrix_memQ A).memR_coe


theorem matrixVectorMul_memR {m n : ℕ} {A : Fin m → Fin n → ℝ}
    {x : Fin n → ℝ} {I : IntervalMatrix m n} {X : IntervalVector n}
    (hA : MatrixMem A I) (hx : VectorMem x X) :
    VectorMem (fun i => ∑ j, A i j * x j) (matrixVectorMul I X) := by
  intro i
  unfold matrixVectorMul
  simpa using finsetSum_memR (s := Finset.univ)
    (I := fun j => mul (I i j) (X j))
    (x := fun j => A i j * x j)
    (fun j _ => mul_memR (hA i j) (hx j))


theorem matrixVectorMulNonneg_memR {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {x : Fin n → ℝ}
    {I : IntervalMatrix m n} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMem A I) (hx : VectorMem x X) :
    VectorMem (fun i => ∑ j, A i j * x j)
      (matrixVectorMulNonneg I X hI hX) := by
  intro i
  unfold matrixVectorMulNonneg
  simpa using finsetSum_memR (s := Finset.univ)
    (I := fun j => mulNonneg (I i j) (X j) (hI i j) (hX j))
    (x := fun j => A i j * x j)
    (fun j _ => mulNonneg_memR (hI i j) (hX j) (hA i j) (hx j))


theorem matrixVectorResidual_memR {n : ℕ} {A : Fin n → Fin n → ℝ}
    {x : Fin n → ℝ} {I : IntervalMatrix n n} {X : IntervalVector n}
    (hA : MatrixMem A I) (hx : VectorMem x X) :
    VectorMem (fun i => (∑ j, A i j * x j) - x i)
      (matrixVectorResidual I X) := by
  exact vectorSub_memR (matrixVectorMul_memR hA hx) hx


theorem matrixVectorResidualNonneg_memR {n : ℕ}
    {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ}
    {I : IntervalMatrix n n} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMem A I) (hx : VectorMem x X) :
    VectorMem (fun i => (∑ j, A i j * x j) - x i)
      (matrixVectorResidualNonneg I X hI hX) := by
  exact vectorSub_memR (matrixVectorMulNonneg_memR hI hX hA hx) hx


theorem matrixVectorAffine_memR {m n : ℕ} {A : Fin m → Fin n → ℝ}
    {b : Fin m → ℝ} {x : Fin n → ℝ} {I : IntervalMatrix m n}
    {B : IntervalVector m} {X : IntervalVector n}
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => (∑ j, A i j * x j) + b i)
      (matrixVectorAffine I B X) := by
  exact vectorAdd_memR (matrixVectorMul_memR hA hx) hb


theorem matrixVectorAffineNonneg_memR {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {x : Fin n → ℝ}
    {I : IntervalMatrix m n} {B : IntervalVector m} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => (∑ j, A i j * x j) + b i)
      (matrixVectorAffineNonneg I B X hI hX) := by
  exact vectorAdd_memR (matrixVectorMulNonneg_memR hI hX hA hx) hb


theorem matrixVectorAffineResidual_memR {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b x : Fin n → ℝ}
    {I : IntervalMatrix n n} {B X : IntervalVector n}
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => ((∑ j, A i j * x j) + b i) - x i)
      (matrixVectorAffineResidual I B X) := by
  exact vectorSub_memR (matrixVectorAffine_memR hA hb hx) hx


theorem matrixVectorAffineResidualNonneg_memR {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b x : Fin n → ℝ}
    {I : IntervalMatrix n n} {B X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => ((∑ j, A i j * x j) + b i) - x i)
      (matrixVectorAffineResidualNonneg I B X hI hX) := by
  exact vectorSub_memR (matrixVectorAffineNonneg_memR hI hX hA hb hx) hx



theorem matrixVectorMulNonneg_nonnegative {m n : ℕ}
    {I : IntervalMatrix m n} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X) :
    VectorNonnegative (matrixVectorMulNonneg I X hI hX) := by
  intro i
  unfold matrixVectorMulNonneg
  exact finsetSum_nonnegative fun j _ =>
    mulNonneg_nonnegative (hI i j) (hX j)



theorem matrixVectorAffineNonneg_nonnegative {m n : ℕ}
    {I : IntervalMatrix m n} {B : IntervalVector m} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hB : VectorNonnegative B)
    (hX : VectorNonnegative X) :
    VectorNonnegative (matrixVectorAffineNonneg I B X hI hX) :=
  vectorAdd_nonnegative (matrixVectorMulNonneg_nonnegative hI hX) hB



theorem matrixVectorMul_memQ {m n : ℕ} {A : Fin m → Fin n → ℚ}
    {x : Fin n → ℚ} {I : IntervalMatrix m n} {X : IntervalVector n}
    (hA : MatrixMemQ A I) (hx : VectorMemQ x X) :
    VectorMemQ (fun i => ∑ j, A i j * x j) (matrixVectorMul I X) := by
  intro i
  unfold matrixVectorMul
  simpa using finsetSum_memQ (s := Finset.univ)
    (I := fun j => mul (I i j) (X j))
    (x := fun j => A i j * x j)
    (fun j _ => mul_memQ (hA i j) (hx j))



theorem matrixVectorMulNonneg_memQ {m n : ℕ}
    {A : Fin m → Fin n → ℚ} {x : Fin n → ℚ}
    {I : IntervalMatrix m n} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMemQ A I) (hx : VectorMemQ x X) :
    VectorMemQ (fun i => ∑ j, A i j * x j)
      (matrixVectorMulNonneg I X hI hX) := by
  intro i
  unfold matrixVectorMulNonneg
  simpa using finsetSum_memQ (s := Finset.univ)
    (I := fun j => mulNonneg (I i j) (X j) (hI i j) (hX j))
    (x := fun j => A i j * x j)
    (fun j _ => mulNonneg_memQ (hI i j) (hX j) (hA i j) (hx j))


theorem matrixVectorResidual_memQ {n : ℕ} {A : Fin n → Fin n → ℚ}
    {x : Fin n → ℚ} {I : IntervalMatrix n n} {X : IntervalVector n}
    (hA : MatrixMemQ A I) (hx : VectorMemQ x X) :
    VectorMemQ (fun i => (∑ j, A i j * x j) - x i)
      (matrixVectorResidual I X) := by
  exact vectorSub_memQ (matrixVectorMul_memQ hA hx) hx


theorem matrixVectorResidualNonneg_memQ {n : ℕ}
    {A : Fin n → Fin n → ℚ} {x : Fin n → ℚ}
    {I : IntervalMatrix n n} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMemQ A I) (hx : VectorMemQ x X) :
    VectorMemQ (fun i => (∑ j, A i j * x j) - x i)
      (matrixVectorResidualNonneg I X hI hX) := by
  exact vectorSub_memQ (matrixVectorMulNonneg_memQ hI hX hA hx) hx


theorem matrixVectorAffine_memQ {m n : ℕ} {A : Fin m → Fin n → ℚ}
    {b : Fin m → ℚ} {x : Fin n → ℚ} {I : IntervalMatrix m n}
    {B : IntervalVector m} {X : IntervalVector n}
    (hA : MatrixMemQ A I) (hb : VectorMemQ b B) (hx : VectorMemQ x X) :
    VectorMemQ (fun i => (∑ j, A i j * x j) + b i)
      (matrixVectorAffine I B X) := by
  exact vectorAdd_memQ (matrixVectorMul_memQ hA hx) hb


theorem matrixVectorAffineNonneg_memQ {m n : ℕ}
    {A : Fin m → Fin n → ℚ} {b : Fin m → ℚ} {x : Fin n → ℚ}
    {I : IntervalMatrix m n} {B : IntervalVector m} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMemQ A I) (hb : VectorMemQ b B) (hx : VectorMemQ x X) :
    VectorMemQ (fun i => (∑ j, A i j * x j) + b i)
      (matrixVectorAffineNonneg I B X hI hX) := by
  exact vectorAdd_memQ (matrixVectorMulNonneg_memQ hI hX hA hx) hb


theorem matrixVectorAffineResidual_memQ {n : ℕ}
    {A : Fin n → Fin n → ℚ} {b x : Fin n → ℚ}
    {I : IntervalMatrix n n} {B X : IntervalVector n}
    (hA : MatrixMemQ A I) (hb : VectorMemQ b B) (hx : VectorMemQ x X) :
    VectorMemQ (fun i => ((∑ j, A i j * x j) + b i) - x i)
      (matrixVectorAffineResidual I B X) := by
  exact vectorSub_memQ (matrixVectorAffine_memQ hA hb hx) hx


theorem matrixVectorAffineResidualNonneg_memQ {n : ℕ}
    {A : Fin n → Fin n → ℚ} {b x : Fin n → ℚ}
    {I : IntervalMatrix n n} {B X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMemQ A I) (hb : VectorMemQ b B) (hx : VectorMemQ x X) :
    VectorMemQ (fun i => ((∑ j, A i j * x j) + b i) - x i)
      (matrixVectorAffineResidualNonneg I B X hI hX) := by
  exact vectorSub_memQ (matrixVectorAffineNonneg_memQ hI hX hA hb hx) hx


structure CaseTable (Case : Type*) where
  cases : Finset Case
  interval : Case → RatInterval


def CaseTable.Covers {Case α : Type*} [DecidableEq Case]
    (T : CaseTable Case) (classify : α → Case) : Prop :=
  ∀ a, classify a ∈ T.cases


def CaseTable.Sound {Case α : Type*} [DecidableEq Case]
    (T : CaseTable Case) (classify : α → Case) (value : α → ℝ) : Prop :=
  ∀ a, (T.interval (classify a)).MemR (value a)

end RatInterval

end Exact3D
end StatMech
