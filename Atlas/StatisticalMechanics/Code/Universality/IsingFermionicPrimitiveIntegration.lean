/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPrimitive












open Finset

namespace StatMech.Universality

noncomputable section


def IsingRectangleClosedOneForm
    (horizontal vertical : Nat -> Nat -> Real) : Prop :=
  forall i j,
    vertical i j + horizontal i (j + 1) =
      horizontal i j + vertical (i + 1) j


def isingRectanglePrimitive
    (horizontal vertical : Nat -> Nat -> Real) (i j : Nat) : Real :=
  (∑ k ∈ range i, horizontal k 0) +
    ∑ l ∈ range j, vertical i l


def isingRectanglePrimitiveWithBase
    (base : Real) (horizontal vertical : Nat -> Nat -> Real)
    (i j : Nat) : Real :=
  base + isingRectanglePrimitive horizontal vertical i j

theorem isingRectanglePrimitiveWithBase_bottom_boundary
    (base : Real) (horizontal vertical : Nat -> Nat -> Real) (i : Nat) :
    isingRectanglePrimitiveWithBase base horizontal vertical i 0 =
      base + ∑ k ∈ range i, horizontal k 0 := by
  simp [isingRectanglePrimitiveWithBase, isingRectanglePrimitive]

theorem isingRectanglePrimitiveWithBase_left_boundary
    (base : Real) (horizontal vertical : Nat -> Nat -> Real) (j : Nat) :
    isingRectanglePrimitiveWithBase base horizontal vertical 0 j =
      base + ∑ l ∈ range j, vertical 0 l := by
  simp [isingRectanglePrimitiveWithBase, isingRectanglePrimitive]



theorem isingRectanglePrimitiveWithBase_axis_boundary_values
    (base : Real) (horizontal vertical : Nat -> Nat -> Real)
    (hbottom : ∀ i, horizontal i 0 = 0)
    (hleft : ∀ j, vertical 0 j = 0) :
    (∀ i, isingRectanglePrimitiveWithBase base horizontal vertical i 0 = base) ∧
      (∀ j, isingRectanglePrimitiveWithBase base horizontal vertical 0 j = base) := by
  constructor
  · intro i
    rw [isingRectanglePrimitiveWithBase_bottom_boundary]
    simp [hbottom]
  · intro j
    rw [isingRectanglePrimitiveWithBase_left_boundary]
    simp [hleft]


theorem isingRectanglePrimitive_vertical_increment
    (horizontal vertical : Nat -> Nat -> Real) (i j : Nat) :
    isingRectanglePrimitive horizontal vertical i (j + 1) -
        isingRectanglePrimitive horizontal vertical i j = vertical i j := by
  simp only [isingRectanglePrimitive, sum_range_succ]
  ring


theorem isingRectangle_vertical_sum_column_difference
    (horizontal vertical : Nat -> Nat -> Real)
    (hclosed : IsingRectangleClosedOneForm horizontal vertical)
    (i j : Nat) :
    (∑ l ∈ range j, vertical (i + 1) l) -
        ∑ l ∈ range j, vertical i l =
      horizontal i j - horizontal i 0 := by
  have hpoint : forall l,
      vertical (i + 1) l - vertical i l =
        horizontal i (l + 1) - horizontal i l := by
    intro l
    have h := hclosed i l
    dsimp [IsingRectangleClosedOneForm] at hclosed
    linarith
  rw [← sum_sub_distrib]
  simp_rw [hpoint]
  exact sum_range_sub (fun l => horizontal i l) j


theorem isingRectanglePrimitive_horizontal_increment
    (horizontal vertical : Nat -> Nat -> Real)
    (hclosed : IsingRectangleClosedOneForm horizontal vertical)
    (i j : Nat) :
    isingRectanglePrimitive horizontal vertical (i + 1) j -
        isingRectanglePrimitive horizontal vertical i j = horizontal i j := by
  rw [isingRectanglePrimitive, isingRectanglePrimitive, sum_range_succ]
  have htel := isingRectangle_vertical_sum_column_difference
    horizontal vertical hclosed i j
  linarith



theorem isingRectanglePrimitive_eq_left_then_top
    (horizontal vertical : Nat -> Nat -> Real)
    (hclosed : IsingRectangleClosedOneForm horizontal vertical)
    (i j : Nat) :
    isingRectanglePrimitive horizontal vertical i j =
      (∑ l ∈ range j, vertical 0 l) +
        ∑ k ∈ range i, horizontal k j := by
  induction i with
  | zero => simp [isingRectanglePrimitive]
  | succ i ih =>
      have hinc := isingRectanglePrimitive_horizontal_increment
        horizontal vertical hclosed i j
      rw [sum_range_succ]
      linarith



theorem isingRectangle_horizontal_sum_eq_primitive_difference
    (horizontal vertical : Nat -> Nat -> Real)
    (hclosed : IsingRectangleClosedOneForm horizontal vertical)
    (width j : Nat) :
    (∑ i ∈ range width, horizontal i j) =
      isingRectanglePrimitive horizontal vertical width j -
        isingRectanglePrimitive horizontal vertical 0 j := by
  rw [isingRectanglePrimitive_eq_left_then_top
      horizontal vertical hclosed width j,
    isingRectanglePrimitive_eq_left_then_top
      horizontal vertical hclosed 0 j]
  simp



theorem isingRectangle_vertical_sum_eq_primitive_difference
    (horizontal vertical : Nat -> Nat -> Real)
    (i height : Nat) :
    (∑ j ∈ range height, vertical i j) =
      isingRectanglePrimitive horizontal vertical i height -
        isingRectanglePrimitive horizontal vertical i 0 := by
  simp [isingRectanglePrimitive]


theorem isingPrimitiveIncrement_nonneg (F : Complex) :
    0 <= isingPrimitiveIncrement F :=
  Complex.normSq_nonneg F



theorem isingRectanglePrimitive_horizontal_mono_of_increment
    (horizontal vertical : Nat -> Nat -> Real)
    (hclosed : IsingRectangleClosedOneForm horizontal vertical)
    (hnonneg : forall i j, 0 <= horizontal i j)
    (i j : Nat) :
    isingRectanglePrimitive horizontal vertical i j <=
      isingRectanglePrimitive horizontal vertical (i + 1) j := by
  have hinc := isingRectanglePrimitive_horizontal_increment
    horizontal vertical hclosed i j
  linarith [hnonneg i j]


theorem isingRectanglePrimitive_vertical_mono_of_increment
    (horizontal vertical : Nat -> Nat -> Real)
    (hnonneg : forall i j, 0 <= vertical i j)
    (i j : Nat) :
    isingRectanglePrimitive horizontal vertical i j <=
      isingRectanglePrimitive horizontal vertical i (j + 1) := by
  have hinc := isingRectanglePrimitive_vertical_increment
    horizontal vertical i j
  linarith [hnonneg i j]



theorem isingRectangle_horizontal_increment_sum_le
    (horizontal vertical : Nat -> Nat -> Real)
    (hclosed : IsingRectangleClosedOneForm horizontal vertical)
    (C : Real) (width height : Nat)
    (hlower : ∀ i j, 0 ≤ isingRectanglePrimitive horizontal vertical i j)
    (hupper : ∀ i j, isingRectanglePrimitive horizontal vertical i j ≤ C) :
    (∑ j ∈ range height, ∑ i ∈ range width, horizontal i j) ≤
      height * C := by
  calc
    (∑ j ∈ range height, ∑ i ∈ range width, horizontal i j) =
        ∑ j ∈ range height,
          (isingRectanglePrimitive horizontal vertical width j -
            isingRectanglePrimitive horizontal vertical 0 j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact isingRectangle_horizontal_sum_eq_primitive_difference
        horizontal vertical hclosed width j
    _ ≤ ∑ _j ∈ range height, C := by
      apply Finset.sum_le_sum
      intro j hj
      linarith [hlower 0 j, hupper width j]
    _ = height * C := by simp


theorem isingRectangle_vertical_increment_sum_le
    (horizontal vertical : Nat -> Nat -> Real)
    (C : Real) (width height : Nat)
    (hlower : ∀ i j, 0 ≤ isingRectanglePrimitive horizontal vertical i j)
    (hupper : ∀ i j, isingRectanglePrimitive horizontal vertical i j ≤ C) :
    (∑ i ∈ range width, ∑ j ∈ range height, vertical i j) ≤
      width * C := by
  calc
    (∑ i ∈ range width, ∑ j ∈ range height, vertical i j) =
        ∑ i ∈ range width,
          (isingRectanglePrimitive horizontal vertical i height -
            isingRectanglePrimitive horizontal vertical i 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact isingRectangle_vertical_sum_eq_primitive_difference
        horizontal vertical i height
    _ ≤ ∑ _i ∈ range width, C := by
      apply Finset.sum_le_sum
      intro i hi
      linarith [hlower i 0, hupper i height]
    _ = width * C := by simp



theorem isingRectangle_increment_sum_le
    (horizontal vertical : Nat -> Nat -> Real)
    (hclosed : IsingRectangleClosedOneForm horizontal vertical)
    (C : Real) (width height : Nat)
    (hlower : ∀ i j, 0 ≤ isingRectanglePrimitive horizontal vertical i j)
    (hupper : ∀ i j, isingRectanglePrimitive horizontal vertical i j ≤ C) :
    (∑ j ∈ range height, ∑ i ∈ range width, horizontal i j) +
        (∑ i ∈ range width, ∑ j ∈ range height, vertical i j) ≤
      (height + width) * C := by
  have hh := isingRectangle_horizontal_increment_sum_le
    horizontal vertical hclosed C width height hlower hupper
  have hv := isingRectangle_vertical_increment_sum_le
    horizontal vertical C width height hlower hupper
  nlinarith




theorem isingRectangle_scaled_increment_sum_le
    (horizontal vertical : Nat -> Nat -> Real)
    (hclosed : IsingRectangleClosedOneForm horizontal vertical)
    (C mesh L : Real) (width height : Nat)
    (hlower : ∀ i j, 0 ≤ isingRectanglePrimitive horizontal vertical i j)
    (hupper : ∀ i j, isingRectanglePrimitive horizontal vertical i j ≤ C)
    (hmesh : 0 ≤ mesh) (hC : 0 ≤ C)
    (hscale : mesh * (height + width) ≤ L) :
    mesh *
        ((∑ j ∈ range height, ∑ i ∈ range width, horizontal i j) +
          (∑ i ∈ range width, ∑ j ∈ range height, vertical i j)) ≤
      L * C := by
  have hsum := isingRectangle_increment_sum_le
    horizontal vertical hclosed C width height hlower hupper
  calc
    mesh *
        ((∑ j ∈ range height, ∑ i ∈ range width, horizontal i j) +
          (∑ i ∈ range width, ∑ j ∈ range height, vertical i j)) ≤
        mesh * ((height + width) * C) :=
      mul_le_mul_of_nonneg_left hsum hmesh
    _ = (mesh * (height + width)) * C := by ring
    _ ≤ L * C := mul_le_mul_of_nonneg_right hscale hC


theorem isingRectangle_scaled_normSq_sum_le
    (horizontalF verticalF : Nat -> Nat -> Complex)
    (hclosed : IsingRectangleClosedOneForm
      (fun i j => isingPrimitiveIncrement (horizontalF i j))
      (fun i j => isingPrimitiveIncrement (verticalF i j)))
    (C mesh L : Real) (width height : Nat)
    (hlower : ∀ i j, 0 ≤ isingRectanglePrimitive
      (fun a b => isingPrimitiveIncrement (horizontalF a b))
      (fun a b => isingPrimitiveIncrement (verticalF a b)) i j)
    (hupper : ∀ i j, isingRectanglePrimitive
      (fun a b => isingPrimitiveIncrement (horizontalF a b))
      (fun a b => isingPrimitiveIncrement (verticalF a b)) i j ≤ C)
    (hmesh : 0 ≤ mesh) (hC : 0 ≤ C)
    (hscale : mesh * (height + width) ≤ L) :
    mesh *
        ((∑ j ∈ range height, ∑ i ∈ range width,
            Complex.normSq (horizontalF i j)) +
          (∑ i ∈ range width, ∑ j ∈ range height,
            Complex.normSq (verticalF i j))) ≤
      L * C := by
  simpa only [isingPrimitiveIncrement] using
    isingRectangle_scaled_increment_sum_le
      (fun i j => isingPrimitiveIncrement (horizontalF i j))
      (fun i j => isingPrimitiveIncrement (verticalF i j))
      hclosed C mesh L width height hlower hupper hmesh hC hscale





theorem isingRectangle_physicalNormalized_normSq_sum_le
    (horizontalF verticalF : Nat -> Nat -> Complex)
    (hclosed : IsingRectangleClosedOneForm
      (fun i j => isingPrimitiveIncrement (horizontalF i j))
      (fun i j => isingPrimitiveIncrement (verticalF i j)))
    (C mesh L : Real) (width height : Nat)
    (hlower : ∀ i j, 0 ≤ isingRectanglePrimitive
      (fun a b => isingPrimitiveIncrement (horizontalF a b))
      (fun a b => isingPrimitiveIncrement (verticalF a b)) i j)
    (hupper : ∀ i j, isingRectanglePrimitive
      (fun a b => isingPrimitiveIncrement (horizontalF a b))
      (fun a b => isingPrimitiveIncrement (verticalF a b)) i j ≤ C)
    (hmesh : 0 < mesh) (hC : 0 ≤ C)
    (hscale : mesh * (height + width) ≤ L) :
    mesh ^ 2 *
        ((∑ j ∈ range height, ∑ i ∈ range width,
            Complex.normSq
              (horizontalF i j / (Real.sqrt (2 * mesh) : Complex))) +
          (∑ i ∈ range width, ∑ j ∈ range height,
            Complex.normSq
              (verticalF i j / (Real.sqrt (2 * mesh) : Complex)))) ≤
      L * C / 2 := by
  have hsqrtSq : Real.sqrt (2 * mesh) ^ 2 = 2 * mesh := by
    rw [Real.sq_sqrt]
    positivity
  have hnormSq (z : Complex) :
      Complex.normSq (z / (Real.sqrt (2 * mesh) : Complex)) =
        Complex.normSq z / (2 * mesh) := by
    rw [Complex.normSq_div]
    congr 1
    rw [Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (by positivity))]
    exact hsqrtSq
  have hraw := isingRectangle_scaled_normSq_sum_le
    horizontalF verticalF hclosed C mesh L width height hlower hupper
      hmesh.le hC hscale
  simp_rw [hnormSq, ← Finset.sum_div] at ⊢
  have hmesh_ne : mesh ≠ 0 := hmesh.ne'
  have hrewrite :
      mesh ^ 2 *
          (((∑ j ∈ range height, ∑ i ∈ range width,
              Complex.normSq (horizontalF i j)) / (2 * mesh)) +
            ((∑ i ∈ range width, ∑ j ∈ range height,
              Complex.normSq (verticalF i j)) / (2 * mesh))) =
        (mesh *
          ((∑ j ∈ range height, ∑ i ∈ range width,
              Complex.normSq (horizontalF i j)) +
            (∑ i ∈ range width, ∑ j ∈ range height,
              Complex.normSq (verticalF i j)))) / 2 := by
    field_simp [hmesh_ne]
  rw [hrewrite]
  exact div_le_div_of_nonneg_right hraw (by norm_num)

end

end StatMech.Universality
