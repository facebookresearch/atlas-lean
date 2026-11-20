/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPrimitiveIntegration









namespace StatMech.Universality

open Finset

noncomputable section

def IsingRectangleClosedOneFormOn
    (horizontal vertical : Nat → Nat → Real)
    (width height : Nat) : Prop :=
  ∀ i < width, ∀ j < height,
    vertical i j + horizontal i (j + 1) =
      horizontal i j + vertical (i + 1) j

theorem isingRectangle_vertical_sum_column_difference_on
    (horizontal vertical : Nat → Nat → Real)
    (width height : Nat)
    (hclosed : IsingRectangleClosedOneFormOn
      horizontal vertical width height)
    (i j : Nat) (hi : i < width) (hj : j ≤ height) :
    (∑ l ∈ range j, vertical (i + 1) l) -
        ∑ l ∈ range j, vertical i l =
      horizontal i j - horizontal i 0 := by
  rw [← sum_sub_distrib]
  calc
    (∑ l ∈ range j, (vertical (i + 1) l - vertical i l)) =
        ∑ l ∈ range j, (horizontal i (l + 1) - horizontal i l) := by
      apply sum_congr rfl
      intro l hl
      have hc := hclosed i hi l (lt_of_lt_of_le (mem_range.mp hl) hj)
      linarith
    _ = horizontal i j - horizontal i 0 :=
      sum_range_sub (fun l ↦ horizontal i l) j

theorem isingRectanglePrimitive_horizontal_increment_on
    (horizontal vertical : Nat → Nat → Real)
    (width height : Nat)
    (hclosed : IsingRectangleClosedOneFormOn
      horizontal vertical width height)
    (i j : Nat) (hi : i < width) (hj : j ≤ height) :
    isingRectanglePrimitive horizontal vertical (i + 1) j -
        isingRectanglePrimitive horizontal vertical i j = horizontal i j := by
  rw [isingRectanglePrimitive, isingRectanglePrimitive, sum_range_succ]
  have htel := isingRectangle_vertical_sum_column_difference_on
    horizontal vertical width height hclosed i j hi hj
  linarith

theorem isingRectangle_horizontal_sum_eq_primitive_difference_on
    (horizontal vertical : Nat → Nat → Real)
    (width height j : Nat)
    (hclosed : IsingRectangleClosedOneFormOn
      horizontal vertical width height)
    (hj : j ≤ height) :
    (∑ i ∈ range width, horizontal i j) =
      isingRectanglePrimitive horizontal vertical width j -
        isingRectanglePrimitive horizontal vertical 0 j := by
  calc
    (∑ i ∈ range width, horizontal i j) =
        ∑ i ∈ range width,
          (isingRectanglePrimitive horizontal vertical (i + 1) j -
            isingRectanglePrimitive horizontal vertical i j) := by
      apply sum_congr rfl
      intro i hi
      rw [isingRectanglePrimitive_horizontal_increment_on
        horizontal vertical width height hclosed i j (mem_range.mp hi) hj]
    _ = isingRectanglePrimitive horizontal vertical width j -
          isingRectanglePrimitive horizontal vertical 0 j :=
      sum_range_sub
        (fun i ↦ isingRectanglePrimitive horizontal vertical i j) width

theorem isingRectangle_increment_sum_le_on
    (horizontal vertical : Nat → Nat → Real)
    (C : Real) (width height : Nat)
    (hclosed : IsingRectangleClosedOneFormOn
      horizontal vertical width height)
    (hlower : ∀ i ≤ width, ∀ j ≤ height,
      0 ≤ isingRectanglePrimitive horizontal vertical i j)
    (hupper : ∀ i ≤ width, ∀ j ≤ height,
      isingRectanglePrimitive horizontal vertical i j ≤ C) :
    (∑ j ∈ range height, ∑ i ∈ range width, horizontal i j) +
        (∑ i ∈ range width, ∑ j ∈ range height, vertical i j) ≤
      (height + width) * C := by
  have hh : (∑ j ∈ range height, ∑ i ∈ range width, horizontal i j) ≤
      height * C := by
    calc
      (∑ j ∈ range height, ∑ i ∈ range width, horizontal i j) =
          ∑ j ∈ range height,
            (isingRectanglePrimitive horizontal vertical width j -
              isingRectanglePrimitive horizontal vertical 0 j) := by
        apply sum_congr rfl
        intro j hj
        exact isingRectangle_horizontal_sum_eq_primitive_difference_on
          horizontal vertical width height j hclosed
          (Nat.le_of_lt (mem_range.mp hj))
      _ ≤ ∑ _j ∈ range height, C := by
        apply sum_le_sum
        intro j hj
        have hjle := Nat.le_of_lt (mem_range.mp hj)
        linarith [hlower 0 (Nat.zero_le width) j hjle,
          hupper width le_rfl j hjle]
      _ = height * C := by simp
  have hv : (∑ i ∈ range width, ∑ j ∈ range height, vertical i j) ≤
      width * C := by
    calc
      (∑ i ∈ range width, ∑ j ∈ range height, vertical i j) =
          ∑ i ∈ range width,
            (isingRectanglePrimitive horizontal vertical i height -
              isingRectanglePrimitive horizontal vertical i 0) := by
        apply sum_congr rfl
        intro i hi
        exact isingRectangle_vertical_sum_eq_primitive_difference
          horizontal vertical i height
      _ ≤ ∑ _i ∈ range width, C := by
        apply sum_le_sum
        intro i hi
        have hile := Nat.le_of_lt (mem_range.mp hi)
        linarith [hlower i hile 0 (Nat.zero_le height),
          hupper i hile height le_rfl]
      _ = width * C := by simp
  nlinarith

theorem isingRectangle_scaled_increment_sum_le_on
    (horizontal vertical : Nat → Nat → Real)
    (C mesh L : Real) (width height : Nat)
    (hclosed : IsingRectangleClosedOneFormOn
      horizontal vertical width height)
    (hlower : ∀ i ≤ width, ∀ j ≤ height,
      0 ≤ isingRectanglePrimitive horizontal vertical i j)
    (hupper : ∀ i ≤ width, ∀ j ≤ height,
      isingRectanglePrimitive horizontal vertical i j ≤ C)
    (hmesh : 0 ≤ mesh) (hC : 0 ≤ C)
    (hscale : mesh * (height + width) ≤ L) :
    mesh *
        ((∑ j ∈ range height, ∑ i ∈ range width, horizontal i j) +
          (∑ i ∈ range width, ∑ j ∈ range height, vertical i j)) ≤
      L * C := by
  have hsum := isingRectangle_increment_sum_le_on
    horizontal vertical C width height hclosed hlower hupper
  calc
    mesh *
        ((∑ j ∈ range height, ∑ i ∈ range width, horizontal i j) +
          (∑ i ∈ range width, ∑ j ∈ range height, vertical i j)) ≤
        mesh * ((height + width) * C) :=
      mul_le_mul_of_nonneg_left hsum hmesh
    _ = (mesh * (height + width)) * C := by ring
    _ ≤ L * C := mul_le_mul_of_nonneg_right hscale hC

theorem isingRectangle_physicalNormalized_normSq_sum_le_on
    (horizontalF verticalF : Nat → Nat → Complex)
    (C mesh L : Real) (width height : Nat)
    (hclosed : IsingRectangleClosedOneFormOn
      (fun i j ↦ isingPrimitiveIncrement (horizontalF i j))
      (fun i j ↦ isingPrimitiveIncrement (verticalF i j)) width height)
    (hlower : ∀ i ≤ width, ∀ j ≤ height, 0 ≤ isingRectanglePrimitive
      (fun a b ↦ isingPrimitiveIncrement (horizontalF a b))
      (fun a b ↦ isingPrimitiveIncrement (verticalF a b)) i j)
    (hupper : ∀ i ≤ width, ∀ j ≤ height, isingRectanglePrimitive
      (fun a b ↦ isingPrimitiveIncrement (horizontalF a b))
      (fun a b ↦ isingPrimitiveIncrement (verticalF a b)) i j ≤ C)
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
  have hraw := isingRectangle_scaled_increment_sum_le_on
    (fun i j ↦ isingPrimitiveIncrement (horizontalF i j))
    (fun i j ↦ isingPrimitiveIncrement (verticalF i j))
    C mesh L width height hclosed hlower hupper (le_of_lt hmesh) hC hscale
  simp only [isingPrimitiveIncrement] at hraw
  simp_rw [hnormSq, ← Finset.sum_div] at ⊢
  have hmesh_ne : mesh ≠ 0 := ne_of_gt hmesh
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
