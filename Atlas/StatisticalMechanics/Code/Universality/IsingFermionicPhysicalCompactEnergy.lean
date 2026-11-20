/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalRadialPatch











namespace StatMech.Universality

open Finset

noncomputable section



def fkIsingSquareRadialPatchPrimitiveCellTotalVariation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) : Real :=
  |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j -
      fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| +
    |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) (j + 1) -
      fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1)| +
    |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1) -
      fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| +
    |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) (j + 1) -
      fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j|


def fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) : Real :=
  |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) (j + 1) -
      fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| +
    |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j -
      fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1)|




theorem fkIsingSquareRadialPatch_normSq_full_le_two_mul_diagonalPrimitiveVariation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j < m) :
    Complex.normSq
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i, hi⟩ ⟨j, hj⟩) ≤
      2 *
        (|fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) (j + 1) -
            fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| +
          |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j -
            fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1)|) := by
  let F := fkIsingSquareRadialPatchFullObservable n m hn hm
    ⟨i, hi⟩ ⟨j, hj⟩
  let e := fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, hj⟩
  let H := fkIsingSquareRadialPatchPrimitive n m hn hm hmpos
  have hbottom := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos i j hi (by omega)
  have htop := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos i (j + 1) hi (by omega)
  have hleft := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos i j
  have hright := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos (i + 1) j
  have hinc (s : FKIsingMedialSide) :=
    fkIsingSquareRadialPatchIncidence_increment_eq_normSq_full_projection
      n m hn hm ⟨i, hi⟩ ⟨j, hj⟩ s
  by_cases heven : Even (i + j)
  · have htopOdd : ¬ Even (i + (j + 1)) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    have hrightOdd : ¬ Even (i + 1 + j) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal := by
      dsimp [e]
      rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ heven,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
      ⟨hW, hE, hS, hN⟩
    simp only [fkIsingSquareRadialPatchHorizontalSignedIncrement,
      fkIsingSquareRadialPatchVerticalSignedIncrement,
      heven, htopOdd, hrightOdd, if_true, if_false] at hbottom htop hleft hright
    rw [fkIsingSquareRadialPatchHorizontalIncidence_bottom
        n m hn hm hmpos i j hi hj] at hbottom
    rw [fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell
        n m hn hm hmpos i j hi hj] at htop
    rw [fkIsingSquareRadialPatchVerticalIncidence_left
        n m hn hm hmpos i j hi hj] at hleft
    rw [fkIsingSquareRadialPatchVerticalIncidence_right_of_cell
        n m hn hm hmpos i j hi hj] at hright
    simp only [fkIsingSquareRadialPatchBottomSide,
      fkIsingSquareRadialPatchTopSide, fkIsingSquareRadialPatchLeftSide,
      fkIsingSquareRadialPatchRightSide, heven, if_true] at hbottom htop hleft hright
    have hdiagPrimal : H (i + 1) (j + 1) - H i j =
        Complex.normSq (isingProj Complex.I F) -
          Complex.normSq (isingProj (-1) F) := by
      dsimp [H, F, e] at hW hE hS hN ⊢
      calc
        _ = (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1) -
              fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j) +
            (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) (j + 1) -
              fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1)) := by
                ring
        _ = fkIsingSquareInteriorRadialIncrement n hn
              (fkIsingSquareRadialPatchIncidence n m hn hm
                ⟨i, hi⟩ ⟨j, hj⟩ .south) -
            fkIsingSquareInteriorRadialIncrement n hn
              (fkIsingSquareRadialPatchIncidence n m hn hm
                ⟨i, hi⟩ ⟨j, hj⟩ .east) := by
                rw [hleft, htop]
                ring
        _ = _ := by
          rw [hinc .south, hinc .east, hS, hE]
          rfl
    have hdiagDual : H (i + 1) j - H i (j + 1) =
        Complex.normSq (isingProj 1 F) -
          Complex.normSq (isingProj Complex.I F) := by
      dsimp [H, F, e] at hW hE hS hN ⊢
      calc
        _ = (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j -
              fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j) -
            (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1) -
              fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j) := by
                ring
        _ = fkIsingSquareInteriorRadialIncrement n hn
              (fkIsingSquareRadialPatchIncidence n m hn hm
                ⟨i, hi⟩ ⟨j, hj⟩ .west) -
            fkIsingSquareInteriorRadialIncrement n hn
              (fkIsingSquareRadialPatchIncidence n m hn hm
                ⟨i, hi⟩ ⟨j, hj⟩ .south) := by
                rw [hbottom, hleft]
        _ = _ := by
          rw [hinc .west, hinc .south, hW, hS]
          rfl
    dsimp [F, H] at hdiagPrimal hdiagDual ⊢
    rw [hdiagPrimal, hdiagDual]
    exact isingProj_normSq_le_two_mul_diagonal_variation _

  · have htopEven : Even (i + (j + 1)) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    have hrightEven : Even (i + 1 + j) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical := by
      dsimp [e]
      rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ heven,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
      ⟨hW, hE, hS, hN⟩
    simp only [fkIsingSquareRadialPatchHorizontalSignedIncrement,
      fkIsingSquareRadialPatchVerticalSignedIncrement,
      heven, htopEven, hrightEven, if_true, if_false] at hbottom htop hleft hright
    rw [fkIsingSquareRadialPatchHorizontalIncidence_bottom
        n m hn hm hmpos i j hi hj] at hbottom
    rw [fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell
        n m hn hm hmpos i j hi hj] at htop
    rw [fkIsingSquareRadialPatchVerticalIncidence_left
        n m hn hm hmpos i j hi hj] at hleft
    rw [fkIsingSquareRadialPatchVerticalIncidence_right_of_cell
        n m hn hm hmpos i j hi hj] at hright
    simp only [fkIsingSquareRadialPatchBottomSide,
      fkIsingSquareRadialPatchTopSide, fkIsingSquareRadialPatchLeftSide,
      fkIsingSquareRadialPatchRightSide, heven, if_false] at hbottom htop hleft hright
    have hclosed := isingPrimitiveIncrement_local_closed 1 Complex.I F
      (by norm_num) (by norm_num)
    unfold isingPrimitiveIncrement at hclosed
    have hdiagPrimal : H (i + 1) (j + 1) - H i j =
        Complex.normSq (isingProj Complex.I F) -
          Complex.normSq (isingProj (-1) F) := by
      have hraw : H (i + 1) (j + 1) - H i j =
          Complex.normSq (isingProj 1 F) -
            Complex.normSq (isingProj (-Complex.I) F) := by
        dsimp [H, F, e] at hW hE hS hN ⊢
        calc
          _ = (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1) -
                fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j) +
              (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) (j + 1) -
                fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1)) := by
                  ring
          _ = -fkIsingSquareInteriorRadialIncrement n hn
                (fkIsingSquareRadialPatchIncidence n m hn hm
                  ⟨i, hi⟩ ⟨j, hj⟩ .west) +
              fkIsingSquareInteriorRadialIncrement n hn
                (fkIsingSquareRadialPatchIncidence n m hn hm
                  ⟨i, hi⟩ ⟨j, hj⟩ .south) := by
                  rw [hleft, htop]
          _ = _ := by
            rw [hinc .west, hinc .south, hW, hS]
            simp only [fkIsingSquareRadialPatchFullObservable]
            ring
      linarith
    have hdiagDual : H (i + 1) j - H i (j + 1) =
        Complex.normSq (isingProj 1 F) -
          Complex.normSq (isingProj Complex.I F) := by
      have hraw : H (i + 1) j - H i (j + 1) =
          Complex.normSq (isingProj (-Complex.I) F) -
            Complex.normSq (isingProj (-1) F) := by
        dsimp [H, F, e] at hW hE hS hN ⊢
        calc
          _ = (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j -
                fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j) -
              (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1) -
                fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j) := by
                  ring
          _ = -fkIsingSquareInteriorRadialIncrement n hn
                (fkIsingSquareRadialPatchIncidence n m hn hm
                  ⟨i, hi⟩ ⟨j, hj⟩ .north) +
              fkIsingSquareInteriorRadialIncrement n hn
                (fkIsingSquareRadialPatchIncidence n m hn hm
                  ⟨i, hi⟩ ⟨j, hj⟩ .west) := by
                  rw [hbottom, hleft]
                  ring
          _ = _ := by
            rw [hinc .north, hinc .west, hN, hW]
            simp only [fkIsingSquareRadialPatchFullObservable]
            ring
      linarith
    dsimp [F, H] at hdiagPrimal hdiagDual ⊢
    rw [hdiagPrimal, hdiagDual]
    exact isingProj_normSq_le_two_mul_diagonal_variation _

theorem fkIsingSquareRadialPatch_normSq_full_le_two_mul_cellDiagonalVariation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Fin m) :
    Complex.normSq
        (fkIsingSquareRadialPatchFullObservable n m hn hm i j) ≤
      2 * fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation
        n m hn hm hmpos i j := by
  simpa [fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation] using
    fkIsingSquareRadialPatch_normSq_full_le_two_mul_diagonalPrimitiveVariation
      n m hn hm hmpos i j i.2 j.2

theorem fkIsingSquareRadialPatch_two_mul_normSq_full_eq_cellTotalVariation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Fin m) :
    2 * Complex.normSq
        (fkIsingSquareRadialPatchFullObservable n m hn hm i j) =
      fkIsingSquareRadialPatchPrimitiveCellTotalVariation
        n m hn hm hmpos i j := by
  exact fkIsingSquareRadialPatch_two_mul_normSq_full_eq_cell_totalVariation
    n m hn hm hmpos i j i.2 j.2



theorem fkIsingSquareRadialPatch_physicalNormalized_normSq_sum_eq_totalVariation
    (n m : Nat) (mesh : Real) (hn : 0 < n) (hm : m ≤ n)
    (hmpos : 0 < m) (hmesh : 0 < mesh) :
    mesh ^ 2 *
        ∑ i : Fin m, ∑ j : Fin m,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm i j /
              (Real.sqrt (2 * mesh) : Complex)) =
      mesh / 4 *
        ∑ i : Fin m, ∑ j : Fin m,
          fkIsingSquareRadialPatchPrimitiveCellTotalVariation
            n m hn hm hmpos i j := by
  have hsqrtSq : Real.sqrt (2 * mesh) ^ 2 = 2 * mesh := by
    rw [Real.sq_sqrt]
    positivity
  have hnorm (z : Complex) :
      Complex.normSq (z / (Real.sqrt (2 * mesh) : Complex)) =
        Complex.normSq z / (2 * mesh) := by
    rw [Complex.normSq_div]
    congr 1
    rw [Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (by positivity))]
    exact hsqrtSq
  have hcell (i j : Fin m) :
      Complex.normSq
          (fkIsingSquareRadialPatchFullObservable n m hn hm i j) =
        fkIsingSquareRadialPatchPrimitiveCellTotalVariation
          n m hn hm hmpos i j / 2 := by
    have h :=
      fkIsingSquareRadialPatch_two_mul_normSq_full_eq_cellTotalVariation
        n m hn hm hmpos i j
    linarith
  have hsum_div {α : Type} [Fintype α] (f : α → Real) (a : Real) :
      (∑ x, f x / a) = (∑ x, f x) / a := by
    exact (Finset.sum_div Finset.univ f a).symm
  simp_rw [hnorm, hcell, div_div]
  simp_rw [hsum_div]
  field_simp [ne_of_gt hmesh]
  ring



theorem fkIsingSquareRadialPatch_physicalNormalized_normSq_sum_le_diagonalVariation
    (n m : Nat) (mesh : Real) (hn : 0 < n) (hm : m ≤ n)
    (hmpos : 0 < m) (hmesh : 0 < mesh) :
    mesh ^ 2 *
        ∑ i : Fin m, ∑ j : Fin m,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm i j /
              (Real.sqrt (2 * mesh) : Complex)) ≤
      mesh *
        ∑ i : Fin m, ∑ j : Fin m,
          fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation
            n m hn hm hmpos i j := by
  have hsqrtSq : Real.sqrt (2 * mesh) ^ 2 = 2 * mesh := by
    rw [Real.sq_sqrt]
    positivity
  have hnorm (z : Complex) :
      Complex.normSq (z / (Real.sqrt (2 * mesh) : Complex)) =
        Complex.normSq z / (2 * mesh) := by
    rw [Complex.normSq_div]
    congr 1
    rw [Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (by positivity))]
    exact hsqrtSq
  have hsum :
      (∑ i : Fin m, ∑ j : Fin m,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm i j)) ≤
        2 *
          ∑ i : Fin m, ∑ j : Fin m,
            fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation
              n m hn hm hmpos i j := by
    calc
      (∑ i : Fin m, ∑ j : Fin m,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm i j)) ≤
        ∑ i : Fin m, ∑ j : Fin m,
          2 * fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation
            n m hn hm hmpos i j := by
              apply sum_le_sum
              intro i hi
              apply sum_le_sum
              intro j hj
              exact
                fkIsingSquareRadialPatch_normSq_full_le_two_mul_cellDiagonalVariation
                  n m hn hm hmpos i j
      _ = _ := by simp_rw [Finset.mul_sum]
  have hsum_div {α : Type} [Fintype α] (f : α → Real) (a : Real) :
      (∑ x, f x / a) = (∑ x, f x) / a := by
    exact (Finset.sum_div Finset.univ f a).symm
  simp_rw [hnorm, hsum_div]
  have hmeshNonneg : 0 ≤ mesh / 2 := by positivity
  calc
    mesh ^ 2 *
        ((∑ i : Fin m, ∑ j : Fin m,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm i j)) /
              (2 * mesh)) =
      mesh / 2 *
        ∑ i : Fin m, ∑ j : Fin m,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm i j) := by
              field_simp [ne_of_gt hmesh]
    _ ≤ mesh / 2 *
        (2 *
          ∑ i : Fin m, ∑ j : Fin m,
            fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation
              n m hn hm hmpos i j) :=
      mul_le_mul_of_nonneg_left hsum hmeshNonneg
    _ = _ := by ring



theorem fkIsingSquareRadialPatch_physicalNormalized_normSq_sum_le_of_cellVariation
    (n m : Nat) (mesh B L : Real) (hn : 0 < n) (hm : m ≤ n)
    (hmpos : 0 < m) (hmesh : 0 < mesh) (hB : 0 ≤ B)
    (hscale : mesh * (m : Real) ≤ L)
    (hvariation : ∀ i j : Fin m,
      fkIsingSquareRadialPatchPrimitiveCellTotalVariation
          n m hn hm hmpos i j ≤ 4 * B * mesh) :
    mesh ^ 2 *
        ∑ i : Fin m, ∑ j : Fin m,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm i j /
              (Real.sqrt (2 * mesh) : Complex)) ≤
      B * L ^ 2 := by
  have henergy :=
    fkIsingSquareRadialPatch_physicalNormalized_normSq_sum_eq_totalVariation
      n m mesh hn hm hmpos hmesh
  rw [henergy]
  have hsum :
      (∑ i : Fin m, ∑ j : Fin m,
          fkIsingSquareRadialPatchPrimitiveCellTotalVariation
            n m hn hm hmpos i j) ≤
        (m : Real) ^ 2 * (4 * B * mesh) := by
    calc
      (∑ i : Fin m, ∑ j : Fin m,
          fkIsingSquareRadialPatchPrimitiveCellTotalVariation
            n m hn hm hmpos i j) ≤
          ∑ _i : Fin m, ∑ _j : Fin m, 4 * B * mesh := by
            apply sum_le_sum
            intro i hi
            apply sum_le_sum
            intro j hj
            exact hvariation i j
      _ = (m : Real) ^ 2 * (4 * B * mesh) := by
        simp [pow_two]
        ring
  have hside0 : 0 ≤ mesh * (m : Real) := by positivity
  have hL : 0 ≤ L := hside0.trans hscale
  have hscaleSq : (mesh * (m : Real)) ^ 2 ≤ L ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hscale) (add_nonneg hL hside0)]
  calc
    mesh / 4 *
        ∑ i : Fin m, ∑ j : Fin m,
          fkIsingSquareRadialPatchPrimitiveCellTotalVariation
            n m hn hm hmpos i j ≤
      mesh / 4 * ((m : Real) ^ 2 * (4 * B * mesh)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = B * (mesh * (m : Real)) ^ 2 := by ring
    _ ≤ B * L ^ 2 := mul_le_mul_of_nonneg_left hscaleSq hB

end

end StatMech.Universality
