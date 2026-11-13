/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPrimitiveIncrementComparison
import Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerIntegration











namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

private theorem int_natAbs_le_of_bounds {n : Nat} {z : Int}
    (h0 : -(n : Int) <= z) (h1 : z <= (n : Int)) : z.natAbs <= n := by
  have h : |z| <= (n : Int) := abs_le.mpr ⟨h0, h1⟩
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h



theorem
    fkIsingSquareBoundaryLayerRadialCell_increment_eq_normSq_full_projection
    (n : Nat) (hn : 0 < n)
    (C : FKIsingSquareInteriorRadialCell n) (s : FKIsingMedialSide) :
    fkIsingSquareBoundaryLayerRadialIncrement n hn
        (fkIsingSquareInteriorRadialCellIncidence n hn C s) =
      Complex.normSq
        (isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (C.1, s)))
          (fkIsingSquareBoundaryFullMedialObservable n hn C.1)) := by
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (C.1, s)) = _
  exact fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
    n hn C.1 (fkIsingSquareInteriorRadialCell_not_mem_perimeter n C) s



theorem fkIsingSquareFullRadialCellOfCoordinate_axis_horizontal
    (n : Nat) (q : Int × Int)
    (hq : FKIsingSquareFullDiamondCell n q)
    (heven : Even (q.1 + q.2)) :
    (fkIsingSquareOrientedEdge n
      (fkIsingSquareFullRadialCellOfCoordinate n q hq).1).axis =
        .horizontal := by
  let a : Int := Classical.choose heven
  have ha : q.1 + q.2 = a + a := Classical.choose_spec heven
  let b : Int := q.1 - a
  have h00 := hq.1
  have h10 := hq.2.1
  have h01 := hq.2.2.1
  have h11 := hq.2.2.2
  simp [FKIsingSquareFullDiamond] at h00 h10 h01 h11
  have ha0 : -(n : Int) <= a := by omega
  have ha1 : a < (n : Int) := by omega
  have hb0 : -(n : Int) <= b := by
    dsimp [b]
    omega
  have hb1 : b <= (n : Int) := by
    dsimp [b]
    omega
  let u : FKIsingSquareFullVertexNode n :=
    ⟨![a, b], by
      intro k
      fin_cases k
      · exact int_natAbs_le_of_bounds ha0 ha1.le
      · exact int_natAbs_le_of_bounds hb0 hb1⟩
  have hu : fkIsingSquareDirectionAvailable n u .east := by
    change a < (n : Int)
    exact ha1
  have hcell : (fkIsingSquareFullRadialCellOfCoordinate n q hq).1 =
      fkIsingSquareDirectionEdge n u .east hu := by
    simp [fkIsingSquareFullRadialCellOfCoordinate, heven, u, b, a]
  rw [hcell, fkIsingSquareOrientedEdge_directionEdge]
  simp [fkIsingSquareDirectionEdgeOrientation]


theorem fkIsingSquareFullRadialCellOfCoordinate_axis_vertical
    (n : Nat) (q : Int × Int)
    (hq : FKIsingSquareFullDiamondCell n q)
    (hodd : ¬ Even (q.1 + q.2)) :
    (fkIsingSquareOrientedEdge n
      (fkIsingSquareFullRadialCellOfCoordinate n q hq).1).axis =
        .vertical := by
  have ho : Odd (q.1 + q.2) := Int.not_even_iff_odd.mp hodd
  let a : Int := Classical.choose ho
  have ha : q.1 + q.2 = 2 * a + 1 := Classical.choose_spec ho
  let b : Int := q.1 - a - 1
  have h00 := hq.1
  have h10 := hq.2.1
  have h01 := hq.2.2.1
  have h11 := hq.2.2.2
  simp [FKIsingSquareFullDiamond] at h00 h10 h01 h11
  have ha0 : -(n : Int) <= a + 1 := by omega
  have ha1 : a + 1 < (n : Int) := by omega
  have hb0 : -(n : Int) <= b := by
    dsimp [b]
    omega
  have hb1 : b < (n : Int) := by
    dsimp [b]
    omega
  let u : FKIsingSquareFullVertexNode n :=
    ⟨![a + 1, b], by
      intro k
      fin_cases k
      · exact int_natAbs_le_of_bounds ha0 ha1.le
      · exact int_natAbs_le_of_bounds hb0 hb1.le⟩
  have hu : fkIsingSquareDirectionAvailable n u .north := by
    change b < (n : Int)
    exact hb1
  have hcell : (fkIsingSquareFullRadialCellOfCoordinate n q hq).1 =
      fkIsingSquareDirectionEdge n u .north hu := by
    simp [fkIsingSquareFullRadialCellOfCoordinate, hodd, u, b, a]
  rw [hcell, fkIsingSquareOrientedEdge_directionEdge]
  simp [fkIsingSquareDirectionEdgeOrientation]




theorem FKIsingSquareFullCoordinateOneForm.coordinatePrimitive_even_northeast
    (n : Nat) (hn : 0 < n)
    (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real)
    (hinc : forall C : FKIsingSquareInteriorRadialCell n,
      inc (fkIsingSquareInteriorRadialCellIncidence n hn C .west) +
          inc (fkIsingSquareInteriorRadialCellIncidence n hn C .east) =
        inc (fkIsingSquareInteriorRadialCellIncidence n hn C .south) +
          inc (fkIsingSquareInteriorRadialCellIncidence n hn C .north))
    (q : Int × Int) (hq : FKIsingSquareFullDiamondCell n q)
    (heven : Even (q.1 + q.2)) :
    let A := fkIsingSquareFullCoordinateOneFormOf n hn inc hinc
    let C := fkIsingSquareFullRadialCellOfCoordinate n q hq
    A.coordinatePrimitive (q.1 + 1, q.2 + 1) - A.coordinatePrimitive q =
      inc (fkIsingSquareInteriorRadialCellIncidence n hn C .west) -
        inc (fkIsingSquareInteriorRadialCellIncidence n hn C .north) := by
  let A := fkIsingSquareFullCoordinateOneFormOf n hn inc hinc
  let C := fkIsingSquareFullRadialCellOfCoordinate n q hq
  let west := fkIsingSquareInteriorRadialCellIncidence n hn C .west
  let north := fkIsingSquareInteriorRadialCellIncidence n hn C .north
  have hw := fkIsingSquareFullRadialCellOfCoordinate_even_side_coordinates
    n hn q hq heven .west
  have hnorth := fkIsingSquareFullRadialCellOfCoordinate_even_side_coordinates
    n hn q hq heven .north
  change fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn west = q ∧
    fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn west =
      (q.1 + 1, q.2) at hw
  change fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn north =
      (q.1 + 1, q.2 + 1) ∧
    fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn north =
      (q.1 + 1, q.2) at hnorth
  have nqW := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n q hq.1
    (fkIsingSquareInteriorRadialEndpoint n hn west) hw.1
  have neW := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n
    (q.1 + 1, q.2) hq.2.1
    (fkIsingSquareFullFaceOfRadialIncidence n hn west) hw.2
  have neN := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n
    (q.1 + 1, q.2) hq.2.1
    (fkIsingSquareFullFaceOfRadialIncidence n hn north) hnorth.2
  have nneN := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n
    (q.1 + 1, q.2 + 1) hq.2.2.2
    (fkIsingSquareInteriorRadialEndpoint n hn north) hnorth.1
  have hH : A.horizontal q = inc west := by
    simp [A, fkIsingSquareFullCoordinateOneFormOf,
      fkIsingSquareFullHorizontalIncrementOf, nqW, neW]
  have hV : A.vertical (q.1 + 1, q.2) = -inc north := by
    simp [A, fkIsingSquareFullCoordinateOneFormOf,
      fkIsingSquareFullVerticalIncrementOf, neN, nneN]
  have hHorizontal := A.coordinatePrimitive_horizontal_increment q hq.1
  have hVertical := A.coordinatePrimitive_vertical_increment
    (q.1 + 1, q.2) hq.2.1 hq.2.2.2
  dsimp only at hHorizontal hVertical ⊢
  rw [hH] at hHorizontal
  rw [hV] at hVertical
  linarith




theorem FKIsingSquareFullCoordinateOneForm.coordinatePrimitive_odd_southeast
    (n : Nat) (hn : 0 < n)
    (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real)
    (hinc : forall C : FKIsingSquareInteriorRadialCell n,
      inc (fkIsingSquareInteriorRadialCellIncidence n hn C .west) +
          inc (fkIsingSquareInteriorRadialCellIncidence n hn C .east) =
        inc (fkIsingSquareInteriorRadialCellIncidence n hn C .south) +
          inc (fkIsingSquareInteriorRadialCellIncidence n hn C .north))
    (q : Int × Int) (hq : FKIsingSquareFullDiamondCell n q)
    (hodd : ¬ Even (q.1 + q.2)) :
    let A := fkIsingSquareFullCoordinateOneFormOf n hn inc hinc
    let C := fkIsingSquareFullRadialCellOfCoordinate n q hq
    A.coordinatePrimitive (q.1 + 1, q.2) -
        A.coordinatePrimitive (q.1, q.2 + 1) =
      inc (fkIsingSquareInteriorRadialCellIncidence n hn C .west) -
        inc (fkIsingSquareInteriorRadialCellIncidence n hn C .north) := by
  let A := fkIsingSquareFullCoordinateOneFormOf n hn inc hinc
  let C := fkIsingSquareFullRadialCellOfCoordinate n q hq
  let west := fkIsingSquareInteriorRadialCellIncidence n hn C .west
  let north := fkIsingSquareInteriorRadialCellIncidence n hn C .north
  have hw := fkIsingSquareFullRadialCellOfCoordinate_odd_side_coordinates
    n hn q hq hodd .west
  have hnorth := fkIsingSquareFullRadialCellOfCoordinate_odd_side_coordinates
    n hn q hq hodd .north
  change fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn west =
      (q.1, q.2 + 1) ∧
    fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn west = q at hw
  change fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn north =
      (q.1 + 1, q.2) ∧
    fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn north = q at hnorth
  have nnW := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n
    (q.1, q.2 + 1) hq.2.2.1
    (fkIsingSquareInteriorRadialEndpoint n hn west) hw.1
  have nqW := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n q hq.1
    (fkIsingSquareFullFaceOfRadialIncidence n hn west) hw.2
  have neN := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n
    (q.1 + 1, q.2) hq.2.1
    (fkIsingSquareInteriorRadialEndpoint n hn north) hnorth.1
  have nqN := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n q hq.1
    (fkIsingSquareFullFaceOfRadialIncidence n hn north) hnorth.2
  have hH : A.horizontal q = -inc north := by
    simp [A, fkIsingSquareFullCoordinateOneFormOf,
      fkIsingSquareFullHorizontalIncrementOf, nqN, neN]
  have hV : A.vertical q = -inc west := by
    simp [A, fkIsingSquareFullCoordinateOneFormOf,
      fkIsingSquareFullVerticalIncrementOf, nqW, nnW]
  have hHorizontal := A.coordinatePrimitive_horizontal_increment q hq.1
  have hVertical := A.coordinatePrimitive_vertical_increment
    q hq.1 hq.2.2.1
  dsimp only at hHorizontal hVertical ⊢
  rw [hH] at hHorizontal
  rw [hV] at hVertical
  linarith




theorem
    fkIsingSquareBoundaryLayer_coordinatePrimitive_even_northeast_eq_sq_im
    (n : Nat) (hn : 0 < n) (q : Int × Int)
    (hq : FKIsingSquareFullDiamondCell n q)
    (heven : Even (q.1 + q.2)) :
    let A := fkIsingSquareBoundaryLayerCoordinateOneForm n hn
    let C := fkIsingSquareFullRadialCellOfCoordinate n q hq
    A.coordinatePrimitive (q.1 + 1, q.2 + 1) - A.coordinatePrimitive q =
      ((fkIsingSquareBoundaryFullMedialObservable n hn C.1) ^ 2 *
        ((-1 + Complex.I) / 2)).im := by
  let A := fkIsingSquareBoundaryLayerCoordinateOneForm n hn
  let C := fkIsingSquareFullRadialCellOfCoordinate n q hq
  let west := fkIsingSquareInteriorRadialCellIncidence n hn C .west
  let north := fkIsingSquareInteriorRadialCellIncidence n hn C .north
  have hmacro :=
    FKIsingSquareFullCoordinateOneForm.coordinatePrimitive_even_northeast
      n hn (fkIsingSquareBoundaryLayerRadialIncrement n hn)
      (fkIsingSquareBoundaryLayerRadialCell_increment_closed n hn)
      q hq heven
  have haxis := fkIsingSquareFullRadialCellOfCoordinate_axis_horizontal
    n q hq heven
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn C.1 haxis with
    ⟨hwest, -, -, hnorth⟩
  have hwestProjection :=
    fkIsingSquareBoundaryLayerRadialCell_increment_eq_normSq_full_projection
      n hn C .west
  have hnorthProjection :=
    fkIsingSquareBoundaryLayerRadialCell_increment_eq_normSq_full_projection
      n hn C .north
  rw [hwest] at hwestProjection
  rw [hnorth] at hnorthProjection
  dsimp only [A, C, west, north] at hmacro ⊢
  unfold fkIsingSquareBoundaryLayerCoordinateOneForm
  rw [hmacro, hwestProjection, hnorthProjection]
  exact normSq_isingProj_one_sub_negI_eq_sq_mul_northwest_im _



theorem
    fkIsingSquareBoundaryLayer_coordinatePrimitive_odd_southeast_eq_sq_im
    (n : Nat) (hn : 0 < n) (q : Int × Int)
    (hq : FKIsingSquareFullDiamondCell n q)
    (hodd : ¬ Even (q.1 + q.2)) :
    let A := fkIsingSquareBoundaryLayerCoordinateOneForm n hn
    let C := fkIsingSquareFullRadialCellOfCoordinate n q hq
    A.coordinatePrimitive (q.1 + 1, q.2) -
        A.coordinatePrimitive (q.1, q.2 + 1) =
      ((fkIsingSquareBoundaryFullMedialObservable n hn C.1) ^ 2 *
        ((1 + Complex.I) / 2)).im := by
  let A := fkIsingSquareBoundaryLayerCoordinateOneForm n hn
  let C := fkIsingSquareFullRadialCellOfCoordinate n q hq
  have hmacro :=
    FKIsingSquareFullCoordinateOneForm.coordinatePrimitive_odd_southeast
      n hn (fkIsingSquareBoundaryLayerRadialIncrement n hn)
      (fkIsingSquareBoundaryLayerRadialCell_increment_closed n hn)
      q hq hodd
  have haxis := fkIsingSquareFullRadialCellOfCoordinate_axis_vertical
    n q hq hodd
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn C.1 haxis with
    ⟨hwest, -, -, hnorth⟩
  have hwestProjection :=
    fkIsingSquareBoundaryLayerRadialCell_increment_eq_normSq_full_projection
      n hn C .west
  have hnorthProjection :=
    fkIsingSquareBoundaryLayerRadialCell_increment_eq_normSq_full_projection
      n hn C .north
  rw [hwest] at hwestProjection
  rw [hnorth] at hnorthProjection
  dsimp only [A, C] at hmacro ⊢
  unfold fkIsingSquareBoundaryLayerCoordinateOneForm
  rw [hmacro, hwestProjection, hnorthProjection]
  exact normSq_isingProj_negI_sub_negOne_eq_sq_mul_northeast_im _

end

end StatMech.Universality
