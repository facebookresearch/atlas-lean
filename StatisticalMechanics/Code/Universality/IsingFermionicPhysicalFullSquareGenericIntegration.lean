/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive











namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section


structure FKIsingSquareFullCoordinateOneForm (n : Nat) where
  horizontal : Int × Int -> Real
  vertical : Int × Int -> Real
  closed : ∀ q, FKIsingSquareFullDiamondCell n q ->
    vertical q + horizontal (q.1, q.2 + 1) =
      horizontal q + vertical (q.1 + 1, q.2)

namespace FKIsingSquareFullCoordinateOneForm

noncomputable def horizontalNat {n : Nat}
    (A : FKIsingSquareFullCoordinateOneForm n) (i j : Nat) : Real :=
  A.horizontal (FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate n i j)

noncomputable def verticalNat {n : Nat}
    (A : FKIsingSquareFullCoordinateOneForm n) (i j : Nat) : Real :=
  A.vertical (FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate n i j)

noncomputable def primitiveNat {n : Nat}
    (A : FKIsingSquareFullCoordinateOneForm n) (i j : Nat) : Real :=
  isingCenteredPrimitive A.horizontalNat A.verticalNat (2 * n) i j

theorem primitiveNat_horizontal_increment {n : Nat}
    (A : FKIsingSquareFullCoordinateOneForm n) (i j : Nat) :
    A.primitiveNat (i + 1) j - A.primitiveNat i j =
      A.horizontalNat i j := by
  exact isingCenteredPrimitive_horizontal_increment
    A.horizontalNat A.verticalNat (2 * n) i j

theorem primitiveNat_vertical_increment {n : Nat}
    (A : FKIsingSquareFullCoordinateOneForm n) (i j : Nat)
    (h0 : FKIsingSquareFullDiamond n
      (FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate n i j))
    (h1 : FKIsingSquareFullDiamond n
      (FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate n i (j + 1))) :
    A.primitiveNat i (j + 1) - A.primitiveNat i j =
      A.verticalNat i j := by
  apply isingCenteredPrimitive_vertical_increment
  intro k hk
  have hcell := FKIsingSquareFullIntegratedPrimitive.diamondCell_of_row_interval
    n i j k h0 h1 hk
  let q := FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate n k j
  have hx : FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate
      n (k + 1) j = (q.1 + 1, q.2) := by
    apply Prod.ext <;>
      simp [q, FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate] <;>
      omega
  have hy : FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate
      n k (j + 1) = (q.1, q.2 + 1) := by
    apply Prod.ext <;>
      simp [q, FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate] <;>
      omega
  dsimp [horizontalNat, verticalNat]
  rw [hx, hy]
  exact A.closed q hcell

noncomputable def coordinatePrimitive {n : Nat}
    (A : FKIsingSquareFullCoordinateOneForm n) (q : Int × Int) : Real :=
  A.primitiveNat
    (FKIsingSquareFullIntegratedPrimitive.coordinateIndex n q).1
    (FKIsingSquareFullIntegratedPrimitive.coordinateIndex n q).2

theorem coordinatePrimitive_horizontal_increment {n : Nat}
    (A : FKIsingSquareFullCoordinateOneForm n) (q : Int × Int)
    (hq : FKIsingSquareFullDiamond n q) :
    A.coordinatePrimitive (q.1 + 1, q.2) - A.coordinatePrimitive q =
      A.horizontal q := by
  unfold coordinatePrimitive
  rw [FKIsingSquareFullIntegratedPrimitive.coordinateIndex_east n q hq]
  have h := A.primitiveNat_horizontal_increment
    (FKIsingSquareFullIntegratedPrimitive.coordinateIndex n q).1
    (FKIsingSquareFullIntegratedPrimitive.coordinateIndex n q).2
  simpa [horizontalNat,
    FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate_coordinateIndex
      n q hq] using h

theorem coordinatePrimitive_vertical_increment {n : Nat}
    (A : FKIsingSquareFullCoordinateOneForm n) (q : Int × Int)
    (hq : FKIsingSquareFullDiamond n q)
    (hqN : FKIsingSquareFullDiamond n (q.1, q.2 + 1)) :
    A.coordinatePrimitive (q.1, q.2 + 1) - A.coordinatePrimitive q =
      A.vertical q := by
  let ij := FKIsingSquareFullIntegratedPrimitive.coordinateIndex n q
  have hshift : FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate
      n ij.1 ij.2 = q :=
    FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate_coordinateIndex
      n q hq
  have hshiftN : FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate
      n ij.1 (ij.2 + 1) = (q.1, q.2 + 1) := by
    have hy : FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate
        n ij.1 (ij.2 + 1) =
      ((FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate
        n ij.1 ij.2).1,
       (FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate
        n ij.1 ij.2).2 + 1) := by
      apply Prod.ext <;>
        simp [FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate] <;>
        omega
    rw [hy, hshift]
  unfold coordinatePrimitive
  rw [FKIsingSquareFullIntegratedPrimitive.coordinateIndex_north n q hq]
  have h := A.primitiveNat_vertical_increment ij.1 ij.2
    (hshift ▸ hq) (hshiftN ▸ hqN)
  simpa [ij, verticalNat, hshift] using h

noncomputable def vertexPrimitive {n : Nat}
    (A : FKIsingSquareFullCoordinateOneForm n)
    (x : FKIsingSquareFullVertexNode n) : Real :=
  A.coordinatePrimitive (fkIsingSquareFullVertexCoordinate n x) -
    A.coordinatePrimitive
      (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))

noncomputable def facePrimitive {n : Nat}
    (A : FKIsingSquareFullCoordinateOneForm n)
    (c : FKIsingSquareFullFaceNode n) : Real :=
  A.coordinatePrimitive (fkIsingSquareFullFaceCoordinate n c) -
    A.coordinatePrimitive
      (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))

end FKIsingSquareFullCoordinateOneForm



noncomputable def fkIsingSquareFullBoxCoordinateOneForm
    (n : Nat) (hn : 0 < n) : FKIsingSquareFullCoordinateOneForm n where
  horizontal := fkIsingSquareFullHorizontalIncrement n hn
  vertical := fkIsingSquareFullVerticalIncrement n hn
  closed := fkIsingSquareFull_increment_closed n hn

theorem fkIsingSquareFullBoxCoordinateOneForm_coordinatePrimitive
    (n : Nat) (hn : 0 < n) (q : Int × Int) :
    (fkIsingSquareFullBoxCoordinateOneForm n hn).coordinatePrimitive q =
      FKIsingSquareFullIntegratedPrimitive.coordinatePrimitive n hn q := by
  rfl

theorem fkIsingSquareFullBoxCoordinateOneForm_vertexPrimitive
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareFullVertexNode n) :
    (fkIsingSquareFullBoxCoordinateOneForm n hn).vertexPrimitive x =
      FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn x := by
  rfl

theorem fkIsingSquareFullBoxCoordinateOneForm_facePrimitive
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n) :
    (fkIsingSquareFullBoxCoordinateOneForm n hn).facePrimitive c =
      FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn c := by
  rfl

end

end StatMech.Universality
