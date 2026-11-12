/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerSwitching
import Code.Universality.IsingFermionicPhysicalFullSquareGenericIntegration









namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareFullOrientedRadialIncrementOf
    (n : Nat) (hn : 0 < n)
    (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real) :
    FKIsingSquareFullRadialNode n -> FKIsingSquareFullRadialNode n -> Real := by
  classical
  intro a b
  exact match a, b with
    | .inl x, .inr c =>
        if h : FKIsingSquareFullRadiallyAdjacent n x c then
          inc (fkIsingSquareFullIncidenceOfAdjacent n hn x c h)
        else 0
    | .inr c, .inl x =>
        if h : FKIsingSquareFullRadiallyAdjacent n x c then
          -inc (fkIsingSquareFullIncidenceOfAdjacent n hn x c h)
        else 0
    | _, _ => 0

@[simp] theorem fkIsingSquareFullOrientedRadialIncrementOf_incidence
    (n : Nat) (hn : 0 < n)
    (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    fkIsingSquareFullOrientedRadialIncrementOf n hn inc
        (.inl (fkIsingSquareInteriorRadialEndpoint n hn e))
        (.inr (fkIsingSquareFullFaceOfRadialIncidence n hn e)) = inc e := by
  rw [fkIsingSquareFullOrientedRadialIncrementOf]
  split
  · rw [fkIsingSquareFullIncidenceOfAdjacent_of_incidence n hn e]
  · rename_i h
    exact False.elim
      (h (fkIsingSquareFull_radiallyAdjacent_of_incidence n hn e))

@[simp] theorem fkIsingSquareFullOrientedRadialIncrementOf_incidence_reverse
    (n : Nat) (hn : 0 < n)
    (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    fkIsingSquareFullOrientedRadialIncrementOf n hn inc
        (.inr (fkIsingSquareFullFaceOfRadialIncidence n hn e))
        (.inl (fkIsingSquareInteriorRadialEndpoint n hn e)) = -inc e := by
  rw [fkIsingSquareFullOrientedRadialIncrementOf]
  split
  · rw [fkIsingSquareFullIncidenceOfAdjacent_of_incidence n hn e]
  · rename_i h
    exact False.elim
      (h (fkIsingSquareFull_radiallyAdjacent_of_incidence n hn e))

noncomputable def fkIsingSquareFullHorizontalIncrementOf
    (n : Nat) (hn : 0 < n)
    (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real)
    (q : Int × Int) : Real :=
  fkIsingSquareFullOrientedRadialIncrementOf n hn inc
    (fkIsingSquareFullRadialNodeAtCoordinate n q)
    (fkIsingSquareFullRadialNodeAtCoordinate n (q.1 + 1, q.2))

noncomputable def fkIsingSquareFullVerticalIncrementOf
    (n : Nat) (hn : 0 < n)
    (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real)
    (q : Int × Int) : Real :=
  fkIsingSquareFullOrientedRadialIncrementOf n hn inc
    (fkIsingSquareFullRadialNodeAtCoordinate n q)
    (fkIsingSquareFullRadialNodeAtCoordinate n (q.1, q.2 + 1))

theorem fkIsingSquareFull_increment_closed_of
    (n : Nat) (hn : 0 < n)
    (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real)
    (hinc : forall C : FKIsingSquareInteriorRadialCell n,
      inc (fkIsingSquareInteriorRadialCellIncidence n hn C .west) +
          inc (fkIsingSquareInteriorRadialCellIncidence n hn C .east) =
        inc (fkIsingSquareInteriorRadialCellIncidence n hn C .south) +
          inc (fkIsingSquareInteriorRadialCellIncidence n hn C .north))
    (q : Int × Int) (hq : FKIsingSquareFullDiamondCell n q) :
    fkIsingSquareFullVerticalIncrementOf n hn inc q +
        fkIsingSquareFullHorizontalIncrementOf n hn inc (q.1, q.2 + 1) =
      fkIsingSquareFullHorizontalIncrementOf n hn inc q +
        fkIsingSquareFullVerticalIncrementOf n hn inc (q.1 + 1, q.2) := by
  let C := fkIsingSquareFullRadialCellOfCoordinate n q hq
  let west := fkIsingSquareInteriorRadialCellIncidence n hn C .west
  let east := fkIsingSquareInteriorRadialCellIncidence n hn C .east
  let south := fkIsingSquareInteriorRadialCellIncidence n hn C .south
  let north := fkIsingSquareInteriorRadialCellIncidence n hn C .north
  have hclosed := hinc C
  by_cases heven : Even (q.1 + q.2)
  · have hw := fkIsingSquareFullRadialCellOfCoordinate_even_side_coordinates
      n hn q hq heven .west
    have he := fkIsingSquareFullRadialCellOfCoordinate_even_side_coordinates
      n hn q hq heven .east
    have hs := fkIsingSquareFullRadialCellOfCoordinate_even_side_coordinates
      n hn q hq heven .south
    have hnorth := fkIsingSquareFullRadialCellOfCoordinate_even_side_coordinates
      n hn q hq heven .north
    change fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn west = q ∧
      fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn west =
        (q.1 + 1, q.2) at hw
    change fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn east =
        (q.1 + 1, q.2 + 1) ∧
      fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn east =
        (q.1, q.2 + 1) at he
    change fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn south = q ∧
      fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn south =
        (q.1, q.2 + 1) at hs
    change fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn north =
        (q.1 + 1, q.2 + 1) ∧
      fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn north =
        (q.1 + 1, q.2) at hnorth
    have nqW := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n q hq.1
      (fkIsingSquareInteriorRadialEndpoint n hn west) hw.1
    have neW := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n
      (q.1 + 1, q.2) hq.2.1
      (fkIsingSquareFullFaceOfRadialIncidence n hn west) hw.2
    have nnE := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n
      (q.1, q.2 + 1) hq.2.2.1
      (fkIsingSquareFullFaceOfRadialIncidence n hn east) he.2
    have nneE := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n
      (q.1 + 1, q.2 + 1) hq.2.2.2
      (fkIsingSquareInteriorRadialEndpoint n hn east) he.1
    have nqS := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n q hq.1
      (fkIsingSquareInteriorRadialEndpoint n hn south) hs.1
    have nnS := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n
      (q.1, q.2 + 1) hq.2.2.1
      (fkIsingSquareFullFaceOfRadialIncidence n hn south) hs.2
    have neN := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n
      (q.1 + 1, q.2) hq.2.1
      (fkIsingSquareFullFaceOfRadialIncidence n hn north) hnorth.2
    have nneN := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n
      (q.1 + 1, q.2 + 1) hq.2.2.2
      (fkIsingSquareInteriorRadialEndpoint n hn north) hnorth.1
    have hH0 : fkIsingSquareFullHorizontalIncrementOf n hn inc q = inc west := by
      simp [fkIsingSquareFullHorizontalIncrementOf, nqW, neW]
    have hH1 : fkIsingSquareFullHorizontalIncrementOf n hn inc
        (q.1, q.2 + 1) = -inc east := by
      simp [fkIsingSquareFullHorizontalIncrementOf, nnE, nneE]
    have hV0 : fkIsingSquareFullVerticalIncrementOf n hn inc q = inc south := by
      simp [fkIsingSquareFullVerticalIncrementOf, nqS, nnS]
    have hV1 : fkIsingSquareFullVerticalIncrementOf n hn inc
        (q.1 + 1, q.2) = -inc north := by
      simp [fkIsingSquareFullVerticalIncrementOf, neN, nneN]
    rw [hH0, hH1, hV0, hV1]
    change _ + _ = _ + _ at hclosed
    linarith
  · have hw := fkIsingSquareFullRadialCellOfCoordinate_odd_side_coordinates
      n hn q hq heven .west
    have he := fkIsingSquareFullRadialCellOfCoordinate_odd_side_coordinates
      n hn q hq heven .east
    have hs := fkIsingSquareFullRadialCellOfCoordinate_odd_side_coordinates
      n hn q hq heven .south
    have hnorth := fkIsingSquareFullRadialCellOfCoordinate_odd_side_coordinates
      n hn q hq heven .north
    change fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn west =
        (q.1, q.2 + 1) ∧
      fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn west = q at hw
    change fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn east =
        (q.1 + 1, q.2) ∧
      fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn east =
        (q.1 + 1, q.2 + 1) at he
    change fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn south =
        (q.1, q.2 + 1) ∧
      fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn south =
        (q.1 + 1, q.2 + 1) at hs
    change fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn north =
        (q.1 + 1, q.2) ∧
      fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn north = q at hnorth
    have nnW := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n
      (q.1, q.2 + 1) hq.2.2.1
      (fkIsingSquareInteriorRadialEndpoint n hn west) hw.1
    have nqW := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n q hq.1
      (fkIsingSquareFullFaceOfRadialIncidence n hn west) hw.2
    have neE := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n
      (q.1 + 1, q.2) hq.2.1
      (fkIsingSquareInteriorRadialEndpoint n hn east) he.1
    have nneE := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n
      (q.1 + 1, q.2 + 1) hq.2.2.2
      (fkIsingSquareFullFaceOfRadialIncidence n hn east) he.2
    have nnS := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n
      (q.1, q.2 + 1) hq.2.2.1
      (fkIsingSquareInteriorRadialEndpoint n hn south) hs.1
    have nneS := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n
      (q.1 + 1, q.2 + 1) hq.2.2.2
      (fkIsingSquareFullFaceOfRadialIncidence n hn south) hs.2
    have neN := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n
      (q.1 + 1, q.2) hq.2.1
      (fkIsingSquareInteriorRadialEndpoint n hn north) hnorth.1
    have nqN := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n q hq.1
      (fkIsingSquareFullFaceOfRadialIncidence n hn north) hnorth.2
    have hH0 : fkIsingSquareFullHorizontalIncrementOf n hn inc q = -inc north := by
      simp [fkIsingSquareFullHorizontalIncrementOf, nqN, neN]
    have hH1 : fkIsingSquareFullHorizontalIncrementOf n hn inc
        (q.1, q.2 + 1) = inc south := by
      simp [fkIsingSquareFullHorizontalIncrementOf, nnS, nneS]
    have hV0 : fkIsingSquareFullVerticalIncrementOf n hn inc q = -inc west := by
      simp [fkIsingSquareFullVerticalIncrementOf, nqW, nnW]
    have hV1 : fkIsingSquareFullVerticalIncrementOf n hn inc
        (q.1 + 1, q.2) = inc east := by
      simp [fkIsingSquareFullVerticalIncrementOf, neE, nneE]
    rw [hH0, hH1, hV0, hV1]
    change _ + _ = _ + _ at hclosed
    linarith


noncomputable def fkIsingSquareFullCoordinateOneFormOf
    (n : Nat) (hn : 0 < n)
    (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real)
    (hinc : forall C : FKIsingSquareInteriorRadialCell n,
      inc (fkIsingSquareInteriorRadialCellIncidence n hn C .west) +
          inc (fkIsingSquareInteriorRadialCellIncidence n hn C .east) =
        inc (fkIsingSquareInteriorRadialCellIncidence n hn C .south) +
          inc (fkIsingSquareInteriorRadialCellIncidence n hn C .north)) :
    FKIsingSquareFullCoordinateOneForm n where
  horizontal := fkIsingSquareFullHorizontalIncrementOf n hn
    inc
  vertical := fkIsingSquareFullVerticalIncrementOf n hn
    inc
  closed := fkIsingSquareFull_increment_closed_of n hn inc hinc


noncomputable def fkIsingSquareBoundaryLayerCoordinateOneForm
    (n : Nat) (hn : 0 < n) : FKIsingSquareFullCoordinateOneForm n :=
  fkIsingSquareFullCoordinateOneFormOf n hn
    (fkIsingSquareBoundaryLayerRadialIncrement n hn)
    (fkIsingSquareBoundaryLayerRadialCell_increment_closed n hn)



theorem fkIsingSquareFullCoordinateOneFormOf_face_sub_vertex
    (n : Nat) (hn : 0 < n)
    (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real)
    (hinc : forall C : FKIsingSquareInteriorRadialCell n,
      inc (fkIsingSquareInteriorRadialCellIncidence n hn C .west) +
          inc (fkIsingSquareInteriorRadialCellIncidence n hn C .east) =
        inc (fkIsingSquareInteriorRadialCellIncidence n hn C .south) +
          inc (fkIsingSquareInteriorRadialCellIncidence n hn C .north))
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    let A := fkIsingSquareFullCoordinateOneFormOf n hn inc hinc
    A.facePrimitive (fkIsingSquareFullFaceOfRadialIncidence n hn e) -
        A.vertexPrimitive (fkIsingSquareInteriorRadialEndpoint n hn e) =
      inc e := by
  let A := fkIsingSquareFullCoordinateOneFormOf n hn inc hinc
  let x := fkIsingSquareInteriorRadialEndpoint n hn e
  let c := fkIsingSquareFullFaceOfRadialIncidence n hn e
  let u := fkIsingSquareFullVertexCoordinate n x
  let p := fkIsingSquareFullFaceCoordinate n c
  have hu : FKIsingSquareFullDiamond n u := by
    simpa [u, x, fkIsingSquareFullRadialNodeCoordinate] using
      fkIsingSquareFullRadialNodeCoordinate_mem_diamond n
        (Sum.inl x : FKIsingSquareFullRadialNode n)
  have hp : FKIsingSquareFullDiamond n p := by
    simpa [p, c, fkIsingSquareFullRadialNodeCoordinate] using
      fkIsingSquareFullRadialNodeCoordinate_mem_diamond n
        (Sum.inr c : FKIsingSquareFullRadialNode n)
  have hxu := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n u hu x rfl
  have hcp := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n p hp c rfl
  have hadj := fkIsingSquareFull_radiallyAdjacent_of_incidence n hn e
  change p = (u.1 + 1, u.2) ∨ p = (u.1, u.2 + 1) ∨
      p = (u.1 - 1, u.2) ∨ p = (u.1, u.2 - 1) at hadj
  rcases hadj with hE | hN | hW | hS
  · have h := A.coordinatePrimitive_horizontal_increment u hu
    have hcu : fkIsingSquareFullRadialNodeAtCoordinate n (u.1 + 1, u.2) =
        .inr c := by simpa [hE] using hcp
    have hgap : A.horizontal u = inc e := by
      change fkIsingSquareFullHorizontalIncrementOf n hn inc u = inc e
      unfold fkIsingSquareFullHorizontalIncrementOf
      rw [hxu, hcu]
      exact fkIsingSquareFullOrientedRadialIncrementOf_incidence n hn inc e
    simp only [FKIsingSquareFullCoordinateOneForm.vertexPrimitive,
      FKIsingSquareFullCoordinateOneForm.facePrimitive]
    change (A.coordinatePrimitive p - A.coordinatePrimitive
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) -
      (A.coordinatePrimitive u - A.coordinatePrimitive
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) = _
    rw [hE]
    linarith
  · have h := A.coordinatePrimitive_vertical_increment u hu (hN ▸ hp)
    have hcu : fkIsingSquareFullRadialNodeAtCoordinate n (u.1, u.2 + 1) =
        .inr c := by simpa [hN] using hcp
    have hgap : A.vertical u = inc e := by
      change fkIsingSquareFullVerticalIncrementOf n hn inc u = inc e
      unfold fkIsingSquareFullVerticalIncrementOf
      rw [hxu, hcu]
      exact fkIsingSquareFullOrientedRadialIncrementOf_incidence n hn inc e
    simp only [FKIsingSquareFullCoordinateOneForm.vertexPrimitive,
      FKIsingSquareFullCoordinateOneForm.facePrimitive]
    change (A.coordinatePrimitive p - A.coordinatePrimitive
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) -
      (A.coordinatePrimitive u - A.coordinatePrimitive
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) = _
    rw [hN]
    linarith
  · have hW0 := congrArg Prod.fst hW
    have hW1 := congrArg Prod.snd hW
    have hu' : u = (p.1 + 1, p.2) := by
      apply Prod.ext <;> omega
    have h := A.coordinatePrimitive_horizontal_increment p hp
    have hup : fkIsingSquareFullRadialNodeAtCoordinate n (p.1 + 1, p.2) =
        .inl x := by simpa [hu'] using hxu
    have hgap : A.horizontal p = -inc e := by
      change fkIsingSquareFullHorizontalIncrementOf n hn inc p = -inc e
      unfold fkIsingSquareFullHorizontalIncrementOf
      rw [hcp, hup]
      exact fkIsingSquareFullOrientedRadialIncrementOf_incidence_reverse
        n hn inc e
    simp only [FKIsingSquareFullCoordinateOneForm.vertexPrimitive,
      FKIsingSquareFullCoordinateOneForm.facePrimitive]
    change (A.coordinatePrimitive p - A.coordinatePrimitive
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) -
      (A.coordinatePrimitive u - A.coordinatePrimitive
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) = _
    rw [hu']
    linarith
  · have hS0 := congrArg Prod.fst hS
    have hS1 := congrArg Prod.snd hS
    have hu' : u = (p.1, p.2 + 1) := by
      apply Prod.ext <;> omega
    have h := A.coordinatePrimitive_vertical_increment p hp (hu' ▸ hu)
    have hup : fkIsingSquareFullRadialNodeAtCoordinate n (p.1, p.2 + 1) =
        .inl x := by simpa [hu'] using hxu
    have hgap : A.vertical p = -inc e := by
      change fkIsingSquareFullVerticalIncrementOf n hn inc p = -inc e
      unfold fkIsingSquareFullVerticalIncrementOf
      rw [hcp, hup]
      exact fkIsingSquareFullOrientedRadialIncrementOf_incidence_reverse
        n hn inc e
    simp only [FKIsingSquareFullCoordinateOneForm.vertexPrimitive,
      FKIsingSquareFullCoordinateOneForm.facePrimitive]
    change (A.coordinatePrimitive p - A.coordinatePrimitive
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) -
      (A.coordinatePrimitive u - A.coordinatePrimitive
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) = _
    rw [hu']
    linarith

theorem fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (fkIsingSquareFullFaceOfRadialIncidence n hn e) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareInteriorRadialEndpoint n hn e) =
      fkIsingSquareBoundaryLayerRadialIncrement n hn e := by
  exact fkIsingSquareFullCoordinateOneFormOf_face_sub_vertex n hn
    (fkIsingSquareBoundaryLayerRadialIncrement n hn)
    (fkIsingSquareBoundaryLayerRadialCell_increment_closed n hn) e

theorem fkIsingSquareBoundaryLayerCoordinateOneForm_vertex_le_face
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareInteriorRadialEndpoint n hn e) <=
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (fkIsingSquareFullFaceOfRadialIncidence n hn e) := by
  have hgap := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex
    n hn e
  have hnonneg := fkIsingSquareBoundaryLayerRadialIncrement_nonneg n hn e
  linarith

theorem fkIsingSquareBoundaryLayerRadialIncrement_perimeterInterior
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareBoundaryLayerRadialIncrement n hn
        (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k) =
      fkIsingSquareBoundaryLayerInwardIncrement n hn side k := by
  change Complex.normSq
      ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterInteriorSide side))) = _
  rw [<- fkIsingSquareBoundaryLayerInwardSide_eq_interiorSide]
  rfl



theorem fkIsingSquareBoundaryLayerCoordinateOneForm_boundary_face_sub_vertex
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (fkIsingSquareFullFaceOfRadialIncidence n hn
            (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k)) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareBoundaryVertex n (side, k)) =
      fkIsingSquareBoundaryLayerInwardIncrement n hn side k := by
  rw [<- fkIsingSquarePerimeterInteriorRadialEndpoint n hn side k,
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex,
    fkIsingSquareBoundaryLayerRadialIncrement_perimeterInterior]

theorem fkIsingSquareBoundaryLayerCoordinateOneForm_boundary_vertex_le_face
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareBoundaryVertex n (side, k)) <=
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (fkIsingSquareFullFaceOfRadialIncidence n hn
          (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k)) := by
  have hgap :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_boundary_face_sub_vertex
      n hn side k
  have hnonneg := fkIsingSquareBoundaryLayerInwardIncrement_nonneg
    n hn side k
  linarith

end

end StatMech.Universality
