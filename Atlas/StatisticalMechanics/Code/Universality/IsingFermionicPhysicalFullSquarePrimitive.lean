/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalFullSquareGhost











open SimpleGraph

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem isingRectanglePrimitiveWithBase_eq_of_local_increments
    (base : Real) (horizontal vertical G : Nat → Nat → Real)
    (width height : Nat)
    (hbase : G 0 0 = base)
    (hhorizontal : ∀ i < width, G (i + 1) 0 - G i 0 = horizontal i 0)
    (hvertical : ∀ i ≤ width, ∀ j < height,
      G i (j + 1) - G i j = vertical i j) :
    ∀ i ≤ width, ∀ j ≤ height,
      G i j = base + isingRectanglePrimitive horizontal vertical i j := by
  have hbottom : ∀ i ≤ width,
      G i 0 = base + ∑ k ∈ Finset.range i, horizontal k 0 := by
    intro i hi
    induction i with
    | zero => simpa using hbase
    | succ i ih =>
        rw [Finset.sum_range_succ]
        have hinc := hhorizontal i (by omega)
        have hprev := ih (by omega)
        linarith
  intro i hi j hj
  induction j with
  | zero =>
      simpa [isingRectanglePrimitive] using hbottom i hi
  | succ j ih =>
      rw [isingRectanglePrimitive, Finset.sum_range_succ]
      have hinc := hvertical i hi j (by omega)
      have hprev := ih (by omega)
      rw [isingRectanglePrimitive] at hprev
      linarith

theorem fkIsingSquareRadialPatchHorizontal_endpoint_of_even
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m)
    (heven : Even (i + j)) :
    fkIsingSquareInteriorRadialEndpoint n hn
        (fkIsingSquareRadialPatchHorizontalIncidence
          n m hn hm hmpos i j) =
      fkIsingSquareRadialPatchPrimalFullVertex n m hm
        ⟨(⟨i, by omega⟩, ⟨j, hj⟩), heven⟩ := by
  rw [fkIsingSquareRadialPatchHorizontalIncidence_bottom
    n m hn hm hmpos i j (by omega) hj]
  simp only [fkIsingSquareRadialPatchIncidence,
    fkIsingSquareInteriorRadialCellIncidence,
    fkIsingSquareInteriorRadialEndpoint_mk]
  rw [show fkIsingSquareRadialPatchBottomSide i j = .west by
    simp [fkIsingSquareRadialPatchBottomSide, heven]]
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareRadialPatchEdge n m hm ⟨i, by omega⟩ ⟨j, hj⟩,
        .west) = _
  rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ heven]
  change _ = fkIsingSquareRadialPatchVertex n m hm ⟨i, by omega⟩ ⟨j, hj⟩
  simp [fkIsingSquareSideCorner]

theorem fkIsingSquareRadialPatchHorizontal_face_of_even
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m)
    (heven : Even (i + j)) :
    fkIsingSquareFullFaceOfRadialIncidence n hn
        (fkIsingSquareRadialPatchHorizontalIncidence
          n m hn hm hmpos i j) =
      fkIsingSquareRadialPatchDualFullFace n m hm (by omega)
        ⟨(⟨i + 1, hi⟩, ⟨j, hj⟩), by
          change ¬ Even ((i + 1) + j)
          rw [Nat.not_even_iff]
          have hmod := Nat.even_iff.mp heven
          omega⟩ := by
  apply fkIsingSquareInteriorCellKey_injective n
  rw [fkIsingSquareFullFaceOfRadialIncidence_key,
    fkIsingSquareRadialPatchDualFullFace_key]
  rw [fkIsingSquareRadialPatchHorizontalIncidence_bottom
    n m hn hm hmpos i j (by omega) hj]
  simp only [fkIsingSquareRadialPatchIncidence,
    fkIsingSquareInteriorRadialCellIncidence,
    fkIsingSquareInteriorRadialFaceKey_mk]
  rw [show fkIsingSquareRadialPatchBottomSide i j = .west by
    simp [fkIsingSquareRadialPatchBottomSide, heven]]
  change fkIsingSquareWedgeFaceKey n
      (fkIsingSquareRadialPatchEdge n m hm ⟨i, by omega⟩ ⟨j, hj⟩,
        .west) = _
  rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ heven]
  unfold fkIsingSquareWedgeFaceKey fkIsingSquareDartEndpoint
    fkIsingSquareDartDirection
  rw [fkIsingSquareOrientedEdge_directionEdge]
  have hmod := Nat.even_iff.mp heven
  simp [fkIsingSquareDirectionEdgeOrientation,
    fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
    fkIsingSquareRadialPatchVertex, fkIsingSquareSideCorner]
  rw [fkIsingSquareRadialPatchHalf_eq]
  constructor <;> push_cast <;> omega

theorem fkIsingSquareRadialPatchHorizontal_endpoint_of_odd
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m)
    (hodd : ¬ Even (i + j)) :
    fkIsingSquareInteriorRadialEndpoint n hn
        (fkIsingSquareRadialPatchHorizontalIncidence
          n m hn hm hmpos i j) =
      fkIsingSquareRadialPatchPrimalFullVertex n m hm
        ⟨(⟨i + 1, hi⟩, ⟨j, hj⟩), by
          change Even ((i + 1) + j)
          rw [Nat.even_iff]
          have hmod := Nat.not_even_iff.mp hodd
          omega⟩ := by
  rw [fkIsingSquareRadialPatchHorizontalIncidence_bottom
    n m hn hm hmpos i j (by omega) hj]
  simp only [fkIsingSquareRadialPatchIncidence,
    fkIsingSquareInteriorRadialCellIncidence,
    fkIsingSquareInteriorRadialEndpoint_mk]
  rw [show fkIsingSquareRadialPatchBottomSide i j = .north by
    simp [fkIsingSquareRadialPatchBottomSide, hodd]]
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareRadialPatchEdge n m hm ⟨i, by omega⟩ ⟨j, hj⟩,
        .north) = _
  rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hodd]
  simp only [fkIsingSquareDartEndpoint_directionEdge_north]
  simp only [fkIsingSquareSideCorner]
  change _ = fkIsingSquareRadialPatchVertex n m hm ⟨i + 1, hi⟩ ⟨j, hj⟩
  change fkIsingSquareNeighbor n
      (fkIsingSquareRadialPatchVertex n m hm ⟨i, by omega⟩ ⟨j, hj⟩)
        .north _ =
    fkIsingSquareRadialPatchVertex n m hm ⟨i + 1, hi⟩ ⟨j, hj⟩
  have hmod := Nat.not_even_iff.mp hodd
  apply Subtype.ext
  funext k
  fin_cases k <;>
    simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf_eq] <;>
    omega

theorem fkIsingSquareRadialPatchHorizontal_face_of_odd
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m)
    (hodd : ¬ Even (i + j)) :
    fkIsingSquareFullFaceOfRadialIncidence n hn
        (fkIsingSquareRadialPatchHorizontalIncidence
          n m hn hm hmpos i j) =
      fkIsingSquareRadialPatchDualFullFace n m hm (by omega)
        ⟨(⟨i, by omega⟩, ⟨j, hj⟩), hodd⟩ := by
  apply fkIsingSquareInteriorCellKey_injective n
  rw [fkIsingSquareFullFaceOfRadialIncidence_key,
    fkIsingSquareRadialPatchDualFullFace_key]
  rw [fkIsingSquareRadialPatchHorizontalIncidence_bottom
    n m hn hm hmpos i j (by omega) hj]
  simp only [fkIsingSquareRadialPatchIncidence,
    fkIsingSquareInteriorRadialCellIncidence,
    fkIsingSquareInteriorRadialFaceKey_mk]
  rw [show fkIsingSquareRadialPatchBottomSide i j = .north by
    simp [fkIsingSquareRadialPatchBottomSide, hodd]]
  change fkIsingSquareWedgeFaceKey n
      (fkIsingSquareRadialPatchEdge n m hm ⟨i, by omega⟩ ⟨j, hj⟩,
        .north) = _
  rw [fkIsingSquareRadialPatchWedgeFaceKey_of_odd n m hm _ _ hodd]
  rw [fkIsingSquareRadialPatchHalf_eq]
  simp

theorem fkIsingSquareRadialPatchVertical_endpoint_of_even
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m)
    (heven : Even (i + j)) :
    fkIsingSquareInteriorRadialEndpoint n hn
        (fkIsingSquareRadialPatchVerticalIncidence
          n m hn hm hmpos i j) =
      fkIsingSquareRadialPatchPrimalFullVertex n m hm
        ⟨(⟨i, hi⟩, ⟨j, by omega⟩), heven⟩ := by
  rw [fkIsingSquareRadialPatchVerticalIncidence_left
    n m hn hm hmpos i j hi (by omega)]
  simp only [fkIsingSquareRadialPatchIncidence,
    fkIsingSquareInteriorRadialCellIncidence,
    fkIsingSquareInteriorRadialEndpoint_mk]
  rw [show fkIsingSquareRadialPatchLeftSide i j = .south by
    simp [fkIsingSquareRadialPatchLeftSide, heven]]
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, by omega⟩,
        .south) = _
  rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ heven]
  change _ = fkIsingSquareRadialPatchVertex n m hm ⟨i, hi⟩ ⟨j, by omega⟩
  simp [fkIsingSquareSideCorner]

theorem fkIsingSquareRadialPatchVertical_face_of_even
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m)
    (heven : Even (i + j)) :
    fkIsingSquareFullFaceOfRadialIncidence n hn
        (fkIsingSquareRadialPatchVerticalIncidence
          n m hn hm hmpos i j) =
      fkIsingSquareRadialPatchDualFullFace n m hm (by omega)
        ⟨(⟨i, hi⟩, ⟨j + 1, hj⟩), by
          change ¬ Even (i + (j + 1))
          rw [Nat.not_even_iff]
          have hmod := Nat.even_iff.mp heven
          omega⟩ := by
  apply fkIsingSquareInteriorCellKey_injective n
  rw [fkIsingSquareFullFaceOfRadialIncidence_key,
    fkIsingSquareRadialPatchDualFullFace_key]
  rw [fkIsingSquareRadialPatchVerticalIncidence_left
    n m hn hm hmpos i j hi (by omega)]
  simp only [fkIsingSquareRadialPatchIncidence,
    fkIsingSquareInteriorRadialCellIncidence,
    fkIsingSquareInteriorRadialFaceKey_mk]
  rw [show fkIsingSquareRadialPatchLeftSide i j = .south by
    simp [fkIsingSquareRadialPatchLeftSide, heven]]
  change fkIsingSquareWedgeFaceKey n
      (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, by omega⟩,
        .south) = _
  rw [fkIsingSquareRadialPatchWedgeFaceKey_of_even n m hm _ _ heven]
  rw [fkIsingSquareRadialPatchHalf_eq]
  have hmod := Nat.even_iff.mp heven
  simp
  constructor <;> push_cast <;> omega

theorem fkIsingSquareRadialPatchVertical_endpoint_of_odd
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m)
    (hodd : ¬ Even (i + j)) :
    fkIsingSquareInteriorRadialEndpoint n hn
        (fkIsingSquareRadialPatchVerticalIncidence
          n m hn hm hmpos i j) =
      fkIsingSquareRadialPatchPrimalFullVertex n m hm
        ⟨(⟨i, hi⟩, ⟨j + 1, hj⟩), by
          change Even (i + (j + 1))
          rw [Nat.even_iff]
          have hmod := Nat.not_even_iff.mp hodd
          omega⟩ := by
  rw [fkIsingSquareRadialPatchVerticalIncidence_left
    n m hn hm hmpos i j hi (by omega)]
  simp only [fkIsingSquareRadialPatchIncidence,
    fkIsingSquareInteriorRadialCellIncidence,
    fkIsingSquareInteriorRadialEndpoint_mk]
  rw [show fkIsingSquareRadialPatchLeftSide i j = .west by
    simp [fkIsingSquareRadialPatchLeftSide, hodd]]
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, by omega⟩,
        .west) = _
  rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hodd]
  simp only [fkIsingSquareDartEndpoint_directionEdge_north]
  simp only [fkIsingSquareSideCorner]
  change _ = fkIsingSquareRadialPatchVertex n m hm ⟨i, hi⟩ ⟨j + 1, hj⟩
  change fkIsingSquareRadialPatchVertex n m hm ⟨i, hi⟩ ⟨j, by omega⟩ =
    fkIsingSquareRadialPatchVertex n m hm ⟨i, hi⟩ ⟨j + 1, hj⟩
  have hmod := Nat.not_even_iff.mp hodd
  apply Subtype.ext
  funext k
  fin_cases k <;>
    simp [fkIsingSquareRadialPatchVertex,
      fkIsingSquareRadialPatchHalf_eq] <;>
    omega

theorem fkIsingSquareRadialPatchVertical_face_of_odd
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m)
    (hodd : ¬ Even (i + j)) :
    fkIsingSquareFullFaceOfRadialIncidence n hn
        (fkIsingSquareRadialPatchVerticalIncidence
          n m hn hm hmpos i j) =
      fkIsingSquareRadialPatchDualFullFace n m hm (by omega)
        ⟨(⟨i, hi⟩, ⟨j, by omega⟩), hodd⟩ := by
  apply fkIsingSquareInteriorCellKey_injective n
  rw [fkIsingSquareFullFaceOfRadialIncidence_key,
    fkIsingSquareRadialPatchDualFullFace_key]
  rw [fkIsingSquareRadialPatchVerticalIncidence_left
    n m hn hm hmpos i j hi (by omega)]
  simp only [fkIsingSquareRadialPatchIncidence,
    fkIsingSquareInteriorRadialCellIncidence,
    fkIsingSquareInteriorRadialFaceKey_mk]
  rw [show fkIsingSquareRadialPatchLeftSide i j = .west by
    simp [fkIsingSquareRadialPatchLeftSide, hodd]]
  change fkIsingSquareWedgeFaceKey n
      (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, by omega⟩,
        .west) = _
  rw [fkIsingSquareRadialPatchWedgeFaceKey_of_odd n m hm _ _ hodd]
  rw [fkIsingSquareRadialPatchHalf_eq]
  simp

def FKIsingSquareFullPrimitiveCompatible
    (n : Nat) (hn : 0 < n)
    (vertexH : FKIsingSquareFullVertexNode n → Real)
    (faceH : FKIsingSquareFullFaceNode n → Real) : Prop :=
  ∀ e : FKIsingSquareInteriorRadialIncidence n hn,
    faceH (fkIsingSquareFullFaceOfRadialIncidence n hn e) -
        vertexH (fkIsingSquareInteriorRadialEndpoint n hn e) =
      fkIsingSquareInteriorRadialIncrement n hn e

def fkIsingSquareRadialPatchFullValue
    (n m : Nat) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (vertexH : FKIsingSquareFullVertexNode n → Real)
    (faceH : FKIsingSquareFullFaceNode n → Real)
    (i j : Fin m) : Real :=
  if h : Even (i.1 + j.1) then
    vertexH (fkIsingSquareRadialPatchPrimalFullVertex n m hm
      ⟨(i, j), h⟩)
  else
    faceH (fkIsingSquareRadialPatchDualFullFace n m hm hm2
      ⟨(i, j), h⟩)

theorem fkIsingSquareRadialPatchFullValue_horizontal_increment
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (vertexH : FKIsingSquareFullVertexNode n → Real)
    (faceH : FKIsingSquareFullFaceNode n → Real)
    (hcompatible : FKIsingSquareFullPrimitiveCompatible n hn vertexH faceH)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m) :
    fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH
          ⟨i + 1, hi⟩ ⟨j, hj⟩ -
        fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH
          ⟨i, by omega⟩ ⟨j, hj⟩ =
      fkIsingSquareRadialPatchHorizontalSignedIncrement
        n m hn hm (by omega) i j := by
  let e := fkIsingSquareRadialPatchHorizontalIncidence
    n m hn hm (by omega) i j
  have hc := hcompatible e
  by_cases heven : Even (i + j)
  · have hnext : ¬ Even ((i + 1) + j) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    rw [fkIsingSquareRadialPatchHorizontal_face_of_even
        n m hn hm (by omega) i j hi hj heven,
      fkIsingSquareRadialPatchHorizontal_endpoint_of_even
        n m hn hm (by omega) i j hi hj heven] at hc
    simpa [fkIsingSquareRadialPatchFullValue, heven, hnext,
      fkIsingSquareRadialPatchHorizontalSignedIncrement, e] using hc
  · have hnext : Even ((i + 1) + j) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    rw [fkIsingSquareRadialPatchHorizontal_face_of_odd
        n m hn hm (by omega) i j hi hj heven,
      fkIsingSquareRadialPatchHorizontal_endpoint_of_odd
        n m hn hm (by omega) i j hi hj heven] at hc
    simp only [fkIsingSquareRadialPatchFullValue, hnext, heven,
      dite_true, dite_false,
      fkIsingSquareRadialPatchHorizontalSignedIncrement, if_false]
    change _ = -fkIsingSquareInteriorRadialIncrement n hn e
    linarith

theorem fkIsingSquareRadialPatchFullValue_vertical_increment
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (vertexH : FKIsingSquareFullVertexNode n → Real)
    (faceH : FKIsingSquareFullFaceNode n → Real)
    (hcompatible : FKIsingSquareFullPrimitiveCompatible n hn vertexH faceH)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m) :
    fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH
          ⟨i, hi⟩ ⟨j + 1, hj⟩ -
        fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH
          ⟨i, hi⟩ ⟨j, by omega⟩ =
      fkIsingSquareRadialPatchVerticalSignedIncrement
        n m hn hm (by omega) i j := by
  let e := fkIsingSquareRadialPatchVerticalIncidence
    n m hn hm (by omega) i j
  have hc := hcompatible e
  by_cases heven : Even (i + j)
  · have hnext : ¬ Even (i + (j + 1)) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    rw [fkIsingSquareRadialPatchVertical_face_of_even
        n m hn hm (by omega) i j hi hj heven,
      fkIsingSquareRadialPatchVertical_endpoint_of_even
        n m hn hm (by omega) i j hi hj heven] at hc
    simpa [fkIsingSquareRadialPatchFullValue, heven, hnext,
      fkIsingSquareRadialPatchVerticalSignedIncrement, e] using hc
  · have hnext : Even (i + (j + 1)) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    rw [fkIsingSquareRadialPatchVertical_face_of_odd
        n m hn hm (by omega) i j hi hj heven,
      fkIsingSquareRadialPatchVertical_endpoint_of_odd
        n m hn hm (by omega) i j hi hj heven] at hc
    simp only [fkIsingSquareRadialPatchFullValue, hnext, heven,
      dite_true, dite_false,
      fkIsingSquareRadialPatchVerticalSignedIncrement, if_false]
    change _ = -fkIsingSquareInteriorRadialIncrement n hn e
    linarith

private def fkIsingSquareRadialPatchFullValueNat
    (n m : Nat) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (vertexH : FKIsingSquareFullVertexNode n → Real)
    (faceH : FKIsingSquareFullFaceNode n → Real) : Nat → Nat → Real :=
  fun i j ↦
    if hi : i < m then
      if hj : j < m then
        fkIsingSquareRadialPatchFullValue
          n m hm hm2 vertexH faceH ⟨i, hi⟩ ⟨j, hj⟩
      else 0
    else 0

theorem fkIsingSquareRadialPatchFullValue_eq_primitive
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (base : Real)
    (vertexH : FKIsingSquareFullVertexNode n → Real)
    (faceH : FKIsingSquareFullFaceNode n → Real)
    (hcompatible : FKIsingSquareFullPrimitiveCompatible n hn vertexH faceH)
    (hbase : fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH
      ⟨0, by omega⟩ ⟨0, by omega⟩ = base) :
    ∀ i j : Fin m,
      fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH i j =
        base + fkIsingSquareRadialPatchPrimitive
          n m hn hm (by omega) i.1 j.1 := by
  let G := fkIsingSquareRadialPatchFullValueNat n m hm hm2 vertexH faceH
  have hGbase : G 0 0 = base := by
    have hmpos : 0 < m := by omega
    simpa [G, fkIsingSquareRadialPatchFullValueNat, hmpos] using hbase
  have hGh : ∀ i < m - 1, G (i + 1) 0 - G i 0 =
      fkIsingSquareRadialPatchHorizontalSignedIncrement
        n m hn hm (by omega) i 0 := by
    intro i hi
    have hi' : i + 1 < m := by omega
    have hi0 : i < m := by omega
    have hmpos : 0 < m := by omega
    have h := fkIsingSquareRadialPatchFullValue_horizontal_increment
      n m hn hm hm2 vertexH faceH hcompatible i 0 hi' (by omega)
    simpa [G, fkIsingSquareRadialPatchFullValueNat,
      hi', hi0, hmpos] using h
  have hGv : ∀ i ≤ m - 1, ∀ j < m - 1,
      G i (j + 1) - G i j =
        fkIsingSquareRadialPatchVerticalSignedIncrement
          n m hn hm (by omega) i j := by
    intro i hi j hj
    have hi' : i < m := by omega
    have hj' : j + 1 < m := by omega
    have hj0 : j < m := by omega
    have h := fkIsingSquareRadialPatchFullValue_vertical_increment
      n m hn hm hm2 vertexH faceH hcompatible i j hi' hj'
    simpa [G, fkIsingSquareRadialPatchFullValueNat,
      hi', hj', hj0] using h
  have hu := isingRectanglePrimitiveWithBase_eq_of_local_increments base
    (fkIsingSquareRadialPatchHorizontalSignedIncrement
      n m hn hm (by omega))
    (fkIsingSquareRadialPatchVerticalSignedIncrement
      n m hn hm (by omega)) G (m - 1) (m - 1) hGbase hGh hGv
  intro i j
  have hij := hu i.1 (by omega) j.1 (by omega)
  simpa [G, fkIsingSquareRadialPatchFullValueNat,
    fkIsingSquareRadialPatchPrimitive] using hij

theorem fkIsingSquareRadialPatchPrimalValue_eq_full_of_compatible
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (base : Real)
    (vertexH : FKIsingSquareFullVertexNode n → Real)
    (faceH : FKIsingSquareFullFaceNode n → Real)
    (hcompatible : FKIsingSquareFullPrimitiveCompatible n hn vertexH faceH)
    (hbase : fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH
      ⟨0, by omega⟩ ⟨0, by omega⟩ = base) :
    ∀ p : FKIsingSquareRadialPatchPrimalNode m,
      fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p =
        vertexH (fkIsingSquareRadialPatchPrimalFullVertex n m hm p) := by
  intro p
  have h := fkIsingSquareRadialPatchFullValue_eq_primitive
    n m hn hm hm2 base
    vertexH faceH hcompatible hbase p.1.1 p.1.2
  rw [show fkIsingSquareRadialPatchFullValue
      n m hm hm2 vertexH faceH p.1.1 p.1.2 =
      vertexH (fkIsingSquareRadialPatchPrimalFullVertex n m hm p) by
    simp [fkIsingSquareRadialPatchFullValue, p.2]] at h
  exact h.symm

theorem fkIsingSquareRadialPatchDualValue_eq_full_of_compatible
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (base : Real)
    (vertexH : FKIsingSquareFullVertexNode n → Real)
    (faceH : FKIsingSquareFullFaceNode n → Real)
    (hcompatible : FKIsingSquareFullPrimitiveCompatible n hn vertexH faceH)
    (hbase : fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH
      ⟨0, by omega⟩ ⟨0, by omega⟩ = base) :
    ∀ q : FKIsingSquareRadialPatchDualNode m,
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q =
        faceH (fkIsingSquareRadialPatchDualFullFace n m hm hm2 q) := by
  intro q
  have h := fkIsingSquareRadialPatchFullValue_eq_primitive
    n m hn hm hm2 base
    vertexH faceH hcompatible hbase q.1.1 q.1.2
  rw [show fkIsingSquareRadialPatchFullValue
      n m hm hm2 vertexH faceH q.1.1 q.1.2 =
      faceH (fkIsingSquareRadialPatchDualFullFace n m hm hm2 q) by
    simp [fkIsingSquareRadialPatchFullValue, q.2]] at h
  exact h.symm



theorem fkIsingSquareRadialPatch_unitRange_of_fullSquareGhost_compatible
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (base : Real)
    (vertexH : FKIsingSquareFullVertexNode n → Real)
    (faceH : FKIsingSquareFullFaceNode n → Real)
    (hvertexModified : ∀ x,
      ¬ fkIsingSquareFullVertexFixedBoundary n x →
        isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) vertexH x +
          isingFermionicGhostRate
            (fkIsingSquareFullVertexGhostMultiplicity n) x *
              (1 - vertexH x) ≤ 0)
    (hvertexFixed : ∀ x,
      fkIsingSquareFullVertexFixedBoundary n x → 0 ≤ vertexH x)
    (hfaceModified : ∀ c,
      ¬ fkIsingSquareFullFaceFixedBoundary n c →
        0 ≤ isingFiniteGraphLaplacian
          (fkIsingSquareFullFaceGraph n) faceH c +
            isingFermionicGhostRate
              (fkIsingSquareFullFaceGhostMultiplicity n) c *
                (0 - faceH c))
    (hfaceFixed : ∀ c,
      fkIsingSquareFullFaceFixedBoundary n c → faceH c ≤ 1)
    (hcompatible :
      FKIsingSquareFullPrimitiveCompatible n hn vertexH faceH)
    (hbase : fkIsingSquareRadialPatchFullValue
      n m hm hm2 vertexH faceH ⟨0, by omega⟩ ⟨0, by omega⟩ = base) :
    (∀ p, 0 ≤ fkIsingSquareRadialPatchPrimalValue
        n m hn hm (by omega) base p ∧
      fkIsingSquareRadialPatchPrimalValue
        n m hn hm (by omega) base p ≤ 1) ∧
      (∀ q, 0 ≤ fkIsingSquareRadialPatchDualValue
          n m hn hm (by omega) base q ∧
        fkIsingSquareRadialPatchDualValue
          n m hn hm (by omega) base q ≤ 1) := by
  apply fkIsingSquareRadialPatch_unitRange_of_fullSquareGhost
    n m hn hm hm2 base vertexH faceH hvertexModified hvertexFixed
      hfaceModified hfaceFixed
  · exact fkIsingSquareRadialPatchPrimalValue_eq_full_of_compatible
      n m hn hm hm2 base vertexH faceH hcompatible hbase
  · exact fkIsingSquareRadialPatchDualValue_eq_full_of_compatible
      n m hn hm hm2 base vertexH faceH hcompatible hbase

end

end StatMech.Universality
