/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalRadialRectangle
import Code.Universality.IsingFermionicPhysicalDirichletLimit










namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD
open Filter Set Topology

noncomputable section

private def fkIsingSquareRadialPatchHalf (i j : Nat) : Nat :=
  (i + j + 1) / 2

theorem fkIsingSquareRadialPatchHalf_eq (i j : Nat) :
    fkIsingSquareRadialPatchHalf i j = (i + j + 1) / 2 := rfl

private theorem fkIsingSquareRadialPatchHalf_lt
    {n m : Nat} (hm : m ≤ n) (i j : Fin m) :
    fkIsingSquareRadialPatchHalf i.1 j.1 < n := by
  unfold fkIsingSquareRadialPatchHalf
  rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]
  have hi := i.2
  have hj := j.2
  omega


def fkIsingSquareRadialPatchVertex
    (n m : Nat) (hm : m ≤ n) (i j : Fin m) :
    (fkSquareBoxPlanar n).V := by
  let q := fkIsingSquareRadialPatchHalf i.1 j.1
  have hq : q < n := fkIsingSquareRadialPatchHalf_lt hm i j
  refine ⟨![(q : Int), (i.1 : Int) - (q : Int)], ?_⟩
  intro k
  fin_cases k
  · simpa using Nat.le_of_lt hq
  · exact Nat.le_trans
      (Int.natAbs_coe_sub_coe_lt_of_lt
        (lt_of_lt_of_le i.2 hm) hq).le
      (Nat.le_refl n)


def fkIsingSquareRadialPatchDirection (i j : Nat) :
    FKIsingSquareDirection :=
  if Even (i + j) then .east else .north

theorem fkIsingSquareRadialPatchDirection_available
    (n m : Nat) (hm : m ≤ n) (i j : Fin m) :
    fkIsingSquareDirectionAvailable n
      (fkIsingSquareRadialPatchVertex n m hm i j)
      (fkIsingSquareRadialPatchDirection i.1 j.1) := by
  have hi : i.1 < n := lt_of_lt_of_le i.2 hm
  have hq := fkIsingSquareRadialPatchHalf_lt hm i j
  by_cases heven : Even (i.1 + j.1)
  · simp [fkIsingSquareRadialPatchDirection, heven,
      fkIsingSquareDirectionAvailable, fkIsingSquareRadialPatchVertex]
    exact_mod_cast hq
  · simp [fkIsingSquareRadialPatchDirection, heven,
      fkIsingSquareDirectionAvailable, fkIsingSquareRadialPatchVertex]
    omega


def fkIsingSquareRadialPatchEdge
    (n m : Nat) (hm : m ≤ n) (i j : Fin m) :
    FKIsingMedialVertex (fkSquareBoxPlanar n) :=
  fkIsingSquareDirectionEdge n
    (fkIsingSquareRadialPatchVertex n m hm i j)
    (fkIsingSquareRadialPatchDirection i.1 j.1)
    (fkIsingSquareRadialPatchDirection_available n m hm i j)

@[simp] theorem fkIsingSquareRadialPatchEdge_orientation
    (n m : Nat) (hm : m ≤ n) (i j : Fin m) :
    fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm i j) =
      fkIsingSquareDirectionEdgeOrientation n
        (fkIsingSquareRadialPatchVertex n m hm i j)
        (fkIsingSquareRadialPatchDirection i.1 j.1)
        (fkIsingSquareRadialPatchDirection_available n m hm i j) :=
  fkIsingSquareOrientedEdge_directionEdge n _ _ _

theorem fkIsingSquareRadialPatchEdge_eq_east
    (n m : Nat) (hm : m ≤ n) (i j : Fin m)
    (heven : Even (i.1 + j.1)) :
    fkIsingSquareRadialPatchEdge n m hm i j =
      fkIsingSquareDirectionEdge n
        (fkIsingSquareRadialPatchVertex n m hm i j) .east
        (by simpa [fkIsingSquareRadialPatchDirection, heven] using
          fkIsingSquareRadialPatchDirection_available n m hm i j) := by
  unfold fkIsingSquareRadialPatchEdge
  simp only [fkIsingSquareRadialPatchDirection, if_pos heven]

theorem fkIsingSquareRadialPatchEdge_eq_north
    (n m : Nat) (hm : m ≤ n) (i j : Fin m)
    (hodd : ¬ Even (i.1 + j.1)) :
    fkIsingSquareRadialPatchEdge n m hm i j =
      fkIsingSquareDirectionEdge n
        (fkIsingSquareRadialPatchVertex n m hm i j) .north
        (by simpa [fkIsingSquareRadialPatchDirection, hodd] using
          fkIsingSquareRadialPatchDirection_available n m hm i j) := by
  unfold fkIsingSquareRadialPatchEdge
  simp only [fkIsingSquareRadialPatchDirection, if_neg hodd]

@[simp] theorem fkIsingSquareDartEndpoint_directionEdge_east
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (hu : fkIsingSquareDirectionAvailable n u .east)
    (s : FKIsingMedialSide) :
    fkIsingSquareDartEndpoint n
        (fkIsingSquareDirectionEdge n u .east hu, s) =
      match (fkIsingSquareSideCorner s).1 with
      | .tail => u
      | .head => fkIsingSquareNeighbor n u .east hu := by
  unfold fkIsingSquareDartEndpoint
  rw [fkIsingSquareOrientedEdge_directionEdge]
  cases s <;> rfl

@[simp] theorem fkIsingSquareDartDirection_directionEdge_east
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (hu : fkIsingSquareDirectionAvailable n u .east)
    (s : FKIsingMedialSide) :
    fkIsingSquareDartDirection n
        (fkIsingSquareDirectionEdge n u .east hu, s) =
      match (fkIsingSquareSideCorner s).1 with
      | .tail => .east
      | .head => .west := by
  unfold fkIsingSquareDartDirection
  rw [fkIsingSquareOrientedEdge_directionEdge]
  cases s <;> rfl

@[simp] theorem fkIsingSquareDartEndpoint_directionEdge_north
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (hu : fkIsingSquareDirectionAvailable n u .north)
    (s : FKIsingMedialSide) :
    fkIsingSquareDartEndpoint n
        (fkIsingSquareDirectionEdge n u .north hu, s) =
      match (fkIsingSquareSideCorner s).1 with
      | .tail => u
      | .head => fkIsingSquareNeighbor n u .north hu := by
  unfold fkIsingSquareDartEndpoint
  rw [fkIsingSquareOrientedEdge_directionEdge]
  cases s <;> rfl

@[simp] theorem fkIsingSquareDartDirection_directionEdge_north
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (hu : fkIsingSquareDirectionAvailable n u .north)
    (s : FKIsingMedialSide) :
    fkIsingSquareDartDirection n
        (fkIsingSquareDirectionEdge n u .north hu, s) =
      match (fkIsingSquareSideCorner s).1 with
      | .tail => .north
      | .head => .south := by
  unfold fkIsingSquareDartDirection
  rw [fkIsingSquareOrientedEdge_directionEdge]
  cases s <;> rfl

@[simp] theorem fkIsingSquareDartEndpoint_directionEdge_south
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (hu : fkIsingSquareDirectionAvailable n u .south)
    (s : FKIsingMedialSide) :
    fkIsingSquareDartEndpoint n
        (fkIsingSquareDirectionEdge n u .south hu, s) =
      match (fkIsingSquareSideCorner s).1 with
      | .tail => fkIsingSquareNeighbor n u .south hu
      | .head => u := by
  unfold fkIsingSquareDartEndpoint
  rw [fkIsingSquareOrientedEdge_directionEdge]
  cases s <;> rfl

@[simp] theorem fkIsingSquareDartDirection_directionEdge_south
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (hu : fkIsingSquareDirectionAvailable n u .south)
    (s : FKIsingMedialSide) :
    fkIsingSquareDartDirection n
        (fkIsingSquareDirectionEdge n u .south hu, s) =
      match (fkIsingSquareSideCorner s).1 with
      | .tail => .north
      | .head => .south := by
  unfold fkIsingSquareDartDirection
  rw [fkIsingSquareOrientedEdge_directionEdge]
  cases s <;> rfl

theorem fkIsingSquareRadialPatchWedgeFaceKey_of_even
    (n m : Nat) (hm : m ≤ n) (i j : Fin m)
    (heven : Even (i.1 + j.1)) (s : FKIsingMedialSide) :
    fkIsingSquareWedgeFaceKey n
        (fkIsingSquareRadialPatchEdge n m hm i j, s) =
      match s with
      | .west | .north =>
          ((fkIsingSquareRadialPatchHalf i.1 j.1 : Int),
            (i.1 : Int) - fkIsingSquareRadialPatchHalf i.1 j.1)
      | .east | .south =>
          ((fkIsingSquareRadialPatchHalf i.1 j.1 : Int),
            (i.1 : Int) - fkIsingSquareRadialPatchHalf i.1 j.1 - 1) := by
  rw [fkIsingSquareRadialPatchEdge_eq_east n m hm i j heven]
  unfold fkIsingSquareWedgeFaceKey fkIsingSquareDartEndpoint
    fkIsingSquareDartDirection
  rw [fkIsingSquareOrientedEdge_directionEdge]
  cases s <;>
    simp [fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareRadialPatchVertex, fkIsingSquareSideCorner]

theorem fkIsingSquareRadialPatchWedgeFaceKey_of_odd
    (n m : Nat) (hm : m ≤ n) (i j : Fin m)
    (hodd : ¬ Even (i.1 + j.1)) (s : FKIsingMedialSide) :
    fkIsingSquareWedgeFaceKey n
        (fkIsingSquareRadialPatchEdge n m hm i j, s) =
      match s with
      | .west | .north =>
          ((fkIsingSquareRadialPatchHalf i.1 j.1 : Int) - 1,
            (i.1 : Int) - fkIsingSquareRadialPatchHalf i.1 j.1)
      | .east | .south =>
          ((fkIsingSquareRadialPatchHalf i.1 j.1 : Int),
            (i.1 : Int) - fkIsingSquareRadialPatchHalf i.1 j.1) := by
  rw [fkIsingSquareRadialPatchEdge_eq_north n m hm i j hodd]
  unfold fkIsingSquareWedgeFaceKey fkIsingSquareDartEndpoint
    fkIsingSquareDartDirection
  rw [fkIsingSquareOrientedEdge_directionEdge]
  cases s <;>
    simp [fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareRadialPatchVertex, fkIsingSquareSideCorner]



def fkIsingSquareRadialPatchCell
    (n m : Nat) (hm : m ≤ n) (i j : Fin m) :
    FKIsingSquareInteriorRadialCell n := by
  refine ⟨fkIsingSquareRadialPatchEdge n m hm i j, ?_⟩
  intro s
  have hi : i.1 < n := lt_of_lt_of_le i.2 hm
  have hj : j.1 < n := lt_of_lt_of_le j.2 hm
  have hq := fkIsingSquareRadialPatchHalf_lt hm i j
  by_cases heven : Even (i.1 + j.1)
  · have hmod : (i.1 + j.1) % 2 = 0 := Nat.even_iff.mp heven
    rw [fkIsingSquareRadialPatchWedgeFaceKey_of_even n m hm i j heven s]
    cases s <;> simp [fkIsingSquareInteriorFaceKey] <;> omega
  · have hmod : (i.1 + j.1) % 2 = 1 := by
      exact Nat.not_even_iff.mp heven
    rw [fkIsingSquareRadialPatchWedgeFaceKey_of_odd n m hm i j heven s]
    cases s <;> simp [fkIsingSquareInteriorFaceKey] <;> omega



def fkIsingSquareRadialPatchRightSide (i j : Nat) : FKIsingMedialSide :=
  if Even (i + j) then .north else .east


def fkIsingSquareRadialPatchLeftSide (i j : Nat) : FKIsingMedialSide :=
  if Even (i + j) then .south else .west


def fkIsingSquareRadialPatchBottomSide (i j : Nat) : FKIsingMedialSide :=
  if Even (i + j) then .west else .north


def fkIsingSquareRadialPatchTopSide (i j : Nat) : FKIsingMedialSide :=
  if Even (i + j) then .east else .south

theorem fkIsingSquareRadialPatch_bondMate_right
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m) :
    fkIsingSquareBondMate n hn
        (fkIsingSquareRadialPatchEdge n m hm ⟨i, by omega⟩ ⟨j, hj⟩,
          fkIsingSquareRadialPatchRightSide i j) =
      (fkIsingSquareRadialPatchEdge n m hm ⟨i + 1, hi⟩ ⟨j, hj⟩,
        fkIsingSquareRadialPatchLeftSide (i + 1) j) := by
  let a : Fin m := ⟨i, by omega⟩
  let b : Fin m := ⟨i + 1, hi⟩
  let c : Fin m := ⟨j, hj⟩
  change fkIsingSquareBondMate n hn
      (fkIsingSquareRadialPatchEdge n m hm a c,
        fkIsingSquareRadialPatchRightSide i j) =
    (fkIsingSquareRadialPatchEdge n m hm b c,
      fkIsingSquareRadialPatchLeftSide (i + 1) j)
  have hq : fkIsingSquareRadialPatchHalf i j < n := by
    simpa [a, c] using fkIsingSquareRadialPatchHalf_lt hm a c
  have hq' : fkIsingSquareRadialPatchHalf (i + 1) j < n := by
    simpa [b, c] using fkIsingSquareRadialPatchHalf_lt hm b c
  have hx : (fkIsingSquareRadialPatchHalf i j : Int) < (n : Int) := by
    exact_mod_cast hq
  have hxlow : -(n : Int) < (fkIsingSquareRadialPatchHalf i j : Int) := by
    omega
  have hy : (i : Int) - fkIsingSquareRadialPatchHalf i j < (n : Int) := by
    have hin : i < n := by omega
    omega
  have hylow : -(n : Int) <
      (i : Int) - fkIsingSquareRadialPatchHalf i j := by omega
  have hx' : (fkIsingSquareRadialPatchHalf (i + 1) j : Int) < (n : Int) := by
    exact_mod_cast hq'
  have hxlow' : -(n : Int) <
      (fkIsingSquareRadialPatchHalf (i + 1) j : Int) := by omega
  have hy' : (i + 1 : Int) - fkIsingSquareRadialPatchHalf (i + 1) j <
      (n : Int) := by
    have hin : i + 1 < n := by omega
    omega
  have hylow' : -(n : Int) <
      (i + 1 : Int) - fkIsingSquareRadialPatchHalf (i + 1) j := by omega
  by_cases heven : Even (i + j)
  · have hnext : ¬ Even (i + 1 + j) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    have hcoord : 2 * fkIsingSquareRadialPatchHalf i j = i + j := by
      have hmod := Nat.even_iff.mp heven
      unfold fkIsingSquareRadialPatchHalf
      omega
    have hhalf : fkIsingSquareRadialPatchHalf (i + 1) j =
        fkIsingSquareRadialPatchHalf i j + 1 := by
      have hmod := Nat.even_iff.mp heven
      unfold fkIsingSquareRadialPatchHalf
      omega
    have hcoord' : 2 * fkIsingSquareRadialPatchHalf (i + 1) j =
        i + j + 2 := by omega
    rw [fkIsingSquareRadialPatchEdge_eq_east n m hm a c
        (by simpa [a, c] using heven),
      fkIsingSquareRadialPatchEdge_eq_north n m hm b c
        (by simpa [b, c, Nat.add_assoc] using hnext)]
    rw [show fkIsingSquareRadialPatchRightSide i j = .north by
      simp [fkIsingSquareRadialPatchRightSide, heven]]
    rw [show fkIsingSquareRadialPatchLeftSide (i + 1) j = .west by
      simp [fkIsingSquareRadialPatchLeftSide, hnext]]
    apply fkIsingSquareDart_key_injective n
    simp [fkIsingSquareBondMate, fkIsingSquareRadialPatchRightSide,
      heven, fkIsingSquareNextDirection,
      fkIsingSquarePreviousDirection, fkIsingSquareDirectionAvailable,
      fkIsingSquareRadialPatchVertex, a, b, c,
      fkIsingSquareDirectionDart, fkIsingSquareSideCorner,
      fkIsingSquareCornerSide,
      fkIsingSquareEndpointForDirection, fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite, hhalf,
      hx, hxlow, hy, hylow, hx', hxlow', hy', hylow']
  · have hnext : Even (i + 1 + j) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    have hcoord : 2 * fkIsingSquareRadialPatchHalf i j = i + j + 1 := by
      have hmod := Nat.not_even_iff.mp heven
      unfold fkIsingSquareRadialPatchHalf
      omega
    have hhalf : fkIsingSquareRadialPatchHalf (i + 1) j =
        fkIsingSquareRadialPatchHalf i j := by
      have hmod := Nat.not_even_iff.mp heven
      unfold fkIsingSquareRadialPatchHalf
      omega
    have hcoord' : 2 * fkIsingSquareRadialPatchHalf (i + 1) j =
        i + j + 1 := by omega
    rw [fkIsingSquareRadialPatchEdge_eq_north n m hm a c
        (by simpa [a, c] using heven),
      fkIsingSquareRadialPatchEdge_eq_east n m hm b c
        (by simpa [b, c, Nat.add_assoc] using hnext)]
    rw [show fkIsingSquareRadialPatchRightSide i j = .east by
      simp [fkIsingSquareRadialPatchRightSide, heven]]
    rw [show fkIsingSquareRadialPatchLeftSide (i + 1) j = .south by
      simp [fkIsingSquareRadialPatchLeftSide, hnext]]
    apply fkIsingSquareDart_key_injective n
    simp [fkIsingSquareBondMate, fkIsingSquareRadialPatchRightSide,
      heven, fkIsingSquareNextDirection,
      fkIsingSquarePreviousDirection, fkIsingSquareDirectionAvailable,
      fkIsingSquareRadialPatchVertex, a, b, c,
      fkIsingSquareDirectionDart, fkIsingSquareSideCorner,
      fkIsingSquareCornerSide,
      fkIsingSquareEndpointForDirection, fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite, hhalf,
      hx, hxlow, hy, hylow, hx', hxlow', hy', hylow']
    apply Subtype.ext
    funext k
    fin_cases k <;> simp <;> ring



def fkIsingSquareRadialPatchIncidence
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Fin m) (s : FKIsingMedialSide) :
    FKIsingSquareInteriorRadialIncidence n hn :=
  fkIsingSquareInteriorRadialCellIncidence n hn
    (fkIsingSquareRadialPatchCell n m hm i j) s

theorem fkIsingSquareRadialPatchIncidence_increment_eq_normSq_full_projection
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Fin m) (s : FKIsingMedialSide) :
    fkIsingSquareInteriorRadialIncrement n hn
        (fkIsingSquareRadialPatchIncidence n m hn hm i j s) =
      Complex.normSq
        (isingProj
          (fkIsingSquareWiredDirectedTangent n hn
            (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)))
          (fkIsingSquareWiredFullMedialObservable n hn
            (fkIsingSquareRadialPatchEdge n m hm i j))) := by
  exact fkIsingSquareInteriorRadialCell_increment_eq_normSq_full_projection
    n hn (fkIsingSquareRadialPatchCell n m hm i j) s


noncomputable def fkIsingSquareRadialPatchFullObservable
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (i j : Fin m) : Complex :=
  fkIsingSquareWiredFullMedialObservable n hn
    (fkIsingSquareRadialPatchEdge n m hm i j)

theorem fkIsingSquareRadialPatchFullObservable_projection
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Fin m) (s : FKIsingMedialSide) :
    isingProj
        (fkIsingSquareWiredDirectedTangent n hn
          (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)))
        (fkIsingSquareRadialPatchFullObservable n m hn hm i j) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)) := by
  exact fkIsingSquareWiredFullMedialObservable_projection n hn _ s



theorem fkIsingSquareRadialPatch_normSq_full_eq_bottom_add_top_increment
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (i j : Fin m) :
    Complex.normSq
        (fkIsingSquareRadialPatchFullObservable n m hn hm i j) =
      fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareRadialPatchIncidence n m hn hm i j
            (fkIsingSquareRadialPatchBottomSide i j)) +
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareRadialPatchIncidence n m hn hm i j
            (fkIsingSquareRadialPatchTopSide i j)) := by
  by_cases heven : Even (i.1 + j.1)
  · simpa [fkIsingSquareRadialPatchFullObservable,
      fkIsingSquareRadialPatchIncidence,
      fkIsingSquareInteriorRadialCellIncidence,
      fkIsingSquareRadialPatchBottomSide,
      fkIsingSquareRadialPatchTopSide, heven] using
      fkIsingSquareWired_normSq_full_eq_west_add_east_increment n hn
        (fkIsingSquareRadialPatchEdge n m hm i j)
  · simpa [fkIsingSquareRadialPatchFullObservable,
      fkIsingSquareRadialPatchIncidence,
      fkIsingSquareInteriorRadialCellIncidence,
      fkIsingSquareRadialPatchBottomSide,
      fkIsingSquareRadialPatchTopSide, heven, add_comm] using
      fkIsingSquareWired_normSq_full_eq_south_add_north_increment n hn
        (fkIsingSquareRadialPatchEdge n m hm i j)



theorem fkIsingSquareRadialPatch_normSq_full_eq_left_add_right_increment
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (i j : Fin m) :
    Complex.normSq
        (fkIsingSquareRadialPatchFullObservable n m hn hm i j) =
      fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareRadialPatchIncidence n m hn hm i j
            (fkIsingSquareRadialPatchLeftSide i j)) +
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareRadialPatchIncidence n m hn hm i j
            (fkIsingSquareRadialPatchRightSide i j)) := by
  by_cases heven : Even (i.1 + j.1)
  · simpa [fkIsingSquareRadialPatchFullObservable,
      fkIsingSquareRadialPatchIncidence,
      fkIsingSquareInteriorRadialCellIncidence,
      fkIsingSquareRadialPatchLeftSide,
      fkIsingSquareRadialPatchRightSide, heven] using
      fkIsingSquareWired_normSq_full_eq_south_add_north_increment n hn
        (fkIsingSquareRadialPatchEdge n m hm i j)
  · simpa [fkIsingSquareRadialPatchFullObservable,
      fkIsingSquareRadialPatchIncidence,
      fkIsingSquareInteriorRadialCellIncidence,
      fkIsingSquareRadialPatchLeftSide,
      fkIsingSquareRadialPatchRightSide, heven] using
      fkIsingSquareWired_normSq_full_eq_west_add_east_increment n hn
        (fkIsingSquareRadialPatchEdge n m hm i j)


theorem fkIsingSquareRadialPatchIncidence_right_eq_left
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m) :
    fkIsingSquareRadialPatchIncidence n m hn hm
        ⟨i, by omega⟩ ⟨j, hj⟩ (fkIsingSquareRadialPatchRightSide i j) =
      fkIsingSquareRadialPatchIncidence n m hn hm
        ⟨i + 1, hi⟩ ⟨j, hj⟩
        (fkIsingSquareRadialPatchLeftSide (i + 1) j) := by
  let a : Fin m := ⟨i, by omega⟩
  let b : Fin m := ⟨i + 1, hi⟩
  let c : Fin m := ⟨j, hj⟩
  let d : FKIsingSquareInteriorRadialDart n :=
    ⟨(fkIsingSquareRadialPatchEdge n m hm a c,
        fkIsingSquareRadialPatchRightSide i j),
      (fkIsingSquareRadialPatchCell n m hm a c).2 _⟩
  let e : FKIsingSquareInteriorRadialDart n :=
    ⟨(fkIsingSquareRadialPatchEdge n m hm b c,
        fkIsingSquareRadialPatchLeftSide (i + 1) j),
      (fkIsingSquareRadialPatchCell n m hm b c).2 _⟩
  change Quot.mk _ d = Quot.mk _ e
  apply Quot.sound
  have hstep : fkIsingSquareInteriorRadialBondPerm n hn d = e := by
    apply Subtype.ext
    change fkIsingSquareWiredBondMate n hn d.1 = e.1
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn d.1 d.2]
    exact fkIsingSquareRadialPatch_bondMate_right n m hn hm i j hi hj
  have hcycle :=
    (Equiv.Perm.SameCycle.rfl :
      (fkIsingSquareInteriorRadialBondPerm n hn).SameCycle d d).apply_right
  simpa only [hstep] using hcycle

theorem fkIsingSquareRadialPatch_bondMate_top
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m) :
    fkIsingSquareBondMate n hn
        (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, by omega⟩,
          fkIsingSquareRadialPatchTopSide i j) =
      (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j + 1, hj⟩,
        fkIsingSquareRadialPatchBottomSide i (j + 1)) := by
  let a : Fin m := ⟨i, hi⟩
  let b : Fin m := ⟨j, by omega⟩
  let c : Fin m := ⟨j + 1, hj⟩
  change fkIsingSquareBondMate n hn
      (fkIsingSquareRadialPatchEdge n m hm a b,
        fkIsingSquareRadialPatchTopSide i j) =
    (fkIsingSquareRadialPatchEdge n m hm a c,
      fkIsingSquareRadialPatchBottomSide i (j + 1))
  have hq : fkIsingSquareRadialPatchHalf i j < n := by
    simpa [a, b] using fkIsingSquareRadialPatchHalf_lt hm a b
  have hq' : fkIsingSquareRadialPatchHalf i (j + 1) < n := by
    simpa [a, c] using fkIsingSquareRadialPatchHalf_lt hm a c
  have hx : (fkIsingSquareRadialPatchHalf i j : Int) < (n : Int) := by
    exact_mod_cast hq
  have hxlow : -(n : Int) < (fkIsingSquareRadialPatchHalf i j : Int) := by
    omega
  have hy : (i : Int) - fkIsingSquareRadialPatchHalf i j < (n : Int) := by
    have hin : i < n := by omega
    omega
  have hylow : -(n : Int) <
      (i : Int) - fkIsingSquareRadialPatchHalf i j := by omega
  have hx' : (fkIsingSquareRadialPatchHalf i (j + 1) : Int) < (n : Int) := by
    exact_mod_cast hq'
  have hxlow' : -(n : Int) <
      (fkIsingSquareRadialPatchHalf i (j + 1) : Int) := by omega
  have hy' : (i : Int) - fkIsingSquareRadialPatchHalf i (j + 1) <
      (n : Int) := by
    have hin : i < n := by omega
    omega
  have hylow' : -(n : Int) <
      (i : Int) - fkIsingSquareRadialPatchHalf i (j + 1) := by omega
  by_cases heven : Even (i + j)
  · have hnext : ¬ Even (i + (j + 1)) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    have hhalf : fkIsingSquareRadialPatchHalf i (j + 1) =
        fkIsingSquareRadialPatchHalf i j + 1 := by
      have hmod := Nat.even_iff.mp heven
      unfold fkIsingSquareRadialPatchHalf
      omega
    rw [fkIsingSquareRadialPatchEdge_eq_east n m hm a b
        (by simpa [a, b] using heven),
      fkIsingSquareRadialPatchEdge_eq_north n m hm a c
        (by simpa [a, c, Nat.add_assoc] using hnext)]
    rw [show fkIsingSquareRadialPatchTopSide i j = .east by
      simp [fkIsingSquareRadialPatchTopSide, heven]]
    rw [show fkIsingSquareRadialPatchBottomSide i (j + 1) = .north by
      simp [fkIsingSquareRadialPatchBottomSide, hnext]]
    apply fkIsingSquareDart_key_injective n
    simp [fkIsingSquareBondMate, fkIsingSquareNextDirection,
      fkIsingSquarePreviousDirection, fkIsingSquareDirectionAvailable,
      fkIsingSquareRadialPatchVertex, a, b, c,
      fkIsingSquareDirectionDart, fkIsingSquareSideCorner,
      fkIsingSquareCornerSide, fkIsingSquareEndpointForDirection,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, hhalf,
      hx, hxlow, hy, hylow, hx', hxlow', hy', hylow']
    apply Subtype.ext
    funext k
    fin_cases k <;> simp <;> ring
  · have hnext : Even (i + (j + 1)) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    have hhalf : fkIsingSquareRadialPatchHalf i (j + 1) =
        fkIsingSquareRadialPatchHalf i j := by
      have hmod := Nat.not_even_iff.mp heven
      unfold fkIsingSquareRadialPatchHalf
      omega
    rw [fkIsingSquareRadialPatchEdge_eq_north n m hm a b
        (by simpa [a, b] using heven),
      fkIsingSquareRadialPatchEdge_eq_east n m hm a c
        (by simpa [a, c, Nat.add_assoc] using hnext)]
    rw [show fkIsingSquareRadialPatchTopSide i j = .south by
      simp [fkIsingSquareRadialPatchTopSide, heven]]
    rw [show fkIsingSquareRadialPatchBottomSide i (j + 1) = .west by
      simp [fkIsingSquareRadialPatchBottomSide, hnext]]
    apply fkIsingSquareDart_key_injective n
    simp [fkIsingSquareBondMate, fkIsingSquareNextDirection,
      fkIsingSquarePreviousDirection, fkIsingSquareDirectionAvailable,
      fkIsingSquareRadialPatchVertex, a, b, c,
      fkIsingSquareDirectionDart, fkIsingSquareSideCorner,
      fkIsingSquareCornerSide, fkIsingSquareEndpointForDirection,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, hhalf,
      hx, hxlow, hy, hylow, hx', hxlow', hy', hylow']



theorem fkIsingSquareRadialPatch_directedTangentCode_right_modEq
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m) :
    fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareRadialPatchEdge n m hm ⟨i + 1, hi⟩ ⟨j, hj⟩,
          fkIsingSquareRadialPatchLeftSide (i + 1) j)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareRadialPatchEdge n m hm ⟨i, by omega⟩ ⟨j, hj⟩,
          fkIsingSquareRadialPatchRightSide i j)) [ZMOD 8] := by
  by_cases heven : Even (i + j)
  · have hnext : ¬ Even (i + 1 + j) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    have haxisD : (fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm ⟨i, by omega⟩ ⟨j, hj⟩)).axis =
        .horizontal := by
      rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ heven,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    have haxisF : (fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm ⟨i + 1, hi⟩ ⟨j, hj⟩)).axis =
        .vertical := by
      rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hnext,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    rcases fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
      n hn _ haxisD with ⟨_, _, _, hD⟩
    rcases fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
      n hn _ haxisF with ⟨hF, _, _, _⟩
    simp [fkIsingSquareRadialPatchRightSide, fkIsingSquareRadialPatchLeftSide,
      heven, hnext, hD, hF, Int.ModEq]
  · have hnext : Even (i + 1 + j) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    have haxisD : (fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm ⟨i, by omega⟩ ⟨j, hj⟩)).axis =
        .vertical := by
      rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ heven,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    have haxisF : (fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm ⟨i + 1, hi⟩ ⟨j, hj⟩)).axis =
        .horizontal := by
      rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ hnext,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    rcases fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
      n hn _ haxisD with ⟨_, hD, _, _⟩
    rcases fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
      n hn _ haxisF with ⟨_, _, hF, _⟩
    simp [fkIsingSquareRadialPatchRightSide, fkIsingSquareRadialPatchLeftSide,
      heven, hnext, hD, hF]



theorem fkIsingSquareRadialPatch_directedTangentCode_top_modEq
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m) :
    fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j + 1, hj⟩,
          fkIsingSquareRadialPatchBottomSide i (j + 1))) ≡
      fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, by omega⟩,
          fkIsingSquareRadialPatchTopSide i j)) [ZMOD 8] := by
  by_cases heven : Even (i + j)
  · have hnext : ¬ Even (i + (j + 1)) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    have haxisD : (fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, by omega⟩)).axis =
        .horizontal := by
      rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ heven,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    have haxisF : (fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j + 1, hj⟩)).axis =
        .vertical := by
      rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hnext,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    rcases fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
      n hn _ haxisD with ⟨_, hD, _, _⟩
    rcases fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
      n hn _ haxisF with ⟨_, _, _, hF⟩
    simp [fkIsingSquareRadialPatchTopSide, fkIsingSquareRadialPatchBottomSide,
      heven, hnext, hD, hF, Int.ModEq]
  · have hnext : Even (i + (j + 1)) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    have haxisD : (fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, by omega⟩)).axis =
        .vertical := by
      rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ heven,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    have haxisF : (fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j + 1, hj⟩)).axis =
        .horizontal := by
      rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ hnext,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    rcases fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
      n hn _ haxisD with ⟨_, _, hD, _⟩
    rcases fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
      n hn _ haxisF with ⟨hF, _, _, _⟩
    simp [fkIsingSquareRadialPatchTopSide, fkIsingSquareRadialPatchBottomSide,
      heven, hnext, hD, hF, Int.ModEq]



theorem fkIsingSquareRadialPatch_fermionicObservable_right_eq_left
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareRadialPatchEdge n m hm ⟨i, by omega⟩ ⟨j, hj⟩,
          fkIsingSquareRadialPatchRightSide i j)) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareRadialPatchEdge n m hm ⟨i + 1, hi⟩ ⟨j, hj⟩,
          fkIsingSquareRadialPatchLeftSide (i + 1) j)) := by
  let a : Fin m := ⟨i, by omega⟩
  let b : Fin m := ⟨i + 1, hi⟩
  let c : Fin m := ⟨j, hj⟩
  let d : FKIsingSquareInteriorRadialDart n :=
    ⟨(fkIsingSquareRadialPatchEdge n m hm a c,
        fkIsingSquareRadialPatchRightSide i j),
      (fkIsingSquareRadialPatchCell n m hm a c).2 _⟩
  have hcode : fkIsingSquareWiredDirectedTangentCode n hn
      (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
    change fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn d.1 d.2,
      fkIsingSquareRadialPatch_bondMate_right n m hn hm i j hi hj]
    exact fkIsingSquareRadialPatch_directedTangentCode_right_modEq
      n m hn hm i j hi hj
  have hobs :=
    fkIsingSquareInteriorRadial_fermionicObservable_bondMate_eq_of_code_modEq
      n hn d hcode
  change (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart d.1) at hobs
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn d.1 d.2,
    fkIsingSquareRadialPatch_bondMate_right n m hn hm i j hi hj] at hobs
  simpa only [a, b, c, d] using hobs.symm


theorem fkIsingSquareRadialPatch_fermionicObservable_top_eq_bottom
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, by omega⟩,
          fkIsingSquareRadialPatchTopSide i j)) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j + 1, hj⟩,
          fkIsingSquareRadialPatchBottomSide i (j + 1))) := by
  let a : Fin m := ⟨i, hi⟩
  let b : Fin m := ⟨j, by omega⟩
  let c : Fin m := ⟨j + 1, hj⟩
  let d : FKIsingSquareInteriorRadialDart n :=
    ⟨(fkIsingSquareRadialPatchEdge n m hm a b,
        fkIsingSquareRadialPatchTopSide i j),
      (fkIsingSquareRadialPatchCell n m hm a b).2 _⟩
  have hcode : fkIsingSquareWiredDirectedTangentCode n hn
      (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
    change fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn d.1 d.2,
      fkIsingSquareRadialPatch_bondMate_top n m hn hm i j hi hj]
    exact fkIsingSquareRadialPatch_directedTangentCode_top_modEq
      n m hn hm i j hi hj
  have hobs :=
    fkIsingSquareInteriorRadial_fermionicObservable_bondMate_eq_of_code_modEq
      n hn d hcode
  change (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart d.1) at hobs
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn d.1 d.2,
    fkIsingSquareRadialPatch_bondMate_top n m hn hm i j hi hj] at hobs
  simpa only [a, b, c, d] using hobs.symm



theorem fkIsingSquareRadialPatchFullObservable_quad
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j)) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i - 1, by omega⟩ ⟨j, by omega⟩)
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩)
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i, by omega⟩ ⟨j - 1, by omega⟩)
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i, by omega⟩ ⟨j, by omega⟩) := by
  have hoddN : ¬ Even (i + (j - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hoddS : ¬ Even (i - 1 + j) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hevenW : Even (i - 1 + (j - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hiSub : i - 1 + 1 = i := by omega
  have hjSub : j - 1 + 1 = j := by omega
  let eN := fkIsingSquareRadialPatchEdge n m hm
    ⟨i, by omega⟩ ⟨j - 1, by omega⟩
  let eE := fkIsingSquareRadialPatchEdge n m hm
    ⟨i, by omega⟩ ⟨j, by omega⟩
  let eS := fkIsingSquareRadialPatchEdge n m hm
    ⟨i - 1, by omega⟩ ⟨j, by omega⟩
  let eW := fkIsingSquareRadialPatchEdge n m hm
    ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .vertical := by
    rw [show eN = fkIsingSquareRadialPatchEdge n m hm
        ⟨i, by omega⟩ ⟨j - 1, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hoddN,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisE : (fkIsingSquareOrientedEdge n eE).axis = .horizontal := by
    rw [show eE = fkIsingSquareRadialPatchEdge n m hm
        ⟨i, by omega⟩ ⟨j, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ heven,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisS : (fkIsingSquareOrientedEdge n eS).axis = .vertical := by
    rw [show eS = fkIsingSquareRadialPatchEdge n m hm
        ⟨i - 1, by omega⟩ ⟨j, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hoddS,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .horizontal := by
    rw [show eW = fkIsingSquareRadialPatchEdge n m hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ hevenW,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eN haxisN with
    ⟨hNW, _, hNS, _⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eE haxisE with
    ⟨hEW, _, hES, _⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eS haxisS with
    ⟨_, hSE, _, hSN⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eW haxisW with
    ⟨_, hWE, _, hWN⟩
  have hNEobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .south)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .west)) := by
    simpa only [eN, eE, fkIsingSquareRadialPatchTopSide,
      fkIsingSquareRadialPatchBottomSide, hoddN, heven, if_false, if_true,
      hjSub] using fkIsingSquareRadialPatch_fermionicObservable_top_eq_bottom
        n m hn hm i (j - 1) (by omega) (by omega)
  have hESobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .south)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .east)) := by
    symm
    simpa only [eE, eS, fkIsingSquareRadialPatchRightSide,
      fkIsingSquareRadialPatchLeftSide, hoddS, heven, if_false, if_true,
      hiSub] using fkIsingSquareRadialPatch_fermionicObservable_right_eq_left
        n m hn hm (i - 1) j (by omega) (by omega)
  have hSWobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := by
    symm
    simpa only [eS, eW, fkIsingSquareRadialPatchTopSide,
      fkIsingSquareRadialPatchBottomSide, hevenW, hoddS, if_false, if_true,
      hjSub] using fkIsingSquareRadialPatch_fermionicObservable_top_eq_bottom
        n m hn hm (i - 1) (j - 1) (by omega) (by omega)
  have hWNobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .north)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .west)) := by
    simpa only [eW, eN, fkIsingSquareRadialPatchRightSide,
      fkIsingSquareRadialPatchLeftSide, hevenW, hoddN, if_false, if_true,
      hiSub] using fkIsingSquareRadialPatch_fermionicObservable_right_eq_left
        n m hn hm (i - 1) (j - 1) (by omega) (by omega)
  let north := fkIsingSquareRadialPatchFullObservable n m hn hm
    ⟨i, by omega⟩ ⟨j - 1, by omega⟩
  let east := fkIsingSquareRadialPatchFullObservable n m hn hm
    ⟨i, by omega⟩ ⟨j, by omega⟩
  let south := fkIsingSquareRadialPatchFullObservable n m hn hm
    ⟨i - 1, by omega⟩ ⟨j, by omega⟩
  let west := fkIsingSquareRadialPatchFullObservable n m hn hm
    ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
  change IsingSquareSHolomorphicQuad south west north east
  apply isingSquareSHolomorphicQuad_of_projection_cycle north east south west
  · change isingProj 1 north = isingProj 1 east
    calc
      isingProj 1 north = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .south)))
          north := by rw [hNS]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .south)) := by
        simpa only [north, eN] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i, by omega⟩ ⟨j - 1, by omega⟩ .south
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .west)) := hNEobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eE, .west)))
          east := by
        symm
        simpa only [east, eE] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i, by omega⟩ ⟨j, by omega⟩ .west
      _ = isingProj 1 east := by rw [hEW]
  · change isingProj Complex.I east = isingProj Complex.I south
    calc
      isingProj Complex.I east = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eE, .south)))
          east := by rw [hES]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .south)) := by
        simpa only [east, eE] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i, by omega⟩ ⟨j, by omega⟩ .south
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .east)) := hESobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .east)))
          south := by
        symm
        simpa only [south, eS] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i - 1, by omega⟩ ⟨j, by omega⟩ .east
      _ = isingProj Complex.I south := by rw [hSE]
  · change isingProj (-1) south = isingProj (-1) west
    calc
      isingProj (-1) south = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .north)))
          south := by rw [hSN]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) := by
        simpa only [south, eS] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i - 1, by omega⟩ ⟨j, by omega⟩ .north
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := hSWobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .east)))
          west := by
        symm
        simpa only [west, eW] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ .east
      _ = isingProj (-1) west := by rw [hWE]
  · change isingProj (-Complex.I) west = isingProj (-Complex.I) north
    calc
      isingProj (-Complex.I) west = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .north)))
          west := by rw [hWN]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .north)) := by
        simpa only [west, eW] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ .north
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .west)) := hWNobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .west)))
          north := by
        symm
        simpa only [north, eN] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i, by omega⟩ ⟨j - 1, by omega⟩ .west
      _ = isingProj (-Complex.I) north := by rw [hNW]



theorem fkIsingSquareRadialPatchFullObservable_quad_of_odd
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (hodd : ¬ Even (i + j)) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i, by omega⟩ ⟨j - 1, by omega⟩)
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i, by omega⟩ ⟨j, by omega⟩)
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i - 1, by omega⟩ ⟨j, by omega⟩)
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩) := by
  have hevenN : Even (i + (j - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hevenS : Even (i - 1 + j) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hoddW : ¬ Even (i - 1 + (j - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hiSub : i - 1 + 1 = i := by omega
  have hjSub : j - 1 + 1 = j := by omega
  let eN := fkIsingSquareRadialPatchEdge n m hm
    ⟨i, by omega⟩ ⟨j - 1, by omega⟩
  let eE := fkIsingSquareRadialPatchEdge n m hm
    ⟨i, by omega⟩ ⟨j, by omega⟩
  let eS := fkIsingSquareRadialPatchEdge n m hm
    ⟨i - 1, by omega⟩ ⟨j, by omega⟩
  let eW := fkIsingSquareRadialPatchEdge n m hm
    ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .horizontal := by
    rw [show eN = fkIsingSquareRadialPatchEdge n m hm
        ⟨i, by omega⟩ ⟨j - 1, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ hevenN,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisE : (fkIsingSquareOrientedEdge n eE).axis = .vertical := by
    rw [show eE = fkIsingSquareRadialPatchEdge n m hm
        ⟨i, by omega⟩ ⟨j, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hodd,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisS : (fkIsingSquareOrientedEdge n eS).axis = .horizontal := by
    rw [show eS = fkIsingSquareRadialPatchEdge n m hm
        ⟨i - 1, by omega⟩ ⟨j, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ hevenS,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .vertical := by
    rw [show eW = fkIsingSquareRadialPatchEdge n m hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hoddW,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eN haxisN with
    ⟨_, hNE, hNS, _⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eE haxisE with
    ⟨hEW, _, _, hEN⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eS haxisS with
    ⟨hSW, _, _, hSN⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eW haxisW with
    ⟨_, hWE, hWS, _⟩
  have hNEobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .east)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .north)) := by
    simpa only [eN, eE, fkIsingSquareRadialPatchTopSide,
      fkIsingSquareRadialPatchBottomSide, hevenN, hodd, if_false, if_true,
      hjSub] using fkIsingSquareRadialPatch_fermionicObservable_top_eq_bottom
        n m hn hm i (j - 1) (by omega) (by omega)
  have hESobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .west)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) := by
    symm
    simpa only [eE, eS, fkIsingSquareRadialPatchRightSide,
      fkIsingSquareRadialPatchLeftSide, hevenS, hodd, if_false, if_true,
      hiSub] using fkIsingSquareRadialPatch_fermionicObservable_right_eq_left
        n m hn hm (i - 1) j (by omega) (by omega)
  have hSWobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .west)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .south)) := by
    symm
    simpa only [eS, eW, fkIsingSquareRadialPatchTopSide,
      fkIsingSquareRadialPatchBottomSide, hoddW, hevenS, if_false, if_true,
      hjSub] using fkIsingSquareRadialPatch_fermionicObservable_top_eq_bottom
        n m hn hm (i - 1) (j - 1) (by omega) (by omega)
  have hWNobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .south)) := by
    simpa only [eW, eN, fkIsingSquareRadialPatchRightSide,
      fkIsingSquareRadialPatchLeftSide, hoddW, hevenN, if_false, if_true,
      hiSub] using fkIsingSquareRadialPatch_fermionicObservable_right_eq_left
        n m hn hm (i - 1) (j - 1) (by omega) (by omega)
  let north := fkIsingSquareRadialPatchFullObservable n m hn hm
    ⟨i, by omega⟩ ⟨j - 1, by omega⟩
  let east := fkIsingSquareRadialPatchFullObservable n m hn hm
    ⟨i, by omega⟩ ⟨j, by omega⟩
  let south := fkIsingSquareRadialPatchFullObservable n m hn hm
    ⟨i - 1, by omega⟩ ⟨j, by omega⟩
  let west := fkIsingSquareRadialPatchFullObservable n m hn hm
    ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
  change IsingSquareSHolomorphicQuad north east south west
  apply isingSquareSHolomorphicQuad_of_projection_cycle south west north east
  · calc
      isingProj 1 south = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .west)))
          south := by rw [hSW]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .west)) := by
        simpa only [south, eS] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i - 1, by omega⟩ ⟨j, by omega⟩ .west
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .south)) := hSWobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .south)))
          west := by
        symm
        simpa only [west, eW] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ .south
      _ = isingProj 1 west := by rw [hWS]
  · calc
      isingProj Complex.I west = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .east)))
          west := by rw [hWE]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := by
        simpa only [west, eW] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ .east
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .south)) := hWNobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .south)))
          north := by
        symm
        simpa only [north, eN] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i, by omega⟩ ⟨j - 1, by omega⟩ .south
      _ = isingProj Complex.I north := by rw [hNS]
  · calc
      isingProj (-1) north = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .east)))
          north := by rw [hNE]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .east)) := by
        simpa only [north, eN] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i, by omega⟩ ⟨j - 1, by omega⟩ .east
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .north)) := hNEobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eE, .north)))
          east := by
        symm
        simpa only [east, eE] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i, by omega⟩ ⟨j, by omega⟩ .north
      _ = isingProj (-1) east := by rw [hEN]
  · calc
      isingProj (-Complex.I) east = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eE, .west)))
          east := by rw [hEW]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .west)) := by
        simpa only [east, eE] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i, by omega⟩ ⟨j, by omega⟩ .west
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) := hESobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .north)))
          south := by
        symm
        simpa only [south, eS] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i - 1, by omega⟩ ⟨j, by omega⟩ .north
      _ = isingProj (-Complex.I) south := by rw [hSN]


theorem fkIsingSquareRadialPatchIncidence_top_eq_bottom
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m) :
    fkIsingSquareRadialPatchIncidence n m hn hm
        ⟨i, hi⟩ ⟨j, by omega⟩ (fkIsingSquareRadialPatchTopSide i j) =
      fkIsingSquareRadialPatchIncidence n m hn hm
        ⟨i, hi⟩ ⟨j + 1, hj⟩
        (fkIsingSquareRadialPatchBottomSide i (j + 1)) := by
  let a : Fin m := ⟨i, hi⟩
  let b : Fin m := ⟨j, by omega⟩
  let c : Fin m := ⟨j + 1, hj⟩
  let d : FKIsingSquareInteriorRadialDart n :=
    ⟨(fkIsingSquareRadialPatchEdge n m hm a b,
        fkIsingSquareRadialPatchTopSide i j),
      (fkIsingSquareRadialPatchCell n m hm a b).2 _⟩
  let e : FKIsingSquareInteriorRadialDart n :=
    ⟨(fkIsingSquareRadialPatchEdge n m hm a c,
        fkIsingSquareRadialPatchBottomSide i (j + 1)),
      (fkIsingSquareRadialPatchCell n m hm a c).2 _⟩
  change Quot.mk _ d = Quot.mk _ e
  apply Quot.sound
  have hstep : fkIsingSquareInteriorRadialBondPerm n hn d = e := by
    apply Subtype.ext
    change fkIsingSquareWiredBondMate n hn d.1 = e.1
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn d.1 d.2]
    exact fkIsingSquareRadialPatch_bondMate_top n m hn hm i j hi hj
  have hcycle :=
    (Equiv.Perm.SameCycle.rfl :
      (fkIsingSquareInteriorRadialBondPerm n hn).SameCycle d d).apply_right
  simpa only [hstep] using hcycle

private def fkIsingSquareRadialPatchZero (m : Nat) (hm : 0 < m) : Fin m :=
  ⟨0, hm⟩

private def fkIsingSquareRadialPatchLast (m : Nat) (hm : 0 < m) : Fin m :=
  ⟨m - 1, by omega⟩



def fkIsingSquareRadialPatchHorizontalIncidence
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m) :
    Nat → Nat → FKIsingSquareInteriorRadialIncidence n hn :=
  fun i j ↦
    if hi : i < m then
      if hj : j < m then
        fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩ ⟨j, hj⟩
          (fkIsingSquareRadialPatchBottomSide i j)
      else
        fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩
          (fkIsingSquareRadialPatchLast m hmpos)
          (fkIsingSquareRadialPatchTopSide i (m - 1))
    else
      fkIsingSquareRadialPatchIncidence n m hn hm
        (fkIsingSquareRadialPatchZero m hmpos)
        (fkIsingSquareRadialPatchZero m hmpos) .west



def fkIsingSquareRadialPatchVerticalIncidence
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m) :
    Nat → Nat → FKIsingSquareInteriorRadialIncidence n hn :=
  fun i j ↦
    if hj : j < m then
      if hi : i < m then
        fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩ ⟨j, hj⟩
          (fkIsingSquareRadialPatchLeftSide i j)
      else
        fkIsingSquareRadialPatchIncidence n m hn hm
          (fkIsingSquareRadialPatchLast m hmpos) ⟨j, hj⟩
          (fkIsingSquareRadialPatchRightSide (m - 1) j)
    else
      fkIsingSquareRadialPatchIncidence n m hn hm
        (fkIsingSquareRadialPatchZero m hmpos)
        (fkIsingSquareRadialPatchZero m hmpos) .west

theorem fkIsingSquareRadialPatchHorizontalIncidence_bottom
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j < m) :
    fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j =
      fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩ ⟨j, hj⟩
        (fkIsingSquareRadialPatchBottomSide i j) := by
  simp [fkIsingSquareRadialPatchHorizontalIncidence, hi, hj]

theorem fkIsingSquareRadialPatchHorizontalIncidence_top
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i : Nat) (hi : i < m) :
    fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i m =
      fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩
        (fkIsingSquareRadialPatchLast m hmpos)
        (fkIsingSquareRadialPatchTopSide i (m - 1)) := by
  simp [fkIsingSquareRadialPatchHorizontalIncidence, hi]

theorem fkIsingSquareRadialPatchVerticalIncidence_left
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j < m) :
    fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j =
      fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩ ⟨j, hj⟩
        (fkIsingSquareRadialPatchLeftSide i j) := by
  simp [fkIsingSquareRadialPatchVerticalIncidence, hi, hj]

theorem fkIsingSquareRadialPatchVerticalIncidence_right
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (j : Nat) (hj : j < m) :
    fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos m j =
      fkIsingSquareRadialPatchIncidence n m hn hm
        (fkIsingSquareRadialPatchLast m hmpos) ⟨j, hj⟩
        (fkIsingSquareRadialPatchRightSide (m - 1) j) := by
  simp [fkIsingSquareRadialPatchVerticalIncidence, hj]

theorem fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j < m) :
    fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i (j + 1) =
      fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩ ⟨j, hj⟩
        (fkIsingSquareRadialPatchTopSide i j) := by
  by_cases hnext : j + 1 < m
  · rw [fkIsingSquareRadialPatchHorizontalIncidence_bottom
      n m hn hm hmpos i (j + 1) hi hnext]
    exact (fkIsingSquareRadialPatchIncidence_top_eq_bottom
      n m hn hm i j hi hnext).symm
  · have heq : j + 1 = m := by omega
    subst m
    simpa [fkIsingSquareRadialPatchLast] using
      fkIsingSquareRadialPatchHorizontalIncidence_top
        n (j + 1) hn hm hmpos i hi

theorem fkIsingSquareRadialPatchVerticalIncidence_right_of_cell
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j < m) :
    fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos (i + 1) j =
      fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩ ⟨j, hj⟩
        (fkIsingSquareRadialPatchRightSide i j) := by
  by_cases hnext : i + 1 < m
  · rw [fkIsingSquareRadialPatchVerticalIncidence_left
      n m hn hm hmpos (i + 1) j hnext hj]
    exact (fkIsingSquareRadialPatchIncidence_right_eq_left
      n m hn hm i j hnext hj).symm
  · have heq : i + 1 = m := by omega
    subst m
    simpa [fkIsingSquareRadialPatchLast] using
      fkIsingSquareRadialPatchVerticalIncidence_right
        n (i + 1) hn hm hmpos j hj




def fkIsingSquareRadialPatchHorizontalSignedIncrement
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m) :
    Nat → Nat → Real :=
  fun i j ↦
    let x := fkIsingSquareInteriorRadialIncrement n hn
      (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j)
    if Even (i + j) then x else -x


def fkIsingSquareRadialPatchVerticalSignedIncrement
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m) :
    Nat → Nat → Real :=
  fun i j ↦
    let x := fkIsingSquareInteriorRadialIncrement n hn
      (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j)
    if Even (i + j) then x else -x



theorem fkIsingSquareRadialPatchSignedIncrement_closed_on
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m) :
    IsingRectangleClosedOneFormOn
      (fkIsingSquareRadialPatchHorizontalSignedIncrement n m hn hm hmpos)
      (fkIsingSquareRadialPatchVerticalSignedIncrement n m hn hm hmpos)
      m m := by
  intro i hi j hj
  have hbottom := congrArg (fkIsingSquareInteriorRadialIncrement n hn)
    (fkIsingSquareRadialPatchHorizontalIncidence_bottom
      n m hn hm hmpos i j hi hj)
  have htop := congrArg (fkIsingSquareInteriorRadialIncrement n hn)
    (fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell
      n m hn hm hmpos i j hi hj)
  have hleft := congrArg (fkIsingSquareInteriorRadialIncrement n hn)
    (fkIsingSquareRadialPatchVerticalIncidence_left
      n m hn hm hmpos i j hi hj)
  have hright := congrArg (fkIsingSquareInteriorRadialIncrement n hn)
    (fkIsingSquareRadialPatchVerticalIncidence_right_of_cell
      n m hn hm hmpos i j hi hj)
  have hcell := fkIsingSquareInteriorRadialCell_increment_closed n hn
    (fkIsingSquareRadialPatchCell n m hm ⟨i, hi⟩ ⟨j, hj⟩)
  change fkIsingSquareInteriorRadialIncrement n hn
        (fkIsingSquareRadialPatchIncidence n m hn hm
          ⟨i, hi⟩ ⟨j, hj⟩ .west) +
      fkIsingSquareInteriorRadialIncrement n hn
        (fkIsingSquareRadialPatchIncidence n m hn hm
          ⟨i, hi⟩ ⟨j, hj⟩ .east) =
    fkIsingSquareInteriorRadialIncrement n hn
        (fkIsingSquareRadialPatchIncidence n m hn hm
          ⟨i, hi⟩ ⟨j, hj⟩ .south) +
      fkIsingSquareInteriorRadialIncrement n hn
        (fkIsingSquareRadialPatchIncidence n m hn hm
          ⟨i, hi⟩ ⟨j, hj⟩ .north) at hcell
  by_cases heven : Even (i + j)
  · have htopOdd : ¬ Even (i + (j + 1)) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    have hrightOdd : ¬ Even (i + 1 + j) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    simp only [fkIsingSquareRadialPatchHorizontalSignedIncrement,
      fkIsingSquareRadialPatchVerticalSignedIncrement, heven, htopOdd,
      hrightOdd, if_true, if_false]
    rw [hbottom, htop, hleft, hright]
    simp only [fkIsingSquareRadialPatchBottomSide,
      fkIsingSquareRadialPatchTopSide, fkIsingSquareRadialPatchLeftSide,
      fkIsingSquareRadialPatchRightSide, heven, if_true]
    linarith
  · have htopEven : Even (i + (j + 1)) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    have hrightEven : Even (i + 1 + j) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    simp only [fkIsingSquareRadialPatchHorizontalSignedIncrement,
      fkIsingSquareRadialPatchVerticalSignedIncrement, heven, htopEven,
      hrightEven, if_true, if_false]
    rw [hbottom, htop, hleft, hright]
    simp only [fkIsingSquareRadialPatchBottomSide,
      fkIsingSquareRadialPatchTopSide, fkIsingSquareRadialPatchLeftSide,
      fkIsingSquareRadialPatchRightSide, heven, if_false]
    linarith


def fkIsingSquareRadialPatchPrimitive
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m) :
    Nat → Nat → Real :=
  isingRectanglePrimitive
    (fkIsingSquareRadialPatchHorizontalSignedIncrement n m hn hm hmpos)
    (fkIsingSquareRadialPatchVerticalSignedIncrement n m hn hm hmpos)

theorem fkIsingSquareRadialPatchPrimitive_horizontal_increment
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j ≤ m) :
    fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j -
        fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j =
      fkIsingSquareRadialPatchHorizontalSignedIncrement
        n m hn hm hmpos i j := by
  exact isingRectanglePrimitive_horizontal_increment_on _ _ m m
    (fkIsingSquareRadialPatchSignedIncrement_closed_on n m hn hm hmpos)
    i j hi hj

theorem fkIsingSquareRadialPatchPrimitive_vertical_increment
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) :
    fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1) -
        fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j =
      fkIsingSquareRadialPatchVerticalSignedIncrement
        n m hn hm hmpos i j := by
  exact isingRectanglePrimitive_vertical_increment _ _ i j



theorem fkIsingSquareRadialPatchPrimitive_abs_horizontal_sub_eq_increment
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j ≤ m) :
    |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j -
        fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| =
      fkIsingSquareInteriorRadialIncrement n hn
        (fkIsingSquareRadialPatchHorizontalIncidence
          n m hn hm hmpos i j) := by
  rw [fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos i j hi hj]
  have hnonneg := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j)
  by_cases heven : Even (i + j)
  · simp [fkIsingSquareRadialPatchHorizontalSignedIncrement,
      heven, abs_of_nonneg hnonneg]
  · simp [fkIsingSquareRadialPatchHorizontalSignedIncrement,
      heven, abs_of_nonneg hnonneg]



theorem fkIsingSquareRadialPatchPrimitive_abs_vertical_sub_eq_increment
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) :
    |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1) -
        fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| =
      fkIsingSquareInteriorRadialIncrement n hn
        (fkIsingSquareRadialPatchVerticalIncidence
          n m hn hm hmpos i j) := by
  rw [fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos i j]
  have hnonneg := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j)
  by_cases heven : Even (i + j)
  · simp [fkIsingSquareRadialPatchVerticalSignedIncrement,
      heven, abs_of_nonneg hnonneg]
  · simp [fkIsingSquareRadialPatchVerticalSignedIncrement,
      heven, abs_of_nonneg hnonneg]




theorem fkIsingSquareRadialPatch_two_mul_normSq_full_eq_cell_totalVariation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j < m) :
    2 * Complex.normSq
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i, hi⟩ ⟨j, hj⟩) =
      |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j -
          fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| +
        |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) (j + 1) -
          fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1)| +
        |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1) -
          fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| +
        |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) (j + 1) -
          fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j| := by
  have hbottom :=
    fkIsingSquareRadialPatchPrimitive_abs_horizontal_sub_eq_increment
      n m hn hm hmpos i j hi (by omega)
  have htop :=
    fkIsingSquareRadialPatchPrimitive_abs_horizontal_sub_eq_increment
      n m hn hm hmpos i (j + 1) hi (by omega)
  have hleft :=
    fkIsingSquareRadialPatchPrimitive_abs_vertical_sub_eq_increment
      n m hn hm hmpos i j
  have hright :=
    fkIsingSquareRadialPatchPrimitive_abs_vertical_sub_eq_increment
      n m hn hm hmpos (i + 1) j
  rw [fkIsingSquareRadialPatchHorizontalIncidence_bottom
      n m hn hm hmpos i j hi hj] at hbottom
  rw [fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell
      n m hn hm hmpos i j hi hj] at htop
  rw [fkIsingSquareRadialPatchVerticalIncidence_left
      n m hn hm hmpos i j hi hj] at hleft
  rw [fkIsingSquareRadialPatchVerticalIncidence_right_of_cell
      n m hn hm hmpos i j hi hj] at hright
  have hhorizontal :=
    fkIsingSquareRadialPatch_normSq_full_eq_bottom_add_top_increment
      n m hn hm ⟨i, hi⟩ ⟨j, hj⟩
  have hvertical :=
    fkIsingSquareRadialPatch_normSq_full_eq_left_add_right_increment
      n m hn hm ⟨i, hi⟩ ⟨j, hj⟩
  rw [← hbottom, ← htop] at hhorizontal
  rw [← hleft, ← hright] at hvertical
  calc
    2 * Complex.normSq
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i, hi⟩ ⟨j, hj⟩) =
        Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm
              ⟨i, hi⟩ ⟨j, hj⟩) +
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm
              ⟨i, hi⟩ ⟨j, hj⟩) := by ring
    _ = _ := by
      nth_rewrite 1 [hhorizontal]
      rw [hvertical]
      ring



abbrev FKIsingSquareRadialPatchPrimalNode (m : Nat) :=
  {p : Fin m × Fin m // Even (p.1.1 + p.2.1)}

def fkIsingSquareRadialPatchPrimalNodeVertex
    (n m : Nat) (hm : m ≤ n) :
    FKIsingSquareRadialPatchPrimalNode m → (fkSquareBoxPlanar n).V :=
  fun p ↦ fkIsingSquareRadialPatchVertex n m hm p.1.1 p.1.2

theorem fkIsingSquareRadialPatchPrimalNodeVertex_injective
    (n m : Nat) (hm : m ≤ n) :
    Function.Injective (fkIsingSquareRadialPatchPrimalNodeVertex n m hm) := by
  intro p q hpq
  have h0 := congrArg (fun u : (fkSquareBoxPlanar n).V ↦ u.1 0) hpq
  have h1 := congrArg (fun u : (fkSquareBoxPlanar n).V ↦ u.1 1) hpq
  simp [fkIsingSquareRadialPatchPrimalNodeVertex,
    fkIsingSquareRadialPatchVertex] at h0 h1
  have hpmod : (p.1.1.1 + p.1.2.1) % 2 = 0 := Nat.even_iff.mp p.2
  have hqmod : (q.1.1.1 + q.1.2.1) % 2 = 0 := Nat.even_iff.mp q.2
  have hpcoord : 2 * fkIsingSquareRadialPatchHalf p.1.1.1 p.1.2.1 =
      p.1.1.1 + p.1.2.1 := by
    unfold fkIsingSquareRadialPatchHalf
    omega
  have hqcoord : 2 * fkIsingSquareRadialPatchHalf q.1.1.1 q.1.2.1 =
      q.1.1.1 + q.1.2.1 := by
    unfold fkIsingSquareRadialPatchHalf
    omega
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> omega



theorem fkIsingSquareRadialPatchVertex_northeast_eq_neighbor_east
    (n m i j : Nat) (hm : m ≤ n)
    (hi : i + 1 < m) (hj : j + 1 < m) (heven : Even (i + j)) :
    fkIsingSquareRadialPatchVertex n m hm
        ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ =
      fkIsingSquareNeighbor n
        (fkIsingSquareRadialPatchVertex n m hm
          ⟨i, by omega⟩ ⟨j, by omega⟩)
        .east (by
          have h := fkIsingSquareRadialPatchDirection_available n m hm
            ⟨i, by omega⟩ ⟨j, by omega⟩
          simpa [fkIsingSquareRadialPatchDirection, heven] using h) := by
  apply Subtype.ext
  funext k
  fin_cases k <;>
    simp [fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite, Pi.add_apply]
  · have hmod := Nat.even_iff.mp heven
    omega
  · have hmod := Nat.even_iff.mp heven
    omega



theorem fkIsingSquareRadialPatchVertex_northwest_eq_neighbor_north
    (n m i j : Nat) (hm : m ≤ n)
    (hi : i + 1 < m) (hj0 : 0 < j) (hj : j < m)
    (heven : Even (i + j)) :
    fkIsingSquareRadialPatchVertex n m hm
        ⟨i + 1, hi⟩ ⟨j - 1, by omega⟩ =
      fkIsingSquareNeighbor n
        (fkIsingSquareRadialPatchVertex n m hm
          ⟨i, by omega⟩ ⟨j, by omega⟩)
        .north (by
          simp [fkIsingSquareDirectionAvailable,
            fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf]
          have hmod := Nat.even_iff.mp heven
          omega) := by
  have hjcast : ((j - 1 : Nat) : Int) = (j : Int) - 1 := by omega
  apply Subtype.ext
  funext k
  fin_cases k <;>
    simp [fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite, Pi.add_apply, hjcast]
  · have hmod := Nat.even_iff.mp heven
    omega



theorem fkIsingSquareRadialPatchVertex_southwest_eq_neighbor_west
    (n m i j : Nat) (hm : m ≤ n)
    (hi0 : 0 < i) (hj0 : 0 < j) (hi : i < m) (hj : j < m)
    (heven : Even (i + j)) :
    fkIsingSquareRadialPatchVertex n m hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ =
      fkIsingSquareNeighbor n
        (fkIsingSquareRadialPatchVertex n m hm ⟨i, hi⟩ ⟨j, hj⟩)
        .west (by
          simp [fkIsingSquareDirectionAvailable,
            fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf]
          have hmod := Nat.even_iff.mp heven
          omega) := by
  have hhalf :
      fkIsingSquareRadialPatchHalf (i - 1) (j - 1) + 1 =
        fkIsingSquareRadialPatchHalf i j := by
    unfold fkIsingSquareRadialPatchHalf
    have hmod := Nat.even_iff.mp heven
    omega
  have hhalfInt :
      (fkIsingSquareRadialPatchHalf (i - 1) (j - 1) : Int) + 1 =
        (fkIsingSquareRadialPatchHalf i j : Int) := by
    exact_mod_cast hhalf
  have hicast : ((i - 1 : Nat) : Int) = (i : Int) - 1 := by omega
  apply Subtype.ext
  funext k
  fin_cases k
  · simp [fkIsingSquareRadialPatchVertex, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
    omega
  · simp [fkIsingSquareRadialPatchVertex, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
    omega



theorem fkIsingSquareRadialPatchVertex_southeast_eq_neighbor_south
    (n m i j : Nat) (hm : m ≤ n)
    (hi0 : 0 < i) (hj : j + 1 < m) (hi : i < m)
    (heven : Even (i + j)) :
    fkIsingSquareRadialPatchVertex n m hm
        ⟨i - 1, by omega⟩ ⟨j + 1, hj⟩ =
      fkIsingSquareNeighbor n
        (fkIsingSquareRadialPatchVertex n m hm
          ⟨i, hi⟩ ⟨j, by omega⟩)
        .south (by
          simp [fkIsingSquareDirectionAvailable,
            fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf]
          have hmod := Nat.even_iff.mp heven
          omega) := by
  have hhalf : fkIsingSquareRadialPatchHalf (i - 1) (j + 1) =
      fkIsingSquareRadialPatchHalf i j := by
    unfold fkIsingSquareRadialPatchHalf
    have hmod := Nat.even_iff.mp heven
    omega
  have hhalfInt : (fkIsingSquareRadialPatchHalf (i - 1) (j + 1) : Int) =
      (fkIsingSquareRadialPatchHalf i j : Int) := by
    exact_mod_cast hhalf
  have hicast : ((i - 1 : Nat) : Int) = (i : Int) - 1 := by omega
  apply Subtype.ext
  funext k
  fin_cases k <;>
    simp [fkIsingSquareRadialPatchVertex, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite] <;> omega



theorem fkIsingSquareRadialPatch_adj_iff_diagonal
    (n m i j : Nat) (hm : m ≤ n)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m)
    (heven : Even (i + j)) (y : (fkSquareBoxPlanar n).V) :
    (fkSquareBoxPlanar n).G.Adj
        (fkIsingSquareRadialPatchVertex n m hm
          ⟨i, by omega⟩ ⟨j, by omega⟩) y ↔
      y = fkIsingSquareRadialPatchVertex n m hm
          ⟨i + 1, hi1⟩ ⟨j + 1, hj1⟩ ∨
      y = fkIsingSquareRadialPatchVertex n m hm
          ⟨i + 1, hi1⟩ ⟨j - 1, by omega⟩ ∨
      y = fkIsingSquareRadialPatchVertex n m hm
          ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ ∨
      y = fkIsingSquareRadialPatchVertex n m hm
          ⟨i - 1, by omega⟩ ⟨j + 1, hj1⟩ := by
  let c := fkIsingSquareRadialPatchVertex n m hm
    ⟨i, by omega⟩ ⟨j, by omega⟩
  have heast : fkIsingSquareDirectionAvailable n c .east := by
    have h := fkIsingSquareRadialPatchDirection_available n m hm
      ⟨i, by omega⟩ ⟨j, by omega⟩
    simpa [c, fkIsingSquareRadialPatchDirection, heven] using h
  have hnorth : fkIsingSquareDirectionAvailable n c .north := by
    simp [c, fkIsingSquareDirectionAvailable,
      fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf]
    have hmod := Nat.even_iff.mp heven
    omega
  have hwest : fkIsingSquareDirectionAvailable n c .west := by
    simp [c, fkIsingSquareDirectionAvailable,
      fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf]
    have hmod := Nat.even_iff.mp heven
    omega
  have hsouth : fkIsingSquareDirectionAvailable n c .south := by
    simp [c, fkIsingSquareDirectionAvailable,
      fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf]
    have hmod := Nat.even_iff.mp heven
    omega
  have hNE :
      fkIsingSquareRadialPatchVertex n m hm
          ⟨i + 1, hi1⟩ ⟨j + 1, hj1⟩ =
        fkIsingSquareNeighbor n c .east heast := by
    simpa only [c] using
      fkIsingSquareRadialPatchVertex_northeast_eq_neighbor_east
        n m i j hm hi1 hj1 heven
  have hNW :
      fkIsingSquareRadialPatchVertex n m hm
          ⟨i + 1, hi1⟩ ⟨j - 1, by omega⟩ =
        fkIsingSquareNeighbor n c .north hnorth := by
    simpa only [c] using
      fkIsingSquareRadialPatchVertex_northwest_eq_neighbor_north
        n m i j hm hi1 hj0 (by omega) heven
  have hSW :
      fkIsingSquareRadialPatchVertex n m hm
          ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ =
        fkIsingSquareNeighbor n c .west hwest := by
    simpa only [c] using
      fkIsingSquareRadialPatchVertex_southwest_eq_neighbor_west
        n m i j hm hi0 hj0 (by omega) (by omega) heven
  have hSE :
      fkIsingSquareRadialPatchVertex n m hm
          ⟨i - 1, by omega⟩ ⟨j + 1, hj1⟩ =
        fkIsingSquareNeighbor n c .south hsouth := by
    simpa only [c] using
      fkIsingSquareRadialPatchVertex_southeast_eq_neighbor_south
        n m i j hm hi0 hj1 (by omega) heven
  constructor
  · intro hadj
    change NearestNeighbour 2 c.1 y.1 at hadj
    rw [nearestNeighbour_iff_shift] at hadj
    obtain ⟨k, s, hs, hy⟩ := hadj
    fin_cases k <;> rcases hs with rfl | rfl
    · left
      rw [hNE]
      apply Subtype.ext
      funext l
      have hyl := congrFun hy l
      fin_cases l <;>
        simpa [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
          shift, Function.update] using hyl
    · right; right; left
      rw [hSW]
      apply Subtype.ext
      funext l
      have hyl := congrFun hy l
      fin_cases l <;>
        simpa [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
          shift, Function.update] using hyl
    · right; left
      rw [hNW]
      apply Subtype.ext
      funext l
      have hyl := congrFun hy l
      fin_cases l <;>
        simpa [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
          shift, Function.update] using hyl
    · right; right; right
      rw [hSE]
      apply Subtype.ext
      funext l
      have hyl := congrFun hy l
      fin_cases l <;>
        simpa [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
          shift, Function.update] using hyl
  · rintro (rfl | rfl | rfl | rfl)
    · rw [hNE]
      exact fkIsingSquare_adj_neighbor n c .east heast
    · rw [hNW]
      exact fkIsingSquare_adj_neighbor n c .north hnorth
    · rw [hSW]
      exact fkIsingSquare_adj_neighbor n c .west hwest
    · rw [hSE]
      exact fkIsingSquare_adj_neighbor n c .south hsouth



def fkIsingSquareRadialPatchDiagonalLaplacian
    (H : Nat → Nat → Real) (i j : Nat) : Real :=
  H (i + 1) (j + 1) + H (i + 1) (j - 1) +
    H (i - 1) (j - 1) + H (i - 1) (j + 1) - 4 * H i j


def fkIsingSquareRadialPatchPrimalIncrementDivergence
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) : Real :=
  let inc := fkIsingSquareInteriorRadialIncrement n hn
  inc (fkIsingSquareRadialPatchHorizontalIncidence
      n m hn hm hmpos i j) -
    inc (fkIsingSquareRadialPatchVerticalIncidence
      n m hn hm hmpos (i + 1) j) +
    inc (fkIsingSquareRadialPatchVerticalIncidence
      n m hn hm hmpos i (j - 1)) -
    inc (fkIsingSquareRadialPatchHorizontalIncidence
      n m hn hm hmpos i (j - 1)) +
    inc (fkIsingSquareRadialPatchHorizontalIncidence
      n m hn hm hmpos (i - 1) j) -
    inc (fkIsingSquareRadialPatchVerticalIncidence
      n m hn hm hmpos (i - 1) (j - 1)) +
    inc (fkIsingSquareRadialPatchVerticalIncidence
      n m hn hm hmpos i j) -
    inc (fkIsingSquareRadialPatchHorizontalIncidence
      n m hn hm hmpos (i - 1) (j + 1))



theorem fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_eq_divergence
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j)) :
    fkIsingSquareRadialPatchDiagonalLaplacian
        (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j =
      fkIsingSquareRadialPatchPrimalIncrementDivergence
        n m hn hm hmpos i j := by
  have hoddNE : ¬ Even (i + 1 + j) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hoddNW : ¬ Even (i + (j - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hoddSW : ¬ Even (i - 1 + j) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hevenSW : Even (i - 1 + (j - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hevenSE : Even (i - 1 + (j + 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hrE := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos i j (by omega) (by omega)
  have hvE := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos (i + 1) j
  have hvN := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos i (j - 1)
  have hrN := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos i (j - 1) (by omega) (by omega)
  have hrW := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos (i - 1) j (by omega) (by omega)
  have hvW := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos (i - 1) (j - 1)
  have hvS := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos i j
  have hrS := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos (i - 1) (j + 1) (by omega) (by omega)
  simp only [fkIsingSquareRadialPatchHorizontalSignedIncrement,
    fkIsingSquareRadialPatchVerticalSignedIncrement, heven, hoddNE,
    hoddNW, hoddSW, hevenSW, hevenSE, if_true, if_false] at hrE hvE hvN hrN hrW hvW hvS hrS
  have hiSub : i - 1 + 1 = i := by omega
  have hjSub : j - 1 + 1 = j := by omega
  rw [hiSub] at hrW hrS
  rw [hjSub] at hvN hvW
  unfold fkIsingSquareRadialPatchDiagonalLaplacian
  unfold fkIsingSquareRadialPatchPrimalIncrementDivergence
  dsimp only
  linarith



theorem fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_eq_neg_divergence_of_odd
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (hodd : ¬ Even (i + j)) :
    fkIsingSquareRadialPatchDiagonalLaplacian
        (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j =
      -fkIsingSquareRadialPatchPrimalIncrementDivergence
        n m hn hm hmpos i j := by
  have hevenNE : Even (i + 1 + j) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hevenNW : Even (i + (j - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hevenSW : Even (i - 1 + j) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hoddSW : ¬ Even (i - 1 + (j - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hoddSE : ¬ Even (i - 1 + (j + 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hrE := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos i j (by omega) (by omega)
  have hvE := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos (i + 1) j
  have hvN := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos i (j - 1)
  have hrN := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos i (j - 1) (by omega) (by omega)
  have hrW := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos (i - 1) j (by omega) (by omega)
  have hvW := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos (i - 1) (j - 1)
  have hvS := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos i j
  have hrS := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos (i - 1) (j + 1) (by omega) (by omega)
  simp only [fkIsingSquareRadialPatchHorizontalSignedIncrement,
    fkIsingSquareRadialPatchVerticalSignedIncrement, hodd, hevenNE,
    hevenNW, hevenSW, hoddSW, hoddSE, if_true, if_false]
    at hrE hvE hvN hrN hrW hvW hvS hrS
  have hiSub : i - 1 + 1 = i := by omega
  have hjSub : j - 1 + 1 = j := by omega
  rw [hiSub] at hrW hrS
  rw [hjSub] at hvN hvW
  unfold fkIsingSquareRadialPatchDiagonalLaplacian
  unfold fkIsingSquareRadialPatchPrimalIncrementDivergence
  dsimp only
  linarith



theorem fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_projectionDivergence
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j)) :
    fkIsingSquareRadialPatchPrimalIncrementDivergence
        n m hn hm hmpos i j =
      isingPrimalProjectionDivergence
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j - 1, by omega⟩)
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j, by omega⟩)
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i - 1, by omega⟩ ⟨j, by omega⟩)
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩) := by
  have hoddN : ¬ Even (i + (j - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hoddS : ¬ Even (i - 1 + j) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hevenW : Even (i - 1 + (j - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  let eN := fkIsingSquareRadialPatchEdge n m hm
    ⟨i, by omega⟩ ⟨j - 1, by omega⟩
  let eE := fkIsingSquareRadialPatchEdge n m hm
    ⟨i, by omega⟩ ⟨j, by omega⟩
  let eS := fkIsingSquareRadialPatchEdge n m hm
    ⟨i - 1, by omega⟩ ⟨j, by omega⟩
  let eW := fkIsingSquareRadialPatchEdge n m hm
    ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .vertical := by
    rw [show eN = fkIsingSquareRadialPatchEdge n m hm
        ⟨i, by omega⟩ ⟨j - 1, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hoddN,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisE : (fkIsingSquareOrientedEdge n eE).axis = .horizontal := by
    rw [show eE = fkIsingSquareRadialPatchEdge n m hm
        ⟨i, by omega⟩ ⟨j, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ heven,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisS : (fkIsingSquareOrientedEdge n eS).axis = .vertical := by
    rw [show eS = fkIsingSquareRadialPatchEdge n m hm
        ⟨i - 1, by omega⟩ ⟨j, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hoddS,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .horizontal := by
    rw [show eW = fkIsingSquareRadialPatchEdge n m hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ hevenW,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eN haxisN with
    ⟨hNW, hNE, hNS, hNN⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eE haxisE with
    ⟨hEW, hEE, hES, hEN⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eS haxisS with
    ⟨hSW, hSE, hSS, hSN⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eW haxisW with
    ⟨hWW, hWE, hWS, hWN⟩
  let inc := fkIsingSquareInteriorRadialIncrement n hn
  have hEWedge := congrArg inc
    (fkIsingSquareRadialPatchHorizontalIncidence_bottom
      n m hn hm hmpos i j (by omega) (by omega))
  have hENedge := congrArg inc
    (fkIsingSquareRadialPatchVerticalIncidence_right_of_cell
      n m hn hm hmpos i j (by omega) (by omega))
  have hNWedge := congrArg inc
    (fkIsingSquareRadialPatchVerticalIncidence_left
      n m hn hm hmpos i (j - 1) (by omega) (by omega))
  have hNNedge := congrArg inc
    (fkIsingSquareRadialPatchHorizontalIncidence_bottom
      n m hn hm hmpos i (j - 1) (by omega) (by omega))
  have hWEedge := congrArg inc
    (fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell
      n m hn hm hmpos (i - 1) (j - 1) (by omega) (by omega))
  have hWSedge := congrArg inc
    (fkIsingSquareRadialPatchVerticalIncidence_left
      n m hn hm hmpos (i - 1) (j - 1) (by omega) (by omega))
  have hSEedge := congrArg inc
    (fkIsingSquareRadialPatchVerticalIncidence_right_of_cell
      n m hn hm hmpos (i - 1) j (by omega) (by omega))
  have hSSedge := congrArg inc
    (fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell
      n m hn hm hmpos (i - 1) j (by omega) (by omega))
  simp only [fkIsingSquareRadialPatchBottomSide,
    fkIsingSquareRadialPatchTopSide, fkIsingSquareRadialPatchLeftSide,
    fkIsingSquareRadialPatchRightSide, heven, hoddN, hoddS, hevenW,
    if_true, if_false] at hEWedge hENedge hNWedge hNNedge hWEedge hWSedge hSEedge hSSedge
  have hiSub : i - 1 + 1 = i := by omega
  have hjSub : j - 1 + 1 = j := by omega
  rw [hjSub] at hWEedge
  rw [hiSub] at hSEedge
  dsimp only [inc] at hEWedge hENedge hNWedge hNNedge hWEedge hWSedge hSEedge hSSedge
  unfold fkIsingSquareRadialPatchPrimalIncrementDivergence
  dsimp only
  rw [hEWedge, hENedge, hNWedge, hNNedge, hWEedge, hWSedge,
    hSEedge, hSSedge]
  simp_rw [fkIsingSquareRadialPatchIncidence_increment_eq_normSq_full_projection]
  unfold isingPrimalProjectionDivergence
  unfold fkIsingSquareRadialPatchFullObservable
  rw [hNW, hNN, hEW, hEN, hSE, hSS, hWE, hWS]
  ring



theorem fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_rotated_projectionDivergence_of_odd
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (hodd : ¬ Even (i + j)) :
    fkIsingSquareRadialPatchPrimalIncrementDivergence
        n m hn hm hmpos i j =
      isingPrimalProjectionDivergence
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i - 1, by omega⟩ ⟨j, by omega⟩)
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩)
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j - 1, by omega⟩)
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j, by omega⟩) := by
  have hevenN : Even (i + (j - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hevenS : Even (i - 1 + j) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hoddW : ¬ Even (i - 1 + (j - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  let eN := fkIsingSquareRadialPatchEdge n m hm
    ⟨i, by omega⟩ ⟨j - 1, by omega⟩
  let eE := fkIsingSquareRadialPatchEdge n m hm
    ⟨i, by omega⟩ ⟨j, by omega⟩
  let eS := fkIsingSquareRadialPatchEdge n m hm
    ⟨i - 1, by omega⟩ ⟨j, by omega⟩
  let eW := fkIsingSquareRadialPatchEdge n m hm
    ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .horizontal := by
    rw [show eN = fkIsingSquareRadialPatchEdge n m hm
        ⟨i, by omega⟩ ⟨j - 1, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ hevenN,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisE : (fkIsingSquareOrientedEdge n eE).axis = .vertical := by
    rw [show eE = fkIsingSquareRadialPatchEdge n m hm
        ⟨i, by omega⟩ ⟨j, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hodd,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisS : (fkIsingSquareOrientedEdge n eS).axis = .horizontal := by
    rw [show eS = fkIsingSquareRadialPatchEdge n m hm
        ⟨i - 1, by omega⟩ ⟨j, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ hevenS,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .vertical := by
    rw [show eW = fkIsingSquareRadialPatchEdge n m hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hoddW,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eN haxisN with
    ⟨hNW, hNE, hNS, hNN⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eE haxisE with
    ⟨hEW, hEE, hES, hEN⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eS haxisS with
    ⟨hSW, hSE, hSS, hSN⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eW haxisW with
    ⟨hWW, hWE, hWS, hWN⟩
  let inc := fkIsingSquareInteriorRadialIncrement n hn
  have hEWedge := congrArg inc
    (fkIsingSquareRadialPatchHorizontalIncidence_bottom
      n m hn hm hmpos i j (by omega) (by omega))
  have hENedge := congrArg inc
    (fkIsingSquareRadialPatchVerticalIncidence_right_of_cell
      n m hn hm hmpos i j (by omega) (by omega))
  have hNWedge := congrArg inc
    (fkIsingSquareRadialPatchVerticalIncidence_left
      n m hn hm hmpos i (j - 1) (by omega) (by omega))
  have hNNedge := congrArg inc
    (fkIsingSquareRadialPatchHorizontalIncidence_bottom
      n m hn hm hmpos i (j - 1) (by omega) (by omega))
  have hWEedge := congrArg inc
    (fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell
      n m hn hm hmpos (i - 1) (j - 1) (by omega) (by omega))
  have hWSedge := congrArg inc
    (fkIsingSquareRadialPatchVerticalIncidence_left
      n m hn hm hmpos (i - 1) (j - 1) (by omega) (by omega))
  have hSEedge := congrArg inc
    (fkIsingSquareRadialPatchVerticalIncidence_right_of_cell
      n m hn hm hmpos (i - 1) j (by omega) (by omega))
  have hSSedge := congrArg inc
    (fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell
      n m hn hm hmpos (i - 1) j (by omega) (by omega))
  simp only [fkIsingSquareRadialPatchBottomSide,
    fkIsingSquareRadialPatchTopSide, fkIsingSquareRadialPatchLeftSide,
    fkIsingSquareRadialPatchRightSide, hodd, hevenN, hevenS, hoddW,
    if_true, if_false] at hEWedge hENedge hNWedge hNNedge hWEedge hWSedge hSEedge hSSedge
  have hiSub : i - 1 + 1 = i := by omega
  have hjSub : j - 1 + 1 = j := by omega
  rw [hjSub] at hWEedge
  rw [hiSub] at hSEedge
  dsimp only [inc] at hEWedge hENedge hNWedge hNNedge hWEedge hWSedge hSEedge hSSedge
  unfold fkIsingSquareRadialPatchPrimalIncrementDivergence
  dsimp only
  rw [hEWedge, hENedge, hNWedge, hNNedge, hWEedge, hWSedge,
    hSEedge, hSSedge]
  simp_rw [fkIsingSquareRadialPatchIncidence_increment_eq_normSq_full_projection]
  unfold isingPrimalProjectionDivergence
  unfold fkIsingSquareRadialPatchFullObservable
  rw [hEN, hEE, hNS, hNW, hWS, hWW, hSN, hSE]
  ring



theorem fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_primitiveLaplacian
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j)) :
    fkIsingSquareRadialPatchPrimalIncrementDivergence
        n m hn hm hmpos i j =
      isingPrimalPrimitiveLaplacian
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j - 1, by omega⟩)
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j, by omega⟩)
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i - 1, by omega⟩ ⟨j, by omega⟩)
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩) := by
  rw [fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_projectionDivergence
      n m i j hn hm hmpos hi0 hi1 hj0 hj1 heven]
  exact (isingPrimalPrimitiveLaplacian_eq_projectionDivergence _ _ _ _).symm



theorem fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_nonneg_of_odd
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (hodd : ¬ Even (i + j)) :
    0 ≤ fkIsingSquareRadialPatchDiagonalLaplacian
      (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j := by
  rw [fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_eq_neg_divergence_of_odd
      n m i j hn hm hmpos hi0 hi1 hj0 hj1 hodd,
    fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_rotated_projectionDivergence_of_odd
      n m i j hn hm hmpos hi0 hi1 hj0 hj1 hodd,
    ← isingPrimalPrimitiveLaplacian_eq_projectionDivergence,
    ← isingPrimalPrimitiveLaplacian_rotate_two]
  exact isingPrimalPrimitiveLaplacian_nonneg _ _ _ _
    (fkIsingSquareRadialPatchFullObservable_quad_of_odd
      n m i j hn hm hi0 hi1 hj0 hj1 hodd)



theorem fkIsingSquareRadialPatch_finiteGraphLaplacian_eq_diagonal
    (n m i j : Nat) (hm : m ≤ n)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m)
    (heven : Even (i + j))
    (f : (fkSquareBoxPlanar n).V → Real) (H : Nat → Nat → Real)
    (hc : f (fkIsingSquareRadialPatchVertex n m hm
        ⟨i, by omega⟩ ⟨j, by omega⟩) = H i j)
    (hne : f (fkIsingSquareRadialPatchVertex n m hm
        ⟨i + 1, hi1⟩ ⟨j + 1, hj1⟩) = H (i + 1) (j + 1))
    (hnw : f (fkIsingSquareRadialPatchVertex n m hm
        ⟨i + 1, hi1⟩ ⟨j - 1, by omega⟩) = H (i + 1) (j - 1))
    (hsw : f (fkIsingSquareRadialPatchVertex n m hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩) = H (i - 1) (j - 1))
    (hse : f (fkIsingSquareRadialPatchVertex n m hm
        ⟨i - 1, by omega⟩ ⟨j + 1, hj1⟩) = H (i - 1) (j + 1)) :
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G f
        (fkIsingSquareRadialPatchVertex n m hm
          ⟨i, by omega⟩ ⟨j, by omega⟩) =
      fkIsingSquareRadialPatchDiagonalLaplacian H i j := by
  let pNE : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨i + 1, hi1⟩, ⟨j + 1, hj1⟩), by
      change Even ((i + 1) + (j + 1))
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp heven
      omega⟩
  let pNW : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨i + 1, hi1⟩, ⟨j - 1, by omega⟩), by
      change Even ((i + 1) + (j - 1))
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp heven
      omega⟩
  let pSW : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨i - 1, by omega⟩, ⟨j - 1, by omega⟩), by
      change Even ((i - 1) + (j - 1))
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp heven
      omega⟩
  let pSE : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨i - 1, by omega⟩, ⟨j + 1, hj1⟩), by
      change Even ((i - 1) + (j + 1))
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp heven
      omega⟩
  let ne := fkIsingSquareRadialPatchPrimalNodeVertex n m hm pNE
  let nw := fkIsingSquareRadialPatchPrimalNodeVertex n m hm pNW
  let sw := fkIsingSquareRadialPatchPrimalNodeVertex n m hm pSW
  let se := fkIsingSquareRadialPatchPrimalNodeVertex n m hm pSE
  let c := fkIsingSquareRadialPatchVertex n m hm
    ⟨i, by omega⟩ ⟨j, by omega⟩
  have hneighbors : (fkSquareBoxPlanar n).G.neighborFinset c =
      {ne, nw, sw, se} := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_singleton]
    simpa only [c, ne, nw, sw, se, pNE, pNW, pSW, pSE,
      fkIsingSquareRadialPatchPrimalNodeVertex] using
      fkIsingSquareRadialPatch_adj_iff_diagonal
        n m i j hm hi0 hi1 hj0 hj1 heven y
  have hinj := fkIsingSquareRadialPatchPrimalNodeVertex_injective n m hm
  have hpNE_NW : pNE ≠ pNW := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m =>
      p.1.2.1) h
    simp [pNE, pNW] at hk
    omega
  have hpNE_SW : pNE ≠ pSW := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m =>
      p.1.1.1) h
    simp [pNE, pSW] at hk
    omega
  have hpNE_SE : pNE ≠ pSE := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m =>
      p.1.1.1) h
    simp [pNE, pSE] at hk
    omega
  have hpNW_SW : pNW ≠ pSW := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m =>
      p.1.1.1) h
    simp [pNW, pSW] at hk
    omega
  have hpNW_SE : pNW ≠ pSE := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m =>
      p.1.1.1) h
    simp [pNW, pSE] at hk
    omega
  have hpSW_SE : pSW ≠ pSE := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m =>
      p.1.2.1) h
    simp [pSW, pSE] at hk
  have hNE_NW : ne ≠ nw := hinj.ne hpNE_NW
  have hNE_SW : ne ≠ sw := hinj.ne hpNE_SW
  have hNE_SE : ne ≠ se := hinj.ne hpNE_SE
  have hNW_SW : nw ≠ sw := hinj.ne hpNW_SW
  have hNW_SE : nw ≠ se := hinj.ne hpNW_SE
  have hSW_SE : sw ≠ se := hinj.ne hpSW_SE
  unfold isingFiniteGraphLaplacian
  rw [hneighbors]
  simp [hNE_NW, hNE_SW, hNE_SE, hNW_SW, hNW_SE, hSW_SE]
  simp only [c, ne, nw, sw, se, pNE, pNW, pSW, pSE,
    fkIsingSquareRadialPatchPrimalNodeVertex] at hc hne hnw hsw hse ⊢
  rw [hc, hne, hnw, hsw, hse]
  unfold fkIsingSquareRadialPatchDiagonalLaplacian
  ring



noncomputable def fkIsingSquareRadialPatchPrimalPrimitiveExtension
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) : (fkSquareBoxPlanar n).V → Real :=
  Function.extend
    (fkIsingSquareRadialPatchPrimalNodeVertex n m hm)
    (fun p ↦ base + fkIsingSquareRadialPatchPrimitive
      n m hn hm hmpos p.1.1.1 p.1.2.1)
    (fun _ ↦ 0)

theorem fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (p : FKIsingSquareRadialPatchPrimalNode m) :
    fkIsingSquareRadialPatchPrimalPrimitiveExtension
        n m hn hm hmpos base
        (fkIsingSquareRadialPatchPrimalNodeVertex n m hm p) =
      base + fkIsingSquareRadialPatchPrimitive
        n m hn hm hmpos p.1.1.1 p.1.2.1 := by
  exact (fkIsingSquareRadialPatchPrimalNodeVertex_injective n m hm).extend_apply
    _ _ p

theorem fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply_of_even
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (i j : Nat) (hi : i < m) (hj : j < m)
    (heven : Even (i + j)) :
    fkIsingSquareRadialPatchPrimalPrimitiveExtension
        n m hn hm hmpos base
        (fkIsingSquareRadialPatchVertex n m hm ⟨i, hi⟩ ⟨j, hj⟩) =
      base + fkIsingSquareRadialPatchPrimitive
        n m hn hm hmpos i j := by
  let p : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨i, hi⟩, ⟨j, hj⟩), heven⟩
  simpa only [p, fkIsingSquareRadialPatchPrimalNodeVertex] using
    fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply
      n m hn hm hmpos base p



theorem fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_eq_diagonal
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j)) :
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareRadialPatchPrimalPrimitiveExtension
          n m hn hm hmpos base)
        (fkIsingSquareRadialPatchVertex n m hm
          ⟨i, by omega⟩ ⟨j, by omega⟩) =
      fkIsingSquareRadialPatchDiagonalLaplacian
        (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j := by
  let H := fkIsingSquareRadialPatchPrimitive n m hn hm hmpos
  calc
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareRadialPatchPrimalPrimitiveExtension
          n m hn hm hmpos base)
        (fkIsingSquareRadialPatchVertex n m hm
          ⟨i, by omega⟩ ⟨j, by omega⟩) =
      fkIsingSquareRadialPatchDiagonalLaplacian
        (fun a b ↦ base + H a b) i j := by
          apply fkIsingSquareRadialPatch_finiteGraphLaplacian_eq_diagonal
            n m i j hm hi0 hi1 hj0 hj1 heven
          · exact fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply_of_even
              n m hn hm hmpos base i j (by omega) (by omega) heven
          · apply fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply_of_even
            rw [Nat.even_iff]
            have hmod := Nat.even_iff.mp heven
            omega
          · apply fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply_of_even
            rw [Nat.even_iff]
            have hmod := Nat.even_iff.mp heven
            omega
          · apply fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply_of_even
            rw [Nat.even_iff]
            have hmod := Nat.even_iff.mp heven
            omega
          · apply fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply_of_even
            rw [Nat.even_iff]
            have hmod := Nat.even_iff.mp heven
            omega
    _ = fkIsingSquareRadialPatchDiagonalLaplacian H i j := by
      unfold fkIsingSquareRadialPatchDiagonalLaplacian
      ring



theorem fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_eq_divergence
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j)) :
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareRadialPatchPrimalPrimitiveExtension
          n m hn hm hmpos base)
        (fkIsingSquareRadialPatchVertex n m hm
          ⟨i, by omega⟩ ⟨j, by omega⟩) =
      fkIsingSquareRadialPatchPrimalIncrementDivergence
        n m hn hm hmpos i j := by
  rw [fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_eq_diagonal
      n m i j hn hm hmpos base hi0 hi1 hj0 hj1 heven,
    fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_eq_divergence
      n m i j hn hm hmpos hi0 hi1 hj0 hj1 heven]




theorem fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_nonneg_of_quad
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j))
    (hquad : IsingSquareSHolomorphicQuad
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i, by omega⟩ ⟨j - 1, by omega⟩)
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i, by omega⟩ ⟨j, by omega⟩)
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i - 1, by omega⟩ ⟨j, by omega⟩)
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩)) :
    0 ≤ isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
      (fkIsingSquareRadialPatchPrimalPrimitiveExtension
        n m hn hm hmpos base)
      (fkIsingSquareRadialPatchVertex n m hm
        ⟨i, by omega⟩ ⟨j, by omega⟩) := by
  rw [fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_eq_divergence
      n m i j hn hm hmpos base hi0 hi1 hj0 hj1 heven,
    fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_primitiveLaplacian
      n m i j hn hm hmpos hi0 hi1 hj0 hj1 heven]
  exact isingPrimalPrimitiveLaplacian_nonneg _ _ _ _ hquad



theorem fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_nonpos
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j)) :
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
      (fkIsingSquareRadialPatchPrimalPrimitiveExtension
        n m hn hm hmpos base)
      (fkIsingSquareRadialPatchVertex n m hm
        ⟨i, by omega⟩ ⟨j, by omega⟩) ≤ 0 := by
  rw [fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_eq_divergence
      n m i j hn hm hmpos base hi0 hi1 hj0 hj1 heven,
    fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_primitiveLaplacian
      n m i j hn hm hmpos hi0 hi1 hj0 hj1 heven]
  apply isingPrimalPrimitiveLaplacian_nonpos_of_rotated_quad
  exact fkIsingSquareRadialPatchFullObservable_quad
    n m i j hn hm hi0 hi1 hj0 hj1 heven



def fkIsingSquareRadialPatchInteriorEvenRegion
    (n m : Nat) (hm : m ≤ n) (x : (fkSquareBoxPlanar n).V) : Prop :=
  ∃ i j : Fin m, 0 < i.1 ∧ i.1 + 1 < m ∧
    0 < j.1 ∧ j.1 + 1 < m ∧ Even (i.1 + j.1) ∧
      x = fkIsingSquareRadialPatchVertex n m hm i j




theorem fkIsingSquareRadialPatchPrimalPrimitiveExtension_superharmonicOn_region
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) :
    IsingFiniteGraphSuperharmonicOn (fkSquareBoxPlanar n).G
      (fun x ↦ ¬ fkIsingSquareRadialPatchInteriorEvenRegion n m hm x)
      (fkIsingSquareRadialPatchPrimalPrimitiveExtension
        n m hn hm hmpos base) := by
  intro x hx
  have hregion : fkIsingSquareRadialPatchInteriorEvenRegion n m hm x := by
    exact Classical.byContradiction (fun h ↦ hx h)
  rcases hregion with ⟨i, j, hi0, hi1, hj0, hj1, heven, rfl⟩
  exact fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_nonpos
    n m i.1 j.1 hn hm hmpos base hi0 hi1 hj0 hj1 heven


noncomputable def fkIsingSquareGrowingRadialPrimalPrimitive
    (m : Nat → Nat) (hm : ∀ n, m n ≤ n) (base : Nat → Real) :
    ∀ n, (fkSquareBoxPlanar n).V → Real :=
  fun n ↦ if hmn : 0 < m n then
    fkIsingSquareRadialPatchPrimalPrimitiveExtension
      n (m n) (lt_of_lt_of_le hmn (hm n)) (hm n) hmn (base n)
  else fun _ ↦ 0

theorem fkIsingSquareGrowingRadialPrimalPrimitive_apply
    (m : Nat → Nat) (hm : ∀ n, m n ≤ n) (base : Nat → Real)
    (n : Nat) (hmn : 0 < m n)
    (p : FKIsingSquareRadialPatchPrimalNode (m n)) :
    fkIsingSquareGrowingRadialPrimalPrimitive m hm base n
        (fkIsingSquareRadialPatchPrimalNodeVertex n (m n) (hm n) p) =
      base n + fkIsingSquareRadialPatchPrimitive
        n (m n) (lt_of_lt_of_le hmn (hm n)) (hm n) hmn
          p.1.1.1 p.1.2.1 := by
  simp only [fkIsingSquareGrowingRadialPrimalPrimitive, dif_pos hmn]
  exact fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply _ _ _ _ _ _ _





theorem fkIsingSquareRadialPatchPrimitive_uniform_convergence_to_imPhi
    (embedding : ∀ n, (fkSquareBoxPlanar n).V → Complex)
    (Phi : Complex → Complex)
    (upper lower harmonic physical :
      ∀ n, (fkSquareBoxPlanar n).V → Real)
    (eps : Nat → Real) (m : Nat → Nat) (base : Nat → Real)
    (hm : ∀ n, m n ≤ n)
    (hmpos : ∀ᶠ n in atTop, 0 < m n)
    (hupper : ∀ n, IsingFiniteGraphSubharmonicOn
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (upper n))
    (hlower : ∀ n, IsingFiniteGraphSuperharmonicOn
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (lower n))
    (hharmonic : ∀ n, IsingFiniteGraphHarmonicOn
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (harmonic n))
    (hupperBoundary : ∀ n x, fkIsingSquareBoxBoundary n x →
      upper n x ≤ harmonic n x + eps n)
    (hlowerBoundary : ∀ n x, fkIsingSquareBoxBoundary n x →
      harmonic n x ≤ lower n x + eps n)
    (hsandwich : ∀ n x,
      lower n x ≤ physical n x ∧ physical n x ≤ upper n x)
    (heps : Tendsto eps atTop (nhds 0))
    (hdirichlet : ∀ eta : Real, 0 < eta →
      ∀ᶠ n in atTop, ∀ x,
        |harmonic n x - fkIsingSquareSampledImaginaryPart
          embedding Phi n x| < eta)
    (hidentify : ∀ n (hn : 0 < n) (hmn : 0 < m n)
      (i j : Fin (m n)), Even (i.1 + j.1) →
      base n + fkIsingSquareRadialPatchPrimitive
          n (m n) hn (hm n) hmn i.1 j.1 =
        physical n (fkIsingSquareRadialPatchVertex n (m n) (hm n) i j)) :
    ∀ eta : Real, 0 < eta →
      ∀ᶠ n in atTop, ∀ (hmn : 0 < m n)
        (i j : Fin (m n)), Even (i.1 + j.1) →
        |base n + fkIsingSquareRadialPatchPrimitive
              n (m n) (lt_of_lt_of_le hmn (hm n)) (hm n) hmn i.1 j.1 -
            fkIsingSquareSampledImaginaryPart embedding Phi n
              (fkIsingSquareRadialPatchVertex n (m n) (hm n) i j)| < eta := by
  intro eta heta
  have hfull := fkIsingSquare_physicalPrimitive_uniform_convergence_to_imPhi
    embedding Phi upper lower harmonic physical eps hupper hlower hharmonic
    hupperBoundary hlowerBoundary hsandwich heps hdirichlet eta heta
  filter_upwards [hfull, hmpos] with n hnconv hmn
  intro hmn' i j heven
  have hn : 0 < n := lt_of_lt_of_le hmn (hm n)
  rw [hidentify n hn hmn' i j heven]
  exact hnconv (fkIsingSquareRadialPatchVertex n (m n) (hm n) i j)



theorem fkIsingSquareGrowingRadialPrimalPrimitive_uniform_convergence_to_imPhi
    (embedding : ∀ n, (fkSquareBoxPlanar n).V → Complex)
    (Phi : Complex → Complex)
    (upper lower harmonic : ∀ n, (fkSquareBoxPlanar n).V → Real)
    (eps : Nat → Real) (m : Nat → Nat) (base : Nat → Real)
    (hm : ∀ n, m n ≤ n)
    (hmpos : ∀ᶠ n in atTop, 0 < m n)
    (hupper : ∀ n, IsingFiniteGraphSubharmonicOn
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (upper n))
    (hlower : ∀ n, IsingFiniteGraphSuperharmonicOn
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (lower n))
    (hharmonic : ∀ n, IsingFiniteGraphHarmonicOn
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (harmonic n))
    (hupperBoundary : ∀ n x, fkIsingSquareBoxBoundary n x →
      upper n x ≤ harmonic n x + eps n)
    (hlowerBoundary : ∀ n x, fkIsingSquareBoxBoundary n x →
      harmonic n x ≤ lower n x + eps n)
    (hsandwich : ∀ n x,
      lower n x ≤ fkIsingSquareGrowingRadialPrimalPrimitive m hm base n x ∧
        fkIsingSquareGrowingRadialPrimalPrimitive m hm base n x ≤ upper n x)
    (heps : Tendsto eps atTop (nhds 0))
    (hdirichlet : ∀ eta : Real, 0 < eta →
      ∀ᶠ n in atTop, ∀ x,
        |harmonic n x - fkIsingSquareSampledImaginaryPart
          embedding Phi n x| < eta) :
    ∀ eta : Real, 0 < eta →
      ∀ᶠ n in atTop, ∀ (p : FKIsingSquareRadialPatchPrimalNode (m n)),
        |base n + fkIsingSquareRadialPatchPrimitive
              n (m n)
              (lt_of_lt_of_le (Nat.zero_lt_of_lt p.1.1.2) (hm n))
              (hm n) (Nat.zero_lt_of_lt p.1.1.2) p.1.1.1 p.1.2.1 -
            fkIsingSquareSampledImaginaryPart embedding Phi n
              (fkIsingSquareRadialPatchPrimalNodeVertex n (m n) (hm n) p)| < eta := by
  intro eta heta
  have hfull := fkIsingSquare_physicalPrimitive_uniform_convergence_to_imPhi
    embedding Phi upper lower harmonic
    (fkIsingSquareGrowingRadialPrimalPrimitive m hm base) eps
    hupper hlower hharmonic hupperBoundary hlowerBoundary hsandwich
    heps hdirichlet eta heta
  filter_upwards [hfull, hmpos] with n hnconv hmn
  intro p
  rw [← fkIsingSquareGrowingRadialPrimalPrimitive_apply m hm base n hmn p]
  exact hnconv (fkIsingSquareRadialPatchPrimalNodeVertex n (m n) (hm n) p)


def fkIsingSquareRadialPatchLaplacian
    (H : Nat → Nat → Real) (i j : Nat) : Real :=
  H (i + 1) j + H (i - 1) j + H i (j + 1) + H i (j - 1) - 4 * H i j



theorem fkIsingSquareRadialPatchPrimitive_laplacian_nonneg_of_even
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi0 : 0 < i) (hi1 : i + 1 ≤ m)
    (hj0 : 0 < j) (hj1 : j + 1 ≤ m)
    (heven : Even (i + j)) :
    0 ≤ fkIsingSquareRadialPatchLaplacian
      (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j := by
  have hi : i < m := by omega
  have hj : j < m := by omega
  have hleftOdd : ¬ Even (i - 1 + j) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hdownOdd : ¬ Even (i + (j - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hr := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos i j hi (by omega)
  have hl := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos (i - 1) j (by omega) (by omega)
  have hu := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos i j
  have hd := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos i (j - 1)
  simp only [fkIsingSquareRadialPatchHorizontalSignedIncrement,
    fkIsingSquareRadialPatchVerticalSignedIncrement, heven, hleftOdd,
    hdownOdd, if_true, if_false] at hr hl hu hd
  have hr0 := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j)
  have hl0 := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos (i - 1) j)
  have hu0 := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j)
  have hd0 := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i (j - 1))
  simp only [fkIsingSquareRadialPatchLaplacian]
  have hiSub : i - 1 + 1 = i := by omega
  have hjSub : j - 1 + 1 = j := by omega
  rw [hiSub] at hl
  rw [hjSub] at hd
  linarith



theorem fkIsingSquareRadialPatchPrimitive_laplacian_nonpos_of_odd
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi0 : 0 < i) (hi1 : i + 1 ≤ m)
    (hj0 : 0 < j) (hj1 : j + 1 ≤ m)
    (hodd : ¬ Even (i + j)) :
    fkIsingSquareRadialPatchLaplacian
      (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j ≤ 0 := by
  have hi : i < m := by omega
  have hj : j < m := by omega
  have hleftEven : Even (i - 1 + j) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hdownEven : Even (i + (j - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hr := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos i j hi (by omega)
  have hl := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos (i - 1) j (by omega) (by omega)
  have hu := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos i j
  have hd := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos i (j - 1)
  simp only [fkIsingSquareRadialPatchHorizontalSignedIncrement,
    fkIsingSquareRadialPatchVerticalSignedIncrement, hodd, hleftEven,
    hdownEven, if_true, if_false] at hr hl hu hd
  have hr0 := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j)
  have hl0 := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos (i - 1) j)
  have hu0 := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j)
  have hd0 := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i (j - 1))
  simp only [fkIsingSquareRadialPatchLaplacian]
  have hiSub : i - 1 + 1 = i := by omega
  have hjSub : j - 1 + 1 = j := by omega
  rw [hiSub] at hl
  rw [hjSub] at hd
  linarith

end

end StatMech.Universality
