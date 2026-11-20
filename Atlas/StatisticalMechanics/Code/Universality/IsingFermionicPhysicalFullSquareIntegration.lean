/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalFullSquareIncidence
import Code.Universality.IsingFermionicDiamondIntegration









namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def FKIsingSquareFullDiamond (n : Nat) (q : Int × Int) : Prop :=
  -(2 * (n : Int)) ≤ q.1 + q.2 ∧ q.1 + q.2 ≤ 2 * (n : Int) ∧
    -(2 * (n : Int)) ≤ q.1 - q.2 ∧ q.1 - q.2 ≤ 2 * (n : Int)

theorem fkIsingSquareFullRadialNodeCoordinate_mem_diamond
    (n : Nat) (z : FKIsingSquareFullRadialNode n) :
    FKIsingSquareFullDiamond n
      (fkIsingSquareFullRadialNodeCoordinate n z) := by
  cases z with
  | inl x =>
      have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
      have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
      simp [FKIsingSquareFullDiamond,
        fkIsingSquareFullRadialNodeCoordinate,
        fkIsingSquareFullVertexCoordinate]
      omega
  | inr c =>
      have hc := fkIsingSquareInteriorCellKey_interior n c
      simp [fkIsingSquareInteriorFaceKey] at hc
      simp [FKIsingSquareFullDiamond,
        fkIsingSquareFullRadialNodeCoordinate,
        fkIsingSquareFullFaceCoordinate]
      omega

private theorem natAbs_le_of_int_bounds {n : Nat} {z : Int}
    (h0 : -(n : Int) ≤ z) (h1 : z ≤ (n : Int)) : z.natAbs ≤ n := by
  have h : |z| ≤ (n : Int) := abs_le.mpr ⟨h0, h1⟩
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h

theorem fkIsingSquareFull_exists_node_of_mem_diamond
    (n : Nat) (q : Int × Int) (hq : FKIsingSquareFullDiamond n q) :
    ∃ z : FKIsingSquareFullRadialNode n,
      fkIsingSquareFullRadialNodeCoordinate n z = q := by
  rcases hq with ⟨hsum0, hsum1, hdiff0, hdiff1⟩
  rcases (q.1 + q.2).even_or_odd with heven | hodd
  · rcases heven with ⟨a, ha⟩
    let b : Int := q.1 - a
    have ha0 : -(n : Int) ≤ a := by omega
    have ha1 : a ≤ (n : Int) := by omega
    have hb0 : -(n : Int) ≤ b := by
      dsimp [b]
      omega
    have hb1 : b ≤ (n : Int) := by
      dsimp [b]
      omega
    let x : FKIsingSquareFullVertexNode n :=
      ⟨![a, b], by
        intro k
        fin_cases k
        · exact natAbs_le_of_int_bounds ha0 ha1
        · exact natAbs_le_of_int_bounds hb0 hb1⟩
    refine ⟨Sum.inl x, ?_⟩
    apply Prod.ext <;>
      simp [fkIsingSquareFullRadialNodeCoordinate,
        fkIsingSquareFullVertexCoordinate, x, b] <;>
      omega
  · rcases hodd with ⟨a, ha⟩
    let b : Int := q.1 - a - 1
    have ha0 : -(n : Int) ≤ a := by omega
    have ha1 : a < (n : Int) := by omega
    have hb0 : -(n : Int) ≤ b := by
      dsimp [b]
      omega
    have hb1 : b < (n : Int) := by
      dsimp [b]
      omega
    have hp : fkIsingSquareInteriorFaceKey n (a, b) := by
      exact ⟨ha0, ha1, hb0, hb1⟩
    let c : FKIsingSquareFullFaceNode n :=
      fkIsingSquareFullFaceOfKey n (a, b) hp
    refine ⟨Sum.inr c, ?_⟩
    apply Prod.ext <;>
      simp [fkIsingSquareFullRadialNodeCoordinate,
        fkIsingSquareFullFaceCoordinate, c, b] <;>
      omega

noncomputable def fkIsingSquareFullRadialNodeOfCoordinate
    (n : Nat) (q : Int × Int) (hq : FKIsingSquareFullDiamond n q) :
    FKIsingSquareFullRadialNode n :=
  Classical.choose (fkIsingSquareFull_exists_node_of_mem_diamond n q hq)

@[simp] theorem fkIsingSquareFullRadialNodeOfCoordinate_coordinate
    (n : Nat) (q : Int × Int) (hq : FKIsingSquareFullDiamond n q) :
    fkIsingSquareFullRadialNodeCoordinate n
      (fkIsingSquareFullRadialNodeOfCoordinate n q hq) = q :=
  Classical.choose_spec (fkIsingSquareFull_exists_node_of_mem_diamond n q hq)

@[simp] theorem fkIsingSquareFullRadialNodeOfCoordinate_inverse
    (n : Nat) (z : FKIsingSquareFullRadialNode n) :
    fkIsingSquareFullRadialNodeOfCoordinate n
        (fkIsingSquareFullRadialNodeCoordinate n z)
        (fkIsingSquareFullRadialNodeCoordinate_mem_diamond n z) = z := by
  apply fkIsingSquareFullRadialNodeCoordinate_injective n
  exact fkIsingSquareFullRadialNodeOfCoordinate_coordinate n _ _

def FKIsingSquareFullDiamondCell (n : Nat) (q : Int × Int) : Prop :=
  FKIsingSquareFullDiamond n q ∧
    FKIsingSquareFullDiamond n (q.1 + 1, q.2) ∧
    FKIsingSquareFullDiamond n (q.1, q.2 + 1) ∧
    FKIsingSquareFullDiamond n (q.1 + 1, q.2 + 1)




noncomputable def fkIsingSquareFullRadialCellOfCoordinate
    (n : Nat) (q : Int × Int) (hq : FKIsingSquareFullDiamondCell n q) :
    FKIsingSquareInteriorRadialCell n := by
  classical
  have h00 := hq.1
  have h10 := hq.2.1
  have h01 := hq.2.2.1
  have h11 := hq.2.2.2
  simp [FKIsingSquareFullDiamond] at h00 h10 h01 h11
  by_cases heven : Even (q.1 + q.2)
  · let a : Int := Classical.choose heven
    have ha : q.1 + q.2 = a + a := Classical.choose_spec heven
    let b : Int := q.1 - a
    have ha0 : -(n : Int) ≤ a := by omega
    have ha1 : a < (n : Int) := by omega
    have hb0 : -(n : Int) < b := by
      dsimp [b]
      omega
    have hb1 : b < (n : Int) := by
      dsimp [b]
      omega
    let u : FKIsingSquareFullVertexNode n :=
      ⟨![a, b], by
        intro k
        fin_cases k
        · exact natAbs_le_of_int_bounds ha0 ha1.le
        · exact natAbs_le_of_int_bounds hb0.le hb1.le⟩
    have hu : fkIsingSquareDirectionAvailable n u .east := by
      change a < (n : Int)
      exact ha1
    let e := fkIsingSquareDirectionEdge n u .east hu
    refine ⟨e, ?_⟩
    intro s
    unfold fkIsingSquareWedgeFaceKey fkIsingSquareDartEndpoint
      fkIsingSquareDartDirection
    rw [fkIsingSquareOrientedEdge_directionEdge]
    cases s <;>
      simp [e, u, b, fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareSideCorner, fkIsingSquareInteriorFaceKey] <;>
      omega
  · have hodd : Odd (q.1 + q.2) := Int.not_even_iff_odd.mp heven
    let a : Int := Classical.choose hodd
    have ha : q.1 + q.2 = 2 * a + 1 := Classical.choose_spec hodd
    let b : Int := q.1 - a - 1
    have ha0 : -(n : Int) ≤ a := by omega
    have ha1 : a + 1 < (n : Int) := by omega
    have ha0' : -(n : Int) ≤ a + 1 := by omega
    have hb0 : -(n : Int) ≤ b := by
      dsimp [b]
      omega
    have hb1 : b < (n : Int) := by
      dsimp [b]
      omega
    let u : FKIsingSquareFullVertexNode n :=
      ⟨![a + 1, b], by
        intro k
        fin_cases k
        · exact natAbs_le_of_int_bounds ha0' ha1.le
        · exact natAbs_le_of_int_bounds hb0 hb1.le⟩
    have hu : fkIsingSquareDirectionAvailable n u .north := by
      change b < (n : Int)
      exact hb1
    let e := fkIsingSquareDirectionEdge n u .north hu
    refine ⟨e, ?_⟩
    intro s
    unfold fkIsingSquareWedgeFaceKey fkIsingSquareDartEndpoint
      fkIsingSquareDartDirection
    rw [fkIsingSquareOrientedEdge_directionEdge]
    cases s <;>
      simp [e, u, b, fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareSideCorner, fkIsingSquareInteriorFaceKey] <;>
      omega

def fkIsingSquareInteriorRadialIncidenceEndpointCoordinate
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) : Int × Int :=
  fkIsingSquareFullVertexCoordinate n
    (fkIsingSquareInteriorRadialEndpoint n hn e)

def fkIsingSquareInteriorRadialIncidenceFaceCoordinate
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) : Int × Int :=
  fkIsingSquareFullFaceCoordinate n
    (fkIsingSquareFullFaceOfRadialIncidence n hn e)

theorem fkIsingSquareFullRadialCellOfCoordinate_even_side_coordinates
    (n : Nat) (hn : 0 < n) (q : Int × Int)
    (hq : FKIsingSquareFullDiamondCell n q)
    (heven : Even (q.1 + q.2)) (s : FKIsingMedialSide) :
    fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn
        (fkIsingSquareInteriorRadialCellIncidence n hn
          (fkIsingSquareFullRadialCellOfCoordinate n q hq) s) =
        (match s with
        | .west | .south => q
        | .east | .north => (q.1 + 1, q.2 + 1)) ∧
      fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn
        (fkIsingSquareInteriorRadialCellIncidence n hn
          (fkIsingSquareFullRadialCellOfCoordinate n q hq) s) =
        (match s with
        | .west | .north => (q.1 + 1, q.2)
        | .east | .south => (q.1, q.2 + 1)) := by
  classical
  let a : Int := Classical.choose heven
  have ha : q.1 + q.2 = a + a := Classical.choose_spec heven
  let b : Int := q.1 - a
  have h00 := hq.1
  have h10 := hq.2.1
  have h01 := hq.2.2.1
  have h11 := hq.2.2.2
  simp [FKIsingSquareFullDiamond] at h00 h10 h01 h11
  have ha0 : -(n : Int) ≤ a := by omega
  have ha1 : a < (n : Int) := by omega
  have hb0 : -(n : Int) ≤ b := by
    dsimp [b]
    omega
  have hb1 : b ≤ (n : Int) := by
    dsimp [b]
    omega
  let u : FKIsingSquareFullVertexNode n :=
    ⟨![a, b], by
      intro k
      fin_cases k
      · exact natAbs_le_of_int_bounds ha0 ha1.le
      · exact natAbs_le_of_int_bounds hb0 hb1⟩
  have hu : fkIsingSquareDirectionAvailable n u .east := by
    change a < (n : Int)
    exact ha1
  have hcell : (fkIsingSquareFullRadialCellOfCoordinate n q hq).1 =
      fkIsingSquareDirectionEdge n u .east hu := by
    simp [fkIsingSquareFullRadialCellOfCoordinate, heven, u, b, a]
  have hend : fkIsingSquareDartEndpoint n
      ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s) =
      match (fkIsingSquareSideCorner s).1 with
      | .tail => u
      | .head => fkIsingSquareNeighbor n u .east hu := by
    unfold fkIsingSquareDartEndpoint
    rw [hcell, fkIsingSquareOrientedEdge_directionEdge]
    cases s <;> rfl
  have hdir : fkIsingSquareDartDirection n
      ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s) =
      match (fkIsingSquareSideCorner s).1 with
      | .tail => .east
      | .head => .west := by
    unfold fkIsingSquareDartDirection
    rw [hcell, fkIsingSquareOrientedEdge_directionEdge]
    cases s <;> rfl
  have hkey : fkIsingSquareWedgeFaceKey n
      ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s) =
      match s with
      | .west | .north => (a, b)
      | .east | .south => (a, b - 1) := by
    rw [show fkIsingSquareWedgeFaceKey n
        ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s) =
        (let v := fkIsingSquareDartEndpoint n
            ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s)
         match fkIsingSquareDartDirection n
              ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s),
             (fkIsingSquareSideCorner s).2 with
         | .east, .counterclockwise => (v.1 0, v.1 1)
         | .east, .clockwise => (v.1 0, v.1 1 - 1)
         | .north, .counterclockwise => (v.1 0 - 1, v.1 1)
         | .north, .clockwise => (v.1 0, v.1 1)
         | .west, .counterclockwise => (v.1 0 - 1, v.1 1 - 1)
         | .west, .clockwise => (v.1 0 - 1, v.1 1)
         | .south, .counterclockwise => (v.1 0, v.1 1 - 1)
         | .south, .clockwise => (v.1 0 - 1, v.1 1 - 1)) by rfl]
    rw [hend, hdir]
    cases s <;>
      simp [fkIsingSquareSideCorner, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, u, b]
  constructor
  · unfold fkIsingSquareInteriorRadialIncidenceEndpointCoordinate
    change fkIsingSquareFullVertexCoordinate n
        (fkIsingSquareDartEndpoint n
          ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s)) = _
    rw [hend]
    cases s <;>
      apply Prod.ext <;>
      simp [fkIsingSquareFullVertexCoordinate, fkIsingSquareSideCorner,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, u, b] <;>
      omega
  · unfold fkIsingSquareInteriorRadialIncidenceFaceCoordinate
      fkIsingSquareFullFaceCoordinate
    rw [fkIsingSquareFullFaceOfRadialIncidence_key]
    change
      let p := fkIsingSquareWedgeFaceKey n
        ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s)
      (p.1 + p.2 + 1, p.1 - p.2) = _
    rw [hkey]
    cases s <;> apply Prod.ext <;> simp [b] <;> omega

theorem fkIsingSquareFullRadialCellOfCoordinate_odd_side_coordinates
    (n : Nat) (hn : 0 < n) (q : Int × Int)
    (hq : FKIsingSquareFullDiamondCell n q)
    (hodd : ¬ Even (q.1 + q.2)) (s : FKIsingMedialSide) :
    fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn
        (fkIsingSquareInteriorRadialCellIncidence n hn
          (fkIsingSquareFullRadialCellOfCoordinate n q hq) s) =
        (match s with
        | .west | .south => (q.1, q.2 + 1)
        | .east | .north => (q.1 + 1, q.2)) ∧
      fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn
        (fkIsingSquareInteriorRadialCellIncidence n hn
          (fkIsingSquareFullRadialCellOfCoordinate n q hq) s) =
        (match s with
        | .west | .north => q
        | .east | .south => (q.1 + 1, q.2 + 1)) := by
  classical
  have ho : Odd (q.1 + q.2) := Int.not_even_iff_odd.mp hodd
  let a : Int := Classical.choose ho
  have ha : q.1 + q.2 = 2 * a + 1 := Classical.choose_spec ho
  let b : Int := q.1 - a - 1
  have h00 := hq.1
  have h10 := hq.2.1
  have h01 := hq.2.2.1
  have h11 := hq.2.2.2
  simp [FKIsingSquareFullDiamond] at h00 h10 h01 h11
  have ha0 : -(n : Int) ≤ a + 1 := by omega
  have ha1 : a + 1 < (n : Int) := by omega
  have hb0 : -(n : Int) ≤ b := by
    dsimp [b]
    omega
  have hb1 : b < (n : Int) := by
    dsimp [b]
    omega
  let u : FKIsingSquareFullVertexNode n :=
    ⟨![a + 1, b], by
      intro k
      fin_cases k
      · exact natAbs_le_of_int_bounds ha0 ha1.le
      · exact natAbs_le_of_int_bounds hb0 hb1.le⟩
  have hu : fkIsingSquareDirectionAvailable n u .north := by
    change b < (n : Int)
    exact hb1
  have hcell : (fkIsingSquareFullRadialCellOfCoordinate n q hq).1 =
      fkIsingSquareDirectionEdge n u .north hu := by
    simp [fkIsingSquareFullRadialCellOfCoordinate, hodd, u, b, a]
  have hend : fkIsingSquareDartEndpoint n
      ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s) =
      match (fkIsingSquareSideCorner s).1 with
      | .tail => u
      | .head => fkIsingSquareNeighbor n u .north hu := by
    unfold fkIsingSquareDartEndpoint
    rw [hcell, fkIsingSquareOrientedEdge_directionEdge]
    cases s <;> rfl
  have hdir : fkIsingSquareDartDirection n
      ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s) =
      match (fkIsingSquareSideCorner s).1 with
      | .tail => .north
      | .head => .south := by
    unfold fkIsingSquareDartDirection
    rw [hcell, fkIsingSquareOrientedEdge_directionEdge]
    cases s <;> rfl
  have hkey : fkIsingSquareWedgeFaceKey n
      ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s) =
      match s with
      | .west | .north => (a, b)
      | .east | .south => (a + 1, b) := by
    rw [show fkIsingSquareWedgeFaceKey n
        ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s) =
        (let v := fkIsingSquareDartEndpoint n
            ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s)
         match fkIsingSquareDartDirection n
              ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s),
             (fkIsingSquareSideCorner s).2 with
         | .east, .counterclockwise => (v.1 0, v.1 1)
         | .east, .clockwise => (v.1 0, v.1 1 - 1)
         | .north, .counterclockwise => (v.1 0 - 1, v.1 1)
         | .north, .clockwise => (v.1 0, v.1 1)
         | .west, .counterclockwise => (v.1 0 - 1, v.1 1 - 1)
         | .west, .clockwise => (v.1 0 - 1, v.1 1)
         | .south, .counterclockwise => (v.1 0, v.1 1 - 1)
         | .south, .clockwise => (v.1 0 - 1, v.1 1 - 1)) by rfl]
    rw [hend, hdir]
    cases s <;>
      simp [fkIsingSquareSideCorner, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, u, b]
  constructor
  · unfold fkIsingSquareInteriorRadialIncidenceEndpointCoordinate
    change fkIsingSquareFullVertexCoordinate n
        (fkIsingSquareDartEndpoint n
          ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s)) = _
    rw [hend]
    cases s <;>
      apply Prod.ext <;>
      simp [fkIsingSquareFullVertexCoordinate, fkIsingSquareSideCorner,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, u, b] <;>
      omega
  · unfold fkIsingSquareInteriorRadialIncidenceFaceCoordinate
      fkIsingSquareFullFaceCoordinate
    rw [fkIsingSquareFullFaceOfRadialIncidence_key]
    change
      let p := fkIsingSquareWedgeFaceKey n
        ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s)
      (p.1 + p.2 + 1, p.1 - p.2) = _
    rw [hkey]
    cases s <;> apply Prod.ext <;> simp [b] <;> omega



noncomputable def fkIsingSquareFullOrientedRadialIncrement
    (n : Nat) (hn : 0 < n) :
    FKIsingSquareFullRadialNode n → FKIsingSquareFullRadialNode n → Real := by
  classical
  intro a b
  exact match a, b with
    | .inl x, .inr c =>
        if h : FKIsingSquareFullRadiallyAdjacent n x c then
          fkIsingSquareInteriorRadialIncrement n hn
            (fkIsingSquareFullIncidenceOfAdjacent n hn x c h)
        else 0
    | .inr c, .inl x =>
        if h : FKIsingSquareFullRadiallyAdjacent n x c then
          -fkIsingSquareInteriorRadialIncrement n hn
            (fkIsingSquareFullIncidenceOfAdjacent n hn x c h)
        else 0
    | _, _ => 0

@[simp] theorem fkIsingSquareFullOrientedRadialIncrement_incidence
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    fkIsingSquareFullOrientedRadialIncrement n hn
        (.inl (fkIsingSquareInteriorRadialEndpoint n hn e))
        (.inr (fkIsingSquareFullFaceOfRadialIncidence n hn e)) =
      fkIsingSquareInteriorRadialIncrement n hn e := by
  rw [fkIsingSquareFullOrientedRadialIncrement]
  split
  · rw [fkIsingSquareFullIncidenceOfAdjacent_of_incidence n hn e]
  · rename_i h
    exact False.elim
      (h (fkIsingSquareFull_radiallyAdjacent_of_incidence n hn e))

@[simp] theorem fkIsingSquareFullOrientedRadialIncrement_incidence_reverse
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    fkIsingSquareFullOrientedRadialIncrement n hn
        (.inr (fkIsingSquareFullFaceOfRadialIncidence n hn e))
        (.inl (fkIsingSquareInteriorRadialEndpoint n hn e)) =
      -fkIsingSquareInteriorRadialIncrement n hn e := by
  rw [fkIsingSquareFullOrientedRadialIncrement]
  split
  · rw [fkIsingSquareFullIncidenceOfAdjacent_of_incidence n hn e]
  · rename_i h
    exact False.elim
      (h (fkIsingSquareFull_radiallyAdjacent_of_incidence n hn e))

theorem fkIsingSquareFullOrientedRadialIncrement_antisymm
    (n : Nat) (hn : 0 < n)
    (a b : FKIsingSquareFullRadialNode n) :
    fkIsingSquareFullOrientedRadialIncrement n hn a b =
      -fkIsingSquareFullOrientedRadialIncrement n hn b a := by
  classical
  cases a with
  | inl x =>
      cases b with
      | inl y => simp [fkIsingSquareFullOrientedRadialIncrement]
      | inr c =>
          by_cases h : FKIsingSquareFullRadiallyAdjacent n x c <;>
            simp [fkIsingSquareFullOrientedRadialIncrement, h]
  | inr c =>
      cases b with
      | inl x =>
          by_cases h : FKIsingSquareFullRadiallyAdjacent n x c <;>
            simp [fkIsingSquareFullOrientedRadialIncrement, h]
      | inr d => simp [fkIsingSquareFullOrientedRadialIncrement]

def fkIsingSquareFullOriginVertex (n : Nat) :
    FKIsingSquareFullVertexNode n := by
  refine ⟨![0, 0], ?_⟩
  intro k
  fin_cases k <;> simp




noncomputable def fkIsingSquareFullRadialNodeAtCoordinate
    (n : Nat) (q : Int × Int) : FKIsingSquareFullRadialNode n := by
  classical
  exact if hq : FKIsingSquareFullDiamond n q then
      fkIsingSquareFullRadialNodeOfCoordinate n q hq
    else .inl (fkIsingSquareFullOriginVertex n)

@[simp] theorem fkIsingSquareFullRadialNodeAtCoordinate_coordinate
    (n : Nat) (q : Int × Int) (hq : FKIsingSquareFullDiamond n q) :
    fkIsingSquareFullRadialNodeCoordinate n
        (fkIsingSquareFullRadialNodeAtCoordinate n q) = q := by
  simp [fkIsingSquareFullRadialNodeAtCoordinate, hq]

theorem fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex
    (n : Nat) (q : Int × Int) (hq : FKIsingSquareFullDiamond n q)
    (x : FKIsingSquareFullVertexNode n)
    (hx : fkIsingSquareFullVertexCoordinate n x = q) :
    fkIsingSquareFullRadialNodeAtCoordinate n q = .inl x := by
  apply fkIsingSquareFullRadialNodeCoordinate_injective n
  rw [fkIsingSquareFullRadialNodeAtCoordinate_coordinate n q hq]
  simpa [fkIsingSquareFullRadialNodeCoordinate] using hx.symm

theorem fkIsingSquareFullRadialNodeAtCoordinate_eq_face
    (n : Nat) (q : Int × Int) (hq : FKIsingSquareFullDiamond n q)
    (c : FKIsingSquareFullFaceNode n)
    (hc : fkIsingSquareFullFaceCoordinate n c = q) :
    fkIsingSquareFullRadialNodeAtCoordinate n q = .inr c := by
  apply fkIsingSquareFullRadialNodeCoordinate_injective n
  rw [fkIsingSquareFullRadialNodeAtCoordinate_coordinate n q hq]
  simpa [fkIsingSquareFullRadialNodeCoordinate] using hc.symm

noncomputable def fkIsingSquareFullHorizontalIncrement
    (n : Nat) (hn : 0 < n) (q : Int × Int) : Real :=
  fkIsingSquareFullOrientedRadialIncrement n hn
    (fkIsingSquareFullRadialNodeAtCoordinate n q)
    (fkIsingSquareFullRadialNodeAtCoordinate n (q.1 + 1, q.2))

noncomputable def fkIsingSquareFullVerticalIncrement
    (n : Nat) (hn : 0 < n) (q : Int × Int) : Real :=
  fkIsingSquareFullOrientedRadialIncrement n hn
    (fkIsingSquareFullRadialNodeAtCoordinate n q)
    (fkIsingSquareFullRadialNodeAtCoordinate n (q.1, q.2 + 1))

theorem fkIsingSquareFull_increment_closed
    (n : Nat) (hn : 0 < n) (q : Int × Int)
    (hq : FKIsingSquareFullDiamondCell n q) :
    fkIsingSquareFullVerticalIncrement n hn q +
        fkIsingSquareFullHorizontalIncrement n hn (q.1, q.2 + 1) =
      fkIsingSquareFullHorizontalIncrement n hn q +
        fkIsingSquareFullVerticalIncrement n hn (q.1 + 1, q.2) := by
  let C := fkIsingSquareFullRadialCellOfCoordinate n q hq
  let west := fkIsingSquareInteriorRadialCellIncidence n hn C .west
  let east := fkIsingSquareInteriorRadialCellIncidence n hn C .east
  let south := fkIsingSquareInteriorRadialCellIncidence n hn C .south
  let north := fkIsingSquareInteriorRadialCellIncidence n hn C .north
  have hclosed := fkIsingSquareInteriorRadialCell_increment_closed n hn C
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
    have hH0 : fkIsingSquareFullHorizontalIncrement n hn q =
        fkIsingSquareInteriorRadialIncrement n hn west := by
      simp [fkIsingSquareFullHorizontalIncrement, nqW, neW]
    have hH1 : fkIsingSquareFullHorizontalIncrement n hn (q.1, q.2 + 1) =
        -fkIsingSquareInteriorRadialIncrement n hn east := by
      simp [fkIsingSquareFullHorizontalIncrement, nnE, nneE]
    have hV0 : fkIsingSquareFullVerticalIncrement n hn q =
        fkIsingSquareInteriorRadialIncrement n hn south := by
      simp [fkIsingSquareFullVerticalIncrement, nqS, nnS]
    have hV1 : fkIsingSquareFullVerticalIncrement n hn (q.1 + 1, q.2) =
        -fkIsingSquareInteriorRadialIncrement n hn north := by
      simp [fkIsingSquareFullVerticalIncrement, neN, nneN]
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
    have hH0 : fkIsingSquareFullHorizontalIncrement n hn q =
        -fkIsingSquareInteriorRadialIncrement n hn north := by
      simp [fkIsingSquareFullHorizontalIncrement, nqN, neN]
    have hH1 : fkIsingSquareFullHorizontalIncrement n hn (q.1, q.2 + 1) =
        fkIsingSquareInteriorRadialIncrement n hn south := by
      simp [fkIsingSquareFullHorizontalIncrement, nnS, nneS]
    have hV0 : fkIsingSquareFullVerticalIncrement n hn q =
        -fkIsingSquareInteriorRadialIncrement n hn west := by
      simp [fkIsingSquareFullVerticalIncrement, nqW, nnW]
    have hV1 : fkIsingSquareFullVerticalIncrement n hn (q.1 + 1, q.2) =
        fkIsingSquareInteriorRadialIncrement n hn east := by
      simp [fkIsingSquareFullVerticalIncrement, neE, nneE]
    rw [hH0, hH1, hV0, hV1]
    change _ + _ = _ + _ at hclosed
    linarith

end

end StatMech.Universality
