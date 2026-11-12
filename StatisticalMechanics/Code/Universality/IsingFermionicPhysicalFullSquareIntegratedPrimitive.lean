/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalFullSquareIntegration
import Code.Universality.IsingFermionicPhysicalFullSquarePrimitive
import Code.Universality.IsingFermionicPhysicalGhostEnergy









namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareFullIntegratedPrimitive

def shiftedCoordinate (n i j : Nat) : Int × Int :=
  ((i : Int) - 2 * (n : Int), (j : Int) - 2 * (n : Int))

def coordinateIndex (n : Nat) (q : Int × Int) : Nat × Nat :=
  ((q.1 + 2 * (n : Int)).toNat, (q.2 + 2 * (n : Int)).toNat)

theorem shiftedCoordinate_coordinateIndex
    (n : Nat) (q : Int × Int) (hq : FKIsingSquareFullDiamond n q) :
    shiftedCoordinate n (coordinateIndex n q).1 (coordinateIndex n q).2 = q := by
  have hq0 : -(2 * (n : Int)) ≤ q.1 := by
    rcases hq with ⟨h0, h1, h2, h3⟩
    omega
  have hq1 : -(2 * (n : Int)) ≤ q.2 := by
    rcases hq with ⟨h0, h1, h2, h3⟩
    omega
  apply Prod.ext <;>
    simp [shiftedCoordinate, coordinateIndex] <;>
    omega

theorem diamondCell_of_row_interval
    (n i j k : Nat)
    (h0 : FKIsingSquareFullDiamond n (shiftedCoordinate n i j))
    (h1 : FKIsingSquareFullDiamond n (shiftedCoordinate n i (j + 1)))
    (hk : (2 * n ≤ k ∧ k < i) ∨ (i ≤ k ∧ k < 2 * n)) :
    FKIsingSquareFullDiamondCell n (shiftedCoordinate n k j) := by
  rcases h0 with ⟨h00, h01, h02, h03⟩
  rcases h1 with ⟨h10, h11, h12, h13⟩
  simp [shiftedCoordinate] at h00 h01 h02 h03 h10 h11 h12 h13
  simp only [FKIsingSquareFullDiamondCell, FKIsingSquareFullDiamond,
    shiftedCoordinate]
  rcases hk with hk | hk
  all_goals repeat' apply And.intro
  all_goals omega

noncomputable def horizontalNat
    (n : Nat) (hn : 0 < n) (i j : Nat) : Real :=
  fkIsingSquareFullHorizontalIncrement n hn (shiftedCoordinate n i j)

noncomputable def verticalNat
    (n : Nat) (hn : 0 < n) (i j : Nat) : Real :=
  fkIsingSquareFullVerticalIncrement n hn (shiftedCoordinate n i j)

noncomputable def primitiveNat
    (n : Nat) (hn : 0 < n) (i j : Nat) : Real :=
  isingCenteredPrimitive (horizontalNat n hn) (verticalNat n hn) (2 * n) i j

theorem primitiveNat_horizontal_increment
    (n : Nat) (hn : 0 < n) (i j : Nat) :
    primitiveNat n hn (i + 1) j - primitiveNat n hn i j =
      horizontalNat n hn i j := by
  exact isingCenteredPrimitive_horizontal_increment
    (horizontalNat n hn) (verticalNat n hn) (2 * n) i j

theorem primitiveNat_vertical_increment
    (n : Nat) (hn : 0 < n) (i j : Nat)
    (h0 : FKIsingSquareFullDiamond n (shiftedCoordinate n i j))
    (h1 : FKIsingSquareFullDiamond n (shiftedCoordinate n i (j + 1))) :
    primitiveNat n hn i (j + 1) - primitiveNat n hn i j =
      verticalNat n hn i j := by
  apply isingCenteredPrimitive_vertical_increment
  intro k hk
  have hcell := diamondCell_of_row_interval n i j k h0 h1 hk
  have hx : shiftedCoordinate n (k + 1) j =
      ((shiftedCoordinate n k j).1 + 1, (shiftedCoordinate n k j).2) := by
    apply Prod.ext <;> simp [shiftedCoordinate] <;> omega
  have hy : shiftedCoordinate n k (j + 1) =
      ((shiftedCoordinate n k j).1, (shiftedCoordinate n k j).2 + 1) := by
    apply Prod.ext <;> simp [shiftedCoordinate] <;> omega
  dsimp [verticalNat, horizontalNat]
  rw [hx, hy]
  exact fkIsingSquareFull_increment_closed n hn (shiftedCoordinate n k j) hcell

theorem coordinateIndex_east
    (n : Nat) (q : Int × Int) (hq : FKIsingSquareFullDiamond n q) :
    coordinateIndex n (q.1 + 1, q.2) =
      ((coordinateIndex n q).1 + 1, (coordinateIndex n q).2) := by
  have hq0 : 0 ≤ q.1 + 2 * (n : Int) := by
    rcases hq with ⟨h0, h1, h2, h3⟩
    omega
  apply Prod.ext <;> simp [coordinateIndex] <;> omega

theorem coordinateIndex_north
    (n : Nat) (q : Int × Int) (hq : FKIsingSquareFullDiamond n q) :
    coordinateIndex n (q.1, q.2 + 1) =
      ((coordinateIndex n q).1, (coordinateIndex n q).2 + 1) := by
  have hq1 : 0 ≤ q.2 + 2 * (n : Int) := by
    rcases hq with ⟨h0, h1, h2, h3⟩
    omega
  apply Prod.ext <;> simp [coordinateIndex] <;> omega

noncomputable def coordinatePrimitive
    (n : Nat) (hn : 0 < n) (q : Int × Int) : Real :=
  primitiveNat n hn (coordinateIndex n q).1 (coordinateIndex n q).2

theorem coordinatePrimitive_horizontal_increment
    (n : Nat) (hn : 0 < n) (q : Int × Int)
    (hq : FKIsingSquareFullDiamond n q) :
    coordinatePrimitive n hn (q.1 + 1, q.2) - coordinatePrimitive n hn q =
      fkIsingSquareFullHorizontalIncrement n hn q := by
  unfold coordinatePrimitive
  rw [coordinateIndex_east n q hq]
  have h := primitiveNat_horizontal_increment n hn
    (coordinateIndex n q).1 (coordinateIndex n q).2
  simpa [horizontalNat, shiftedCoordinate_coordinateIndex n q hq] using h

theorem coordinatePrimitive_vertical_increment
    (n : Nat) (hn : 0 < n) (q : Int × Int)
    (hq : FKIsingSquareFullDiamond n q)
    (hqN : FKIsingSquareFullDiamond n (q.1, q.2 + 1)) :
    coordinatePrimitive n hn (q.1, q.2 + 1) - coordinatePrimitive n hn q =
      fkIsingSquareFullVerticalIncrement n hn q := by
  let ij := coordinateIndex n q
  have hshift : shiftedCoordinate n ij.1 ij.2 = q :=
    shiftedCoordinate_coordinateIndex n q hq
  have hshiftN : shiftedCoordinate n ij.1 (ij.2 + 1) = (q.1, q.2 + 1) := by
    have hy : shiftedCoordinate n ij.1 (ij.2 + 1) =
        ((shiftedCoordinate n ij.1 ij.2).1,
          (shiftedCoordinate n ij.1 ij.2).2 + 1) := by
      apply Prod.ext <;> simp [shiftedCoordinate] <;> omega
    rw [hy, hshift]
  unfold coordinatePrimitive
  rw [coordinateIndex_north n q hq]
  have h := primitiveNat_vertical_increment n hn ij.1 ij.2
    (hshift ▸ hq) (hshiftN ▸ hqN)
  simpa [ij, verticalNat, hshift] using h

noncomputable def vertexPrimitive
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareFullVertexNode n) : Real :=
  coordinatePrimitive n hn (fkIsingSquareFullVertexCoordinate n x) -
    coordinatePrimitive n hn
      (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))

noncomputable def facePrimitive
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n) : Real :=
  coordinatePrimitive n hn (fkIsingSquareFullFaceCoordinate n c) -
    coordinatePrimitive n hn
      (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))

theorem compatible (n : Nat) (hn : 0 < n) :
    FKIsingSquareFullPrimitiveCompatible n hn
      (vertexPrimitive n hn) (facePrimitive n hn) := by
  intro e
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
  · have h := coordinatePrimitive_horizontal_increment n hn u hu
    have hcu : fkIsingSquareFullRadialNodeAtCoordinate n (u.1 + 1, u.2) =
        .inr c := by simpa [hE] using hcp
    have hinc : fkIsingSquareFullHorizontalIncrement n hn u =
        fkIsingSquareInteriorRadialIncrement n hn e := by
      unfold fkIsingSquareFullHorizontalIncrement
      rw [hxu, hcu]
      simpa [x, c] using
        fkIsingSquareFullOrientedRadialIncrement_incidence n hn e
    simp only [vertexPrimitive, facePrimitive]
    change (coordinatePrimitive n hn p - coordinatePrimitive n hn
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) -
      (coordinatePrimitive n hn u - coordinatePrimitive n hn
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) = _
    rw [hE]
    linarith
  · have h := coordinatePrimitive_vertical_increment n hn u hu (hN ▸ hp)
    have hcu : fkIsingSquareFullRadialNodeAtCoordinate n (u.1, u.2 + 1) =
        .inr c := by simpa [hN] using hcp
    have hinc : fkIsingSquareFullVerticalIncrement n hn u =
        fkIsingSquareInteriorRadialIncrement n hn e := by
      unfold fkIsingSquareFullVerticalIncrement
      rw [hxu, hcu]
      simpa [x, c] using
        fkIsingSquareFullOrientedRadialIncrement_incidence n hn e
    simp only [vertexPrimitive, facePrimitive]
    change (coordinatePrimitive n hn p - coordinatePrimitive n hn
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) -
      (coordinatePrimitive n hn u - coordinatePrimitive n hn
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) = _
    rw [hN]
    linarith
  · have hW0 := congrArg Prod.fst hW
    have hW1 := congrArg Prod.snd hW
    have hu' : u = (p.1 + 1, p.2) := by
      apply Prod.ext <;> omega
    have h := coordinatePrimitive_horizontal_increment n hn p hp
    have hup : fkIsingSquareFullRadialNodeAtCoordinate n (p.1 + 1, p.2) =
        .inl x := by simpa [hu'] using hxu
    have hinc : fkIsingSquareFullHorizontalIncrement n hn p =
        -fkIsingSquareInteriorRadialIncrement n hn e := by
      unfold fkIsingSquareFullHorizontalIncrement
      rw [hcp, hup]
      simpa [x, c] using
        fkIsingSquareFullOrientedRadialIncrement_incidence_reverse n hn e
    simp only [vertexPrimitive, facePrimitive]
    change (coordinatePrimitive n hn p - coordinatePrimitive n hn
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) -
      (coordinatePrimitive n hn u - coordinatePrimitive n hn
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) = _
    rw [hu']
    linarith
  · have hS0 := congrArg Prod.fst hS
    have hS1 := congrArg Prod.snd hS
    have hu' : u = (p.1, p.2 + 1) := by
      apply Prod.ext <;> omega
    have h := coordinatePrimitive_vertical_increment n hn p hp (hu' ▸ hu)
    have hup : fkIsingSquareFullRadialNodeAtCoordinate n (p.1, p.2 + 1) =
        .inl x := by simpa [hu'] using hxu
    have hinc : fkIsingSquareFullVerticalIncrement n hn p =
        -fkIsingSquareInteriorRadialIncrement n hn e := by
      unfold fkIsingSquareFullVerticalIncrement
      rw [hcp, hup]
      simpa [x, c] using
        fkIsingSquareFullOrientedRadialIncrement_incidence_reverse n hn e
    simp only [vertexPrimitive, facePrimitive]
    change (coordinatePrimitive n hn p - coordinatePrimitive n hn
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) -
      (coordinatePrimitive n hn u - coordinatePrimitive n hn
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) = _
    rw [hu']
    linarith

theorem face_sub_vertex
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    facePrimitive n hn (fkIsingSquareFullFaceOfRadialIncidence n hn e) -
        vertexPrimitive n hn (fkIsingSquareInteriorRadialEndpoint n hn e) =
      fkIsingSquareInteriorRadialIncrement n hn e :=
  compatible n hn e



theorem vertex_le_face
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    vertexPrimitive n hn (fkIsingSquareInteriorRadialEndpoint n hn e) ≤
      facePrimitive n hn
        (fkIsingSquareFullFaceOfRadialIncidence n hn e) := by
  have hgap := face_sub_vertex n hn e
  have hnonneg := fkIsingSquareInteriorRadialIncrement_nonneg n hn e
  linarith


theorem face_sub_vertex_nonneg
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    0 ≤ facePrimitive n hn
        (fkIsingSquareFullFaceOfRadialIncidence n hn e) -
      vertexPrimitive n hn
        (fkIsingSquareInteriorRadialEndpoint n hn e) := by
  rw [face_sub_vertex n hn e]
  exact fkIsingSquareInteriorRadialIncrement_nonneg n hn e

@[simp] theorem markedB_base (n : Nat) (hn : 0 < n) :
    vertexPrimitive n hn (fkIsingSquareMarkedB n) = 0 := by
  simp [vertexPrimitive]

noncomputable def radialPatchBase
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) : Real :=
  fkIsingSquareRadialPatchFullValue n m hm hm2
    (vertexPrimitive n hn) (facePrimitive n hn)
    ⟨0, by omega⟩ ⟨0, by omega⟩

theorem radialPatchPrimalValue_eq
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (p : FKIsingSquareRadialPatchPrimalNode m) :
    fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega)
        (radialPatchBase n m hn hm hm2) p =
      vertexPrimitive n hn
        (fkIsingSquareRadialPatchPrimalFullVertex n m hm p) := by
  exact fkIsingSquareRadialPatchPrimalValue_eq_full_of_compatible
    n m hn hm hm2 (radialPatchBase n m hn hm hm2)
      (vertexPrimitive n hn) (facePrimitive n hn) (compatible n hn) rfl p

theorem radialPatchDualValue_eq
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (q : FKIsingSquareRadialPatchDualNode m) :
    fkIsingSquareRadialPatchDualValue n m hn hm (by omega)
        (radialPatchBase n m hn hm hm2) q =
      facePrimitive n hn
        (fkIsingSquareRadialPatchDualFullFace n m hm hm2 q) := by
  exact fkIsingSquareRadialPatchDualValue_eq_full_of_compatible
    n m hn hm hm2 (radialPatchBase n m hn hm hm2)
      (vertexPrimitive n hn) (facePrimitive n hn) (compatible n hn) rfl q

theorem radialPatch_unitRange_of_fullSquareGhost
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hvertexModified : ∀ x,
      ¬ fkIsingSquareFullVertexFixedBoundary n x →
        isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
            (vertexPrimitive n hn) x +
          isingFermionicGhostRate
            (fkIsingSquareFullVertexGhostMultiplicity n) x *
              (1 - vertexPrimitive n hn x) ≤ 0)
    (hvertexFixed : ∀ x,
      fkIsingSquareFullVertexFixedBoundary n x →
        0 ≤ vertexPrimitive n hn x)
    (hfaceModified : ∀ c,
      ¬ fkIsingSquareFullFaceFixedBoundary n c →
        0 ≤ isingFiniteGraphLaplacian
          (fkIsingSquareFullFaceGraph n) (facePrimitive n hn) c +
            isingFermionicGhostRate
              (fkIsingSquareFullFaceGhostMultiplicity n) c *
                (0 - facePrimitive n hn c))
    (hfaceFixed : ∀ c,
      fkIsingSquareFullFaceFixedBoundary n c →
        facePrimitive n hn c ≤ 1) :
    (∀ p, 0 ≤ fkIsingSquareRadialPatchPrimalValue
          n m hn hm (by omega) (radialPatchBase n m hn hm hm2) p ∧
        fkIsingSquareRadialPatchPrimalValue
          n m hn hm (by omega) (radialPatchBase n m hn hm hm2) p ≤ 1) ∧
      (∀ q, 0 ≤ fkIsingSquareRadialPatchDualValue
          n m hn hm (by omega) (radialPatchBase n m hn hm hm2) q ∧
        fkIsingSquareRadialPatchDualValue
          n m hn hm (by omega) (radialPatchBase n m hn hm hm2) q ≤ 1) := by
  exact fkIsingSquareRadialPatch_unitRange_of_fullSquareGhost_compatible
    n m hn hm hm2 (radialPatchBase n m hn hm hm2)
      (vertexPrimitive n hn) (facePrimitive n hn)
      hvertexModified hvertexFixed hfaceModified hfaceFixed
      (compatible n hn) rfl

theorem radialPatch_deepCell_energy_sq_le_of_boundary
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (hr : 0 < r)
    (hvertexModified : ∀ x,
      ¬ fkIsingSquareFullVertexFixedBoundary n x →
        isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
            (vertexPrimitive n hn) x +
          isingFermionicGhostRate
            (fkIsingSquareFullVertexGhostMultiplicity n) x *
              (1 - vertexPrimitive n hn x) ≤ 0)
    (hvertexFixed : ∀ x,
      fkIsingSquareFullVertexFixedBoundary n x →
        0 ≤ vertexPrimitive n hn x)
    (hfaceModified : ∀ c,
      ¬ fkIsingSquareFullFaceFixedBoundary n c →
        0 ≤ isingFiniteGraphLaplacian
          (fkIsingSquareFullFaceGraph n) (facePrimitive n hn) c +
            isingFermionicGhostRate
              (fkIsingSquareFullFaceGhostMultiplicity n) c *
                (0 - facePrimitive n hn c))
    (hfaceFixed : ∀ c,
      fkIsingSquareFullFaceFixedBoundary n c →
        facePrimitive n hn c ≤ 1) :
    (((1 / (m : Real)) ^ 2) *
        ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm
                ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ /
              (Real.sqrt (2 * (1 / (m : Real))) : Complex))) ^ 2 ≤
      256 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
  exact
    fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_of_fullSquareGhost_compatible
      n m hn hm hm2 r hr (radialPatchBase n m hn hm hm2)
      (vertexPrimitive n hn) (facePrimitive n hn)
      hvertexModified hvertexFixed hfaceModified hfaceFixed
      (compatible n hn) rfl

end FKIsingSquareFullIntegratedPrimitive

end


end StatMech.Universality
