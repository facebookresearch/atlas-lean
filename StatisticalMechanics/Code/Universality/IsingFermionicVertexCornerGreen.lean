/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicCappedTent











namespace StatMech.Universality

open Finset SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm


abbrev FKIsingSquareAvailableDirection
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :=
  {d : FKIsingSquareDirection // fkIsingSquareDirectionAvailable n x d}

noncomputable local instance fkIsingSquareAvailableDirectionFintype
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    Fintype (FKIsingSquareAvailableDirection n x) :=
  Fintype.ofFinite _


def fkIsingSquareAvailableNeighbor
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (d : FKIsingSquareAvailableDirection n x) :
    FKIsingSquareFullVertexNode n :=
  fkIsingSquareNeighbor n x d.1 d.2

theorem fkIsingSquareAvailableNeighbor_injective
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    Function.Injective (fkIsingSquareAvailableNeighbor n x) := by
  intro d e h
  apply Subtype.ext
  exact fkIsingSquareNeighbor_injective n x d.1 e.1 d.2 e.2 h



theorem fkIsingSquareFullVertex_neighborFinset_eq_available
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    [Fintype ↑((fkIsingSquareFullVertexGraph n).neighborSet x)] :
    (fkIsingSquareFullVertexGraph n).neighborFinset x =
      Finset.univ.image (fkIsingSquareAvailableNeighbor n x) := by
  classical
  ext y
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_image]
  constructor
  · intro hxy
    change (hypercubicLattice 2).Adj x.1 y.1 at hxy
    rcases adj_neighbor_cases x.1 y.1 hxy with h | h | h | h
    · have hd : fkIsingSquareDirectionAvailable n x .west := by
        have hy := fkIsingSquareVertex_coordinate_bounds n y 0
        have hk := congrFun h 0
        simp [Pi.add_apply] at hk
        simp [fkIsingSquareDirectionAvailable]
        omega
      refine ⟨⟨.west, hd⟩, Finset.mem_univ _, ?_⟩
      symm
      apply Subtype.ext
      funext k
      fin_cases k
      · have hk := congrFun h 0
        simp [Pi.add_apply] at hk
        change y.1 0 = x.1 0 - 1
        omega
      · have hk := congrFun h 1
        simpa [fkIsingSquareAvailableNeighbor, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, Pi.add_apply] using hk.symm
    · have hd : fkIsingSquareDirectionAvailable n x .east := by
        have hy := fkIsingSquareVertex_coordinate_bounds n y 0
        have hk := congrFun h 0
        simp [Pi.add_apply] at hk
        simp [fkIsingSquareDirectionAvailable]
        omega
      refine ⟨⟨.east, hd⟩, Finset.mem_univ _, ?_⟩
      symm
      apply Subtype.ext
      funext k
      fin_cases k
      · have hk := congrFun h 0
        simp [Pi.add_apply] at hk
        change y.1 0 = x.1 0 + 1
        omega
      · have hk := congrFun h 1
        simpa [fkIsingSquareAvailableNeighbor, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, Pi.add_apply] using hk.symm
    · have hd : fkIsingSquareDirectionAvailable n x .south := by
        have hy := fkIsingSquareVertex_coordinate_bounds n y 1
        have hk := congrFun h 1
        simp [Pi.add_apply] at hk
        simp [fkIsingSquareDirectionAvailable]
        omega
      refine ⟨⟨.south, hd⟩, Finset.mem_univ _, ?_⟩
      symm
      apply Subtype.ext
      funext k
      fin_cases k
      · have hk := congrFun h 0
        simpa [fkIsingSquareAvailableNeighbor, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, Pi.add_apply] using hk.symm
      · have hk := congrFun h 1
        simp [Pi.add_apply] at hk
        change y.1 1 = x.1 1 - 1
        omega
    · have hd : fkIsingSquareDirectionAvailable n x .north := by
        have hy := fkIsingSquareVertex_coordinate_bounds n y 1
        have hk := congrFun h 1
        simp [Pi.add_apply] at hk
        simp [fkIsingSquareDirectionAvailable]
        omega
      refine ⟨⟨.north, hd⟩, Finset.mem_univ _, ?_⟩
      symm
      apply Subtype.ext
      funext k
      fin_cases k
      · have hk := congrFun h 0
        simpa [fkIsingSquareAvailableNeighbor, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, Pi.add_apply] using hk.symm
      · have hk := congrFun h 1
        simp [Pi.add_apply] at hk
        change y.1 1 = x.1 1 + 1
        omega
  · rintro ⟨d, -, rfl⟩
    exact fkIsingSquare_adj_neighbor n x d.1 d.2



theorem fullVertex_laplacian_eq_sum_available
    (n : Nat) (F : FKIsingSquareFullVertexNode n -> Real)
    (x : FKIsingSquareFullVertexNode n) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) F x =
      ∑ d : FKIsingSquareAvailableDirection n x,
        (F (fkIsingSquareAvailableNeighbor n x d) - F x) := by
  classical
  unfold isingFiniteGraphLaplacian
  rw [fkIsingSquareFullVertex_neighborFinset_eq_available]
  rw [Finset.sum_image]
  exact fun d _ e _ h => fkIsingSquareAvailableNeighbor_injective n x h



noncomputable def fullVertexDirectionIncrement
    (n : Nat) (F : FKIsingSquareFullVertexNode n -> Real)
    (x : FKIsingSquareFullVertexNode n) (d : FKIsingSquareDirection) : Real := by
  classical
  exact if h : fkIsingSquareDirectionAvailable n x d then
      F (fkIsingSquareNeighbor n x d h) - F x
    else 0


theorem fullVertex_laplacian_eq_directionIncrements
    (n : Nat) (F : FKIsingSquareFullVertexNode n -> Real)
    (x : FKIsingSquareFullVertexNode n) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) F x =
      fullVertexDirectionIncrement n F x .east +
        fullVertexDirectionIncrement n F x .north +
        fullVertexDirectionIncrement n F x .west +
        fullVertexDirectionIncrement n F x .south := by
  classical
  rw [fullVertex_laplacian_eq_sum_available]
  calc
    (∑ d : FKIsingSquareAvailableDirection n x,
        (F (fkIsingSquareAvailableNeighbor n x d) - F x)) =
        ∑ d : FKIsingSquareAvailableDirection n x,
          fullVertexDirectionIncrement n F x d.1 := by
      apply Finset.sum_congr rfl
      intro d _
      simp [fullVertexDirectionIncrement, d.2,
        fkIsingSquareAvailableNeighbor]
    _ = ∑ d ∈ Finset.univ.filter
          (fkIsingSquareDirectionAvailable n x),
          fullVertexDirectionIncrement n F x d := by
      symm
      exact Finset.sum_subtype
        (Finset.univ.filter (fkIsingSquareDirectionAvailable n x))
        (by simp) (fullVertexDirectionIncrement n F x)
    _ = _ := by
      rw [show (Finset.univ : Finset FKIsingSquareDirection) =
          {.east, .north, .west, .south} by
        ext d
        fin_cases d <;> simp]
      rw [Finset.sum_filter]
      by_cases he : fkIsingSquareDirectionAvailable n x .east <;>
        by_cases hnorth : fkIsingSquareDirectionAvailable n x .north <;>
        by_cases hw : fkIsingSquareDirectionAvailable n x .west <;>
        by_cases hs : fkIsingSquareDirectionAvailable n x .south <;>
        simp [he, hnorth, hw, hs, fullVertexDirectionIncrement]
      all_goals ring


def fullVertexColumnIndex
    (n : Nat) (x : FKIsingSquareFullVertexNode n) : Nat :=
  (x.1 0 + (n : Int)).toNat


def fullVertexRowIndex
    (n : Nat) (x : FKIsingSquareFullVertexNode n) : Nat :=
  (x.1 1 + (n : Int)).toNat

theorem fullVertexColumnIndex_coe
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    (fullVertexColumnIndex n x : Int) = x.1 0 + (n : Int) := by
  unfold fullVertexColumnIndex
  rw [Int.toNat_of_nonneg]
  have hx := (fkIsingSquareVertex_coordinate_bounds n x 0).1
  omega

theorem fullVertexRowIndex_coe
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    (fullVertexRowIndex n x : Int) = x.1 1 + (n : Int) := by
  unfold fullVertexRowIndex
  rw [Int.toNat_of_nonneg]
  have hx := (fkIsingSquareVertex_coordinate_bounds n x 1).1
  omega

theorem fullVertexColumnIndex_le
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    fullVertexColumnIndex n x <= 2 * n := by
  have hx := (fkIsingSquareVertex_coordinate_bounds n x 0).2
  have hcoe := fullVertexColumnIndex_coe n x
  exact_mod_cast (show (fullVertexColumnIndex n x : Int) <=
      2 * (n : Int) by omega)

theorem fullVertexRowIndex_le
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    fullVertexRowIndex n x <= 2 * n := by
  have hx := (fkIsingSquareVertex_coordinate_bounds n x 1).2
  have hcoe := fullVertexRowIndex_coe n x
  exact_mod_cast (show (fullVertexRowIndex n x : Int) <=
      2 * (n : Int) by omega)

@[simp] theorem fullVertexColumnIndex_neighbor_east
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .east) :
    fullVertexColumnIndex n (fkIsingSquareNeighbor n x .east h) =
      fullVertexColumnIndex n x + 1 := by
  have hnext := fullVertexColumnIndex_coe n
    (fkIsingSquareNeighbor n x .east h)
  have hbase := fullVertexColumnIndex_coe n x
  apply Int.ofNat_inj.mp
  push_cast
  rw [hnext, hbase]
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  change x.1 0 + 1 + (n : Int) = x.1 0 + (n : Int) + 1
  ring

@[simp] theorem fullVertexColumnIndex_neighbor_west
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .west) :
    fullVertexColumnIndex n (fkIsingSquareNeighbor n x .west h) =
      fullVertexColumnIndex n x - 1 := by
  have hpos : 0 < fullVertexColumnIndex n x := by
    have hcoe := fullVertexColumnIndex_coe n x
    simp [fkIsingSquareDirectionAvailable] at h
    omega
  have hnext := fullVertexColumnIndex_coe n
    (fkIsingSquareNeighbor n x .west h)
  have hbase := fullVertexColumnIndex_coe n x
  apply Int.ofNat_inj.mp
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos))]
  push_cast
  rw [hnext, hbase]
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  change x.1 0 - 1 + (n : Int) = x.1 0 + (n : Int) - 1
  ring

@[simp] theorem fullVertexColumnIndex_neighbor_north
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .north) :
    fullVertexColumnIndex n (fkIsingSquareNeighbor n x .north h) =
      fullVertexColumnIndex n x := by
  have hnext := fullVertexColumnIndex_coe n
    (fkIsingSquareNeighbor n x .north h)
  have hbase := fullVertexColumnIndex_coe n x
  apply Int.ofNat_inj.mp
  rw [hnext, hbase]
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  change x.1 0 = x.1 0
  rfl

@[simp] theorem fullVertexColumnIndex_neighbor_south
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .south) :
    fullVertexColumnIndex n (fkIsingSquareNeighbor n x .south h) =
      fullVertexColumnIndex n x := by
  have hnext := fullVertexColumnIndex_coe n
    (fkIsingSquareNeighbor n x .south h)
  have hbase := fullVertexColumnIndex_coe n x
  apply Int.ofNat_inj.mp
  rw [hnext, hbase]
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  change x.1 0 = x.1 0
  rfl

@[simp] theorem fullVertexRowIndex_neighbor_north
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .north) :
    fullVertexRowIndex n (fkIsingSquareNeighbor n x .north h) =
      fullVertexRowIndex n x + 1 := by
  have hnext := fullVertexRowIndex_coe n
    (fkIsingSquareNeighbor n x .north h)
  have hbase := fullVertexRowIndex_coe n x
  apply Int.ofNat_inj.mp
  push_cast
  rw [hnext, hbase]
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  change x.1 1 + 1 + (n : Int) = x.1 1 + (n : Int) + 1
  ring

@[simp] theorem fullVertexRowIndex_neighbor_south
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .south) :
    fullVertexRowIndex n (fkIsingSquareNeighbor n x .south h) =
      fullVertexRowIndex n x - 1 := by
  have hpos : 0 < fullVertexRowIndex n x := by
    have hcoe := fullVertexRowIndex_coe n x
    simp [fkIsingSquareDirectionAvailable] at h
    omega
  have hnext := fullVertexRowIndex_coe n
    (fkIsingSquareNeighbor n x .south h)
  have hbase := fullVertexRowIndex_coe n x
  apply Int.ofNat_inj.mp
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos))]
  push_cast
  rw [hnext, hbase]
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  change x.1 1 - 1 + (n : Int) = x.1 1 + (n : Int) - 1
  ring

@[simp] theorem fullVertexRowIndex_neighbor_east
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .east) :
    fullVertexRowIndex n (fkIsingSquareNeighbor n x .east h) =
      fullVertexRowIndex n x := by
  have hnext := fullVertexRowIndex_coe n
    (fkIsingSquareNeighbor n x .east h)
  have hbase := fullVertexRowIndex_coe n x
  apply Int.ofNat_inj.mp
  rw [hnext, hbase]
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  change x.1 1 = x.1 1
  rfl

@[simp] theorem fullVertexRowIndex_neighbor_west
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .west) :
    fullVertexRowIndex n (fkIsingSquareNeighbor n x .west h) =
      fullVertexRowIndex n x := by
  have hnext := fullVertexRowIndex_coe n
    (fkIsingSquareNeighbor n x .west h)
  have hbase := fullVertexRowIndex_coe n x
  apply Int.ofNat_inj.mp
  rw [hnext, hbase]
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  change x.1 1 = x.1 1
  rfl



theorem fullVertexColumnFunction_laplacian
    (n : Nat) (F : Nat -> Real) (x : FKIsingSquareFullVertexNode n)
    (hleft : -(n : Int) < x.1 0) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => F (fullVertexColumnIndex n y)) x =
      if x.1 0 = (n : Int) then
        F (fullVertexColumnIndex n x - 1) - F (fullVertexColumnIndex n x)
      else
        F (fullVertexColumnIndex n x + 1) +
          F (fullVertexColumnIndex n x - 1) -
            2 * F (fullVertexColumnIndex n x) := by
  rw [fullVertex_laplacian_eq_directionIncrements]
  have hwest : fkIsingSquareDirectionAvailable n x .west := hleft
  have hcol : 0 < fullVertexColumnIndex n x := by
    have hcoe := fullVertexColumnIndex_coe n x
    omega
  have hnorth : fullVertexDirectionIncrement n
      (fun y => F (fullVertexColumnIndex n y)) x .north = 0 := by
    unfold fullVertexDirectionIncrement
    split_ifs with h
    · simp
    · rfl
  have hsouth : fullVertexDirectionIncrement n
      (fun y => F (fullVertexColumnIndex n y)) x .south = 0 := by
    unfold fullVertexDirectionIncrement
    split_ifs with h
    · simp
    · rfl
  rw [hnorth, hsouth]
  by_cases hright : x.1 0 = (n : Int)
  · have heast : Not (fkIsingSquareDirectionAvailable n x .east) := by
      simp [fkIsingSquareDirectionAvailable, hright]
    simp [fullVertexDirectionIncrement, hright, heast, hwest]
  · have heast : fkIsingSquareDirectionAvailable n x .east := by
      have hx := (fkIsingSquareVertex_coordinate_bounds n x 0).2
      simp [fkIsingSquareDirectionAvailable]
      omega
    simp [fullVertexDirectionIncrement, hright, heast, hwest]
    ring




theorem fullVertexRowFunction_laplacian
    (n : Nat) (F : Nat -> Real) (x : FKIsingSquareFullVertexNode n)
    (hn : 0 < n) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => F (fullVertexRowIndex n y)) x =
      if x.1 1 = -(n : Int) then
        F (fullVertexRowIndex n x + 1) - F (fullVertexRowIndex n x)
      else if x.1 1 = (n : Int) then
        F (fullVertexRowIndex n x - 1) - F (fullVertexRowIndex n x)
      else
        F (fullVertexRowIndex n x + 1) +
          F (fullVertexRowIndex n x - 1) -
            2 * F (fullVertexRowIndex n x) := by
  rw [fullVertex_laplacian_eq_directionIncrements]
  have heast : fullVertexDirectionIncrement n
      (fun y => F (fullVertexRowIndex n y)) x .east = 0 := by
    unfold fullVertexDirectionIncrement
    split_ifs with h
    · simp
    · rfl
  have hwest : fullVertexDirectionIncrement n
      (fun y => F (fullVertexRowIndex n y)) x .west = 0 := by
    unfold fullVertexDirectionIncrement
    split_ifs with h
    · simp
    · rfl
  rw [heast, hwest]
  by_cases hbottom : x.1 1 = -(n : Int)
  · have hsouth : Not (fkIsingSquareDirectionAvailable n x .south) := by
      simp [fkIsingSquareDirectionAvailable, hbottom]
    have hnorth : fkIsingSquareDirectionAvailable n x .north := by
      simp [fkIsingSquareDirectionAvailable, hbottom]
      omega
    simp [fullVertexDirectionIncrement, hbottom, hsouth, hnorth]
  · by_cases htop : x.1 1 = (n : Int)
    · have hnorth : Not (fkIsingSquareDirectionAvailable n x .north) := by
        simp [fkIsingSquareDirectionAvailable, htop]
      have hsouth : fkIsingSquareDirectionAvailable n x .south := by
        simp [fkIsingSquareDirectionAvailable, htop]
        omega
      simp [fullVertexDirectionIncrement, htop, hsouth, hnorth,
        hn.ne']
    · have hnorth : fkIsingSquareDirectionAvailable n x .north := by
        have hx := fkIsingSquareVertex_coordinate_bounds n x 1
        simp [fkIsingSquareDirectionAvailable]
        omega
      have hsouth : fkIsingSquareDirectionAvailable n x .south := by
        have hx := fkIsingSquareVertex_coordinate_bounds n x 1
        simp [fkIsingSquareDirectionAvailable]
        omega
      simp [fullVertexDirectionIncrement, hbottom, htop, hsouth, hnorth]
      ring



def fullVertexRightGhostMultiplicity
    (n : Nat) (x : FKIsingSquareFullVertexNode n) : Nat :=
  if x.1 0 = (n : Int) then 1 else 0


def fullVertexVerticalGhostMultiplicity
    (n : Nat) (x : FKIsingSquareFullVertexNode n) : Nat :=
  (if x.1 1 = -(n : Int) then 1 else 0) +
    (if x.1 1 = (n : Int) then 1 else 0)

theorem fullVertexGhostRate_split
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    isingFermionicGhostRate (fullVertexRightGhostMultiplicity n) x +
        isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) x =
      isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n) x := by
  unfold isingFermionicGhostRate fullVertexRightGhostMultiplicity
    fullVertexVerticalGhostMultiplicity
    fkIsingSquareFullVertexGhostMultiplicity
  push_cast
  ring


def vertexLeftColumnCap
    {n : Nat} (source x : FKIsingSquareFullVertexNode n) : Real :=
  isingNatCappedTent (fullVertexColumnIndex n source)
    (fullVertexColumnIndex n x)


noncomputable def vertexBottomRowRobinCap
    {n : Nat} (source x : FKIsingSquareFullVertexNode n) : Real :=
  isingNatCappedRobinTent isingFermionicGhostCoefficient
    (fullVertexRowIndex n source) (fullVertexRowIndex n x)


noncomputable def isingNatReverseCappedRobinTent
    (coefficient : Real) (top source i : Nat) : Real :=
  isingNatReverseCappedTent top source i + 1 / coefficient

noncomputable def vertexTopRowRobinCap
    (n : Nat) (source x : FKIsingSquareFullVertexNode n) : Real :=
  isingNatReverseCappedRobinTent isingFermionicGhostCoefficient (2 * n)
    (fullVertexRowIndex n source) (fullVertexRowIndex n x)

theorem vertexLeftColumnCap_nonneg
    {n : Nat} (source x : FKIsingSquareFullVertexNode n) :
    0 <= vertexLeftColumnCap source x :=
  isingNatCappedTent_nonneg _ _

theorem vertexBottomRowRobinCap_nonneg
    {n : Nat} (source x : FKIsingSquareFullVertexNode n) :
    0 <= vertexBottomRowRobinCap source x :=
  isingNatCappedRobinTent_nonneg isingFermionicGhostCoefficient
    isingFermionicGhostCoefficient_pos _ _

theorem isingNatReverseCappedRobinTent_nonneg
    (coefficient : Real) (hcoefficient : 0 < coefficient)
    (top source i : Nat) :
    0 <= isingNatReverseCappedRobinTent coefficient top source i := by
  exact add_nonneg (isingNatReverseCappedTent_nonneg top source i)
    (one_div_nonneg.mpr hcoefficient.le)

theorem vertexTopRowRobinCap_nonneg
    (n : Nat) (source x : FKIsingSquareFullVertexNode n) :
    0 <= vertexTopRowRobinCap n source x :=
  isingNatReverseCappedRobinTent_nonneg isingFermionicGhostCoefficient
    isingFermionicGhostCoefficient_pos _ _ _

theorem isingNatReverseCappedRobinTent_secondDifference_nonpos
    (coefficient : Real) (top source i : Nat)
    (hi : 0 < i) (hitop : i < top) :
    isingNatReverseCappedRobinTent coefficient top source (i + 1) +
        isingNatReverseCappedRobinTent coefficient top source (i - 1) -
          2 * isingNatReverseCappedRobinTent coefficient top source i <= 0 := by
  unfold isingNatReverseCappedRobinTent
  have h := isingNatReverseCappedTent_secondDifference_nonpos
    top source i hi hitop
  linarith

theorem isingNatReverseCappedRobinTent_secondDifference_source
    (coefficient : Real) (top source : Nat)
    (hsource : 0 < source) (hsourceTop : source < top) :
    isingNatReverseCappedRobinTent coefficient top source (source + 1) +
        isingNatReverseCappedRobinTent coefficient top source (source - 1) -
          2 * isingNatReverseCappedRobinTent coefficient top source source =
      -1 := by
  unfold isingNatReverseCappedRobinTent
  have h := isingNatReverseCappedTent_secondDifference_source
    top source hsource hsourceTop
  linarith


theorem isingNatReverseCappedRobinTent_right_balance
    (coefficient : Real) (hcoefficient : 0 < coefficient)
    (top source : Nat) (hsourceTop : source < top) :
    isingNatReverseCappedRobinTent coefficient top source (top - 1) -
        isingNatReverseCappedRobinTent coefficient top source top -
          coefficient *
            isingNatReverseCappedRobinTent coefficient top source top = 0 := by
  unfold isingNatReverseCappedRobinTent isingNatReverseCappedTent
    isingNatCappedTent
  have htop : top - (top - 1) = 1 := by omega
  have hcap : 1 <= top - source := by omega
  simp [htop, hcap]
  field_simp [hcoefficient.ne']
  ring



theorem isingNatReverseCappedRobinTent_successor_sub_nonpos
    (coefficient : Real) (top source i : Nat) :
    isingNatReverseCappedRobinTent coefficient top source (i + 1) -
      isingNatReverseCappedRobinTent coefficient top source i <= 0 := by
  unfold isingNatReverseCappedRobinTent isingNatReverseCappedTent
  have hnext : top - (i + 1) = top - i - 1 := by omega
  rw [hnext]
  have h := isingNatCappedTent_predecessor_sub_nonpos
    (top - source) (top - i)
  linarith

theorem vertexLeftColumnCap_modifiedLaplacian_nonpos
    (n : Nat) (source x : FKIsingSquareFullVertexNode n)
    (hx : Not (fkIsingSquareFullVertexFixedBoundary n x)) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (vertexLeftColumnCap source) x -
      isingFermionicGhostRate (fullVertexRightGhostMultiplicity n) x *
        vertexLeftColumnCap source x <= 0 := by
  have hleft : -(n : Int) < x.1 0 := by
    have hb := (fkIsingSquareVertex_coordinate_bounds n x 0).1
    by_contra h
    apply hx
    simpa [fkIsingSquareFullVertexFixedBoundary,
      fkIsingSquareWiredArc] using (show x.1 0 = -(n : Int) by omega)
  have hindex : 0 < fullVertexColumnIndex n x := by
    have hcoe := fullVertexColumnIndex_coe n x
    omega
  change isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => isingNatCappedTent (fullVertexColumnIndex n source)
          (fullVertexColumnIndex n y)) x -
      isingFermionicGhostRate (fullVertexRightGhostMultiplicity n) x *
        isingNatCappedTent (fullVertexColumnIndex n source)
          (fullVertexColumnIndex n x) <= 0
  rw [fullVertexColumnFunction_laplacian n _ x hleft]
  by_cases hright : x.1 0 = (n : Int)
  · have hpred := isingNatCappedTent_predecessor_sub_nonpos
      (fullVertexColumnIndex n source) (fullVertexColumnIndex n x)
    have hkill : 0 <= isingFermionicGhostCoefficient *
        isingNatCappedTent (fullVertexColumnIndex n source)
          (fullVertexColumnIndex n x) :=
      mul_nonneg isingFermionicGhostCoefficient_pos.le
        (isingNatCappedTent_nonneg _ _)
    simp [hright, isingFermionicGhostRate,
      fullVertexRightGhostMultiplicity]
    linarith
  · have hsecond := isingNatCappedTent_secondDifference_nonpos
      (fullVertexColumnIndex n source) (fullVertexColumnIndex n x) hindex
    simpa [hright, isingFermionicGhostRate,
      fullVertexRightGhostMultiplicity] using hsecond

theorem vertexLeftColumnCap_modifiedLaplacian_source
    (n : Nat) (source : FKIsingSquareFullVertexNode n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
    (hright : source.1 0 < (n : Int)) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (vertexLeftColumnCap source) source -
      isingFermionicGhostRate (fullVertexRightGhostMultiplicity n) source *
        vertexLeftColumnCap source source = -1 := by
  have hleft : -(n : Int) < source.1 0 := by
    have hb := (fkIsingSquareVertex_coordinate_bounds n source 0).1
    by_contra h
    apply hfixed
    simpa [fkIsingSquareFullVertexFixedBoundary,
      fkIsingSquareWiredArc] using
        (show source.1 0 = -(n : Int) by omega)
  have hindex : 0 < fullVertexColumnIndex n source := by
    have hcoe := fullVertexColumnIndex_coe n source
    omega
  have hnotRight : Not (source.1 0 = (n : Int)) := by omega
  change isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => isingNatCappedTent (fullVertexColumnIndex n source)
          (fullVertexColumnIndex n y)) source -
      isingFermionicGhostRate (fullVertexRightGhostMultiplicity n) source *
        isingNatCappedTent (fullVertexColumnIndex n source)
          (fullVertexColumnIndex n source) = -1
  rw [fullVertexColumnFunction_laplacian n _ source hleft]
  simpa [hnotRight, isingFermionicGhostRate,
    fullVertexRightGhostMultiplicity] using
      isingNatCappedTent_secondDifference_source
        (fullVertexColumnIndex n source) hindex

theorem vertexBottomRowRobinCap_modifiedLaplacian_nonpos
    (n : Nat) (source x : FKIsingSquareFullVertexNode n)
    (hn : 0 < n) (hsourceBottom : -(n : Int) < source.1 1) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (vertexBottomRowRobinCap source) x -
      isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) x *
        vertexBottomRowRobinCap source x <= 0 := by
  have hsourceIndex : 0 < fullVertexRowIndex n source := by
    have hcoe := fullVertexRowIndex_coe n source
    omega
  change isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => isingNatCappedRobinTent isingFermionicGhostCoefficient
          (fullVertexRowIndex n source) (fullVertexRowIndex n y)) x -
      isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) x *
        isingNatCappedRobinTent isingFermionicGhostCoefficient
          (fullVertexRowIndex n source) (fullVertexRowIndex n x) <= 0
  rw [fullVertexRowFunction_laplacian n _ x hn]
  by_cases hbottom : x.1 1 = -(n : Int)
  · have hindex : fullVertexRowIndex n x = 0 := by
      have hcoe := fullVertexRowIndex_coe n x
      omega
    have hbalance := isingNatCappedRobinTent_left_balance
      isingFermionicGhostCoefficient isingFermionicGhostCoefficient_pos
      (fullVertexRowIndex n source) hsourceIndex
    simp [hbottom, hn.ne', hindex, isingFermionicGhostRate,
      fullVertexVerticalGhostMultiplicity] at hbalance ⊢
    linarith
  · by_cases htop : x.1 1 = (n : Int)
    · have hpred := isingNatCappedRobinTent_predecessor_sub_nonpos
        isingFermionicGhostCoefficient (fullVertexRowIndex n source)
          (fullVertexRowIndex n x)
      have hkill : 0 <= isingFermionicGhostCoefficient *
          isingNatCappedRobinTent isingFermionicGhostCoefficient
            (fullVertexRowIndex n source) (fullVertexRowIndex n x) :=
        mul_nonneg isingFermionicGhostCoefficient_pos.le
          (isingNatCappedRobinTent_nonneg isingFermionicGhostCoefficient
            isingFermionicGhostCoefficient_pos _ _)
      simp [htop, hn.ne', isingFermionicGhostRate,
        fullVertexVerticalGhostMultiplicity]
      linarith
    · have hindex : 0 < fullVertexRowIndex n x := by
        have hcoe := fullVertexRowIndex_coe n x
        omega
      have hsecond := isingNatCappedRobinTent_secondDifference_nonpos
        isingFermionicGhostCoefficient (fullVertexRowIndex n source)
          (fullVertexRowIndex n x) hindex
      simpa [hbottom, htop, isingFermionicGhostRate,
        fullVertexVerticalGhostMultiplicity] using hsecond

theorem vertexBottomRowRobinCap_modifiedLaplacian_source
    (n : Nat) (source : FKIsingSquareFullVertexNode n)
    (hn : 0 < n)
    (hbottom : -(n : Int) < source.1 1)
    (htop : source.1 1 < (n : Int)) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (vertexBottomRowRobinCap source) source -
      isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) source *
        vertexBottomRowRobinCap source source = -1 := by
  have hindex : 0 < fullVertexRowIndex n source := by
    have hcoe := fullVertexRowIndex_coe n source
    omega
  have hnotBottom : Not (source.1 1 = -(n : Int)) := by omega
  have hnotTop : Not (source.1 1 = (n : Int)) := by omega
  change isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => isingNatCappedRobinTent isingFermionicGhostCoefficient
          (fullVertexRowIndex n source) (fullVertexRowIndex n y)) source -
      isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) source *
        isingNatCappedRobinTent isingFermionicGhostCoefficient
          (fullVertexRowIndex n source) (fullVertexRowIndex n source) = -1
  rw [fullVertexRowFunction_laplacian n _ source hn]
  simpa [hnotBottom, hnotTop, isingFermionicGhostRate,
    fullVertexVerticalGhostMultiplicity] using
      isingNatCappedRobinTent_secondDifference_source
        isingFermionicGhostCoefficient (fullVertexRowIndex n source) hindex

theorem vertexTopRowRobinCap_modifiedLaplacian_nonpos
    (n : Nat) (source x : FKIsingSquareFullVertexNode n)
    (hn : 0 < n) (hsourceTop : source.1 1 < (n : Int)) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (vertexTopRowRobinCap n source) x -
      isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) x *
        vertexTopRowRobinCap n source x <= 0 := by
  have hsourceIndex : fullVertexRowIndex n source < 2 * n := by
    have hcoe := fullVertexRowIndex_coe n source
    exact_mod_cast (show (fullVertexRowIndex n source : Int) <
        2 * (n : Int) by omega)
  change isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => isingNatReverseCappedRobinTent
          isingFermionicGhostCoefficient (2 * n)
          (fullVertexRowIndex n source) (fullVertexRowIndex n y)) x -
      isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) x *
        isingNatReverseCappedRobinTent isingFermionicGhostCoefficient (2 * n)
          (fullVertexRowIndex n source) (fullVertexRowIndex n x) <= 0
  rw [fullVertexRowFunction_laplacian n _ x hn]
  by_cases hbottom : x.1 1 = -(n : Int)
  · have hindex : fullVertexRowIndex n x = 0 := by
      have hcoe := fullVertexRowIndex_coe n x
      omega
    have hsucc := isingNatReverseCappedRobinTent_successor_sub_nonpos
      isingFermionicGhostCoefficient (2 * n) (fullVertexRowIndex n source)
        (fullVertexRowIndex n x)
    have hkill : 0 <= isingFermionicGhostCoefficient *
        isingNatReverseCappedRobinTent isingFermionicGhostCoefficient (2 * n)
          (fullVertexRowIndex n source) (fullVertexRowIndex n x) :=
      mul_nonneg isingFermionicGhostCoefficient_pos.le
        (isingNatReverseCappedRobinTent_nonneg
          isingFermionicGhostCoefficient isingFermionicGhostCoefficient_pos
          _ _ _)
    simp [hbottom, hn.ne', isingFermionicGhostRate,
      fullVertexVerticalGhostMultiplicity]
    linarith
  · by_cases htop : x.1 1 = (n : Int)
    · have hindex : fullVertexRowIndex n x = 2 * n := by
        have hcoe := fullVertexRowIndex_coe n x
        exact_mod_cast (show (fullVertexRowIndex n x : Int) =
            2 * (n : Int) by omega)
      have hbalance := isingNatReverseCappedRobinTent_right_balance
        isingFermionicGhostCoefficient isingFermionicGhostCoefficient_pos
        (2 * n) (fullVertexRowIndex n source) hsourceIndex
      simp [htop, hn.ne', hindex, isingFermionicGhostRate,
        fullVertexVerticalGhostMultiplicity] at hbalance ⊢
      linarith
    · have hindexPos : 0 < fullVertexRowIndex n x := by
        have hcoe := fullVertexRowIndex_coe n x
        omega
      have hindexTop : fullVertexRowIndex n x < 2 * n := by
        have hcoe := fullVertexRowIndex_coe n x
        have hxBound := (fkIsingSquareVertex_coordinate_bounds n x 1).2
        have hint : (fullVertexRowIndex n x : Int) <
            ((2 * n : Nat) : Int) := by
          push_cast
          omega
        exact_mod_cast hint
      have hsecond :=
        isingNatReverseCappedRobinTent_secondDifference_nonpos
          isingFermionicGhostCoefficient (2 * n)
          (fullVertexRowIndex n source) (fullVertexRowIndex n x)
          hindexPos hindexTop
      simpa [hbottom, htop, isingFermionicGhostRate,
        fullVertexVerticalGhostMultiplicity] using hsecond

theorem vertexTopRowRobinCap_modifiedLaplacian_source
    (n : Nat) (source : FKIsingSquareFullVertexNode n)
    (hn : 0 < n)
    (hbottom : -(n : Int) < source.1 1)
    (htop : source.1 1 < (n : Int)) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (vertexTopRowRobinCap n source) source -
      isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) source *
        vertexTopRowRobinCap n source source = -1 := by
  have hindexPos : 0 < fullVertexRowIndex n source := by
    have hcoe := fullVertexRowIndex_coe n source
    omega
  have hindexTop : fullVertexRowIndex n source < 2 * n := by
    have hcoe := fullVertexRowIndex_coe n source
    exact_mod_cast (show (fullVertexRowIndex n source : Int) <
        2 * (n : Int) by omega)
  have hnotBottom : Not (source.1 1 = -(n : Int)) := by omega
  have hnotTop : Not (source.1 1 = (n : Int)) := by omega
  change isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => isingNatReverseCappedRobinTent
          isingFermionicGhostCoefficient (2 * n)
          (fullVertexRowIndex n source) (fullVertexRowIndex n y)) source -
      isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) source *
        isingNatReverseCappedRobinTent isingFermionicGhostCoefficient (2 * n)
          (fullVertexRowIndex n source) (fullVertexRowIndex n source) = -1
  rw [fullVertexRowFunction_laplacian n _ source hn]
  simpa [hnotBottom, hnotTop, isingFermionicGhostRate,
    fullVertexVerticalGhostMultiplicity] using
      isingNatReverseCappedRobinTent_secondDifference_source
        isingFermionicGhostCoefficient (2 * n)
        (fullVertexRowIndex n source) hindexPos hindexTop

theorem fullVertex_adj_columnIndex_eq_or_rowIndex_eq
    (n : Nat) (x y : FKIsingSquareFullVertexNode n)
    (hxy : (fkIsingSquareFullVertexGraph n).Adj x y) :
    fullVertexColumnIndex n x = fullVertexColumnIndex n y ∨
      fullVertexRowIndex n x = fullVertexRowIndex n y := by
  change (hypercubicLattice 2).Adj x.1 y.1 at hxy
  rcases adj_neighbor_cases x.1 y.1 hxy with h | h | h | h
  · right
    apply Int.ofNat_inj.mp
    rw [fullVertexRowIndex_coe, fullVertexRowIndex_coe]
    have hk := congrFun h 1
    simp [Pi.add_apply] at hk
    omega
  · right
    apply Int.ofNat_inj.mp
    rw [fullVertexRowIndex_coe, fullVertexRowIndex_coe]
    have hk := congrFun h 1
    simp [Pi.add_apply] at hk
    omega
  · left
    apply Int.ofNat_inj.mp
    rw [fullVertexColumnIndex_coe, fullVertexColumnIndex_coe]
    have hk := congrFun h 0
    simp [Pi.add_apply] at hk
    omega
  · left
    apply Int.ofNat_inj.mp
    rw [fullVertexColumnIndex_coe, fullVertexColumnIndex_coe]
    have hk := congrFun h 0
    simp [Pi.add_apply] at hk
    omega

theorem vertexLowerCornerCaps_edgewise
    (n : Nat) (source x y : FKIsingSquareFullVertexNode n)
    (hxy : (fkIsingSquareFullVertexGraph n).Adj x y) :
    (vertexLeftColumnCap source y - vertexLeftColumnCap source x) *
        (vertexBottomRowRobinCap source y -
          vertexBottomRowRobinCap source x) = 0 := by
  rcases fullVertex_adj_columnIndex_eq_or_rowIndex_eq n x y hxy with hcol | hrow
  · simp [vertexLeftColumnCap, hcol]
  · simp [vertexBottomRowRobinCap, hrow]

theorem vertexUpperCornerCaps_edgewise
    (n : Nat) (source x y : FKIsingSquareFullVertexNode n)
    (hxy : (fkIsingSquareFullVertexGraph n).Adj x y) :
    (vertexLeftColumnCap source y - vertexLeftColumnCap source x) *
        (vertexTopRowRobinCap n source y -
          vertexTopRowRobinCap n source x) = 0 := by
  rcases fullVertex_adj_columnIndex_eq_or_rowIndex_eq n x y hxy with hcol | hrow
  · simp [vertexLeftColumnCap, hcol]
  · simp [vertexTopRowRobinCap, hrow]



theorem vertexPointPoissonBarrier_le_lowerLeftProduct
    (n : Nat) (source x : FKIsingSquareFullVertexNode n)
    (hn : 0 < n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
    (hright : source.1 0 < (n : Int))
    (hbottom : -(n : Int) < source.1 1)
    (htop : source.1 1 < (n : Int)) :
    vertexPointPoissonBarrier n (some source) (some x) <=
      vertexLeftColumnCap source x * vertexBottomRowRobinCap source x /
        (vertexLeftColumnCap source source +
          vertexBottomRowRobinCap source source) := by
  letI : Nonempty (FKIsingSquareFullVertexNode n) := ⟨source⟩
  have hreach : forall c : FKIsingSquareFullVertexNode n, exists b,
      (fkIsingSquareFullVertexFixedBoundary n b ∨
        0 < isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) b) ∧
        (fkIsingSquareFullVertexGraph n).Reachable c b := by
    intro c
    obtain ⟨b, hb, hcb⟩ := fkIsingSquareFullVertex_reaches_fixed_or_ghost n c
    refine ⟨b, ?_, hcb⟩
    rcases hb with hb | hb
    · exact Or.inl hb
    · exact Or.inr ((isingFermionicGhostRate_pos_iff
        (fkIsingSquareFullVertexGhostMultiplicity n) b).2 hb)
  have hleft : -(n : Int) < source.1 0 := by
    have hb := (fkIsingSquareVertex_coordinate_bounds n source 0).1
    by_contra h
    apply hfixed
    simpa [fkIsingSquareFullVertexFixedBoundary,
      fkIsingSquareWiredArc] using
        (show source.1 0 = -(n : Int) by omega)
  have hcolIndex : 0 < fullVertexColumnIndex n source := by
    have hcoe := fullVertexColumnIndex_coe n source
    omega
  have hden : 0 < vertexLeftColumnCap source source +
      vertexBottomRowRobinCap source source := by
    have hcol : 0 < vertexLeftColumnCap source source := by
      simpa [vertexLeftColumnCap, isingNatCappedTent_self] using
        (show (0 : Real) < fullVertexColumnIndex n source by positivity)
    linarith [vertexBottomRowRobinCap_nonneg source source]
  change isingFiniteWeightedPointPoissonBarrier
      (isingFiniteGhostGraph (fkIsingSquareFullVertexGraph n)
        (isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n)))
      (isingFiniteGhostConductance (fkIsingSquareFullVertexGraph n)
        (isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n)))
      (isingFiniteGhostBoundaryWith
        (fkIsingSquareFullVertexFixedBoundary n))
      _ _ _ (some source) (some x) <= _
  apply isingFiniteGhostPointPoissonBarrier_le_splitProduct
    (fkIsingSquareFullVertexGraph n)
    (isingFermionicGhostRate
      (fkIsingSquareFullVertexGhostMultiplicity n))
    (isingFermionicGhostRate (fullVertexRightGhostMultiplicity n))
    (isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n))
    (fkIsingSquareFullVertexFixedBoundary n)
  · exact isingFermionicGhostRate_nonneg _
  · exact fullVertexGhostRate_split n
  · exact hreach
  · exact hfixed
  · exact vertexLeftColumnCap_nonneg source
  · exact vertexBottomRowRobinCap_nonneg source
  · exact hden
  · exact vertexLowerCornerCaps_edgewise n source
  · intro c hc
    exact vertexLeftColumnCap_modifiedLaplacian_nonpos n source c hc
  · intro c _hc
    exact vertexBottomRowRobinCap_modifiedLaplacian_nonpos
      n source c hn hbottom
  · exact (vertexLeftColumnCap_modifiedLaplacian_source
      n source hfixed hright).le
  · exact (vertexBottomRowRobinCap_modifiedLaplacian_source
      n source hn hbottom htop).le



theorem vertexPointPoissonBarrier_le_upperLeftProduct
    (n : Nat) (source x : FKIsingSquareFullVertexNode n)
    (hn : 0 < n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
    (hright : source.1 0 < (n : Int))
    (hbottom : -(n : Int) < source.1 1)
    (htop : source.1 1 < (n : Int)) :
    vertexPointPoissonBarrier n (some source) (some x) <=
      vertexLeftColumnCap source x * vertexTopRowRobinCap n source x /
        (vertexLeftColumnCap source source +
          vertexTopRowRobinCap n source source) := by
  letI : Nonempty (FKIsingSquareFullVertexNode n) := ⟨source⟩
  have hreach : forall c : FKIsingSquareFullVertexNode n, exists b,
      (fkIsingSquareFullVertexFixedBoundary n b ∨
        0 < isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) b) ∧
        (fkIsingSquareFullVertexGraph n).Reachable c b := by
    intro c
    obtain ⟨b, hb, hcb⟩ := fkIsingSquareFullVertex_reaches_fixed_or_ghost n c
    refine ⟨b, ?_, hcb⟩
    rcases hb with hb | hb
    · exact Or.inl hb
    · exact Or.inr ((isingFermionicGhostRate_pos_iff
        (fkIsingSquareFullVertexGhostMultiplicity n) b).2 hb)
  have hleft : -(n : Int) < source.1 0 := by
    have hb := (fkIsingSquareVertex_coordinate_bounds n source 0).1
    by_contra h
    apply hfixed
    simpa [fkIsingSquareFullVertexFixedBoundary,
      fkIsingSquareWiredArc] using
        (show source.1 0 = -(n : Int) by omega)
  have hcolIndex : 0 < fullVertexColumnIndex n source := by
    have hcoe := fullVertexColumnIndex_coe n source
    omega
  have hden : 0 < vertexLeftColumnCap source source +
      vertexTopRowRobinCap n source source := by
    have hcol : 0 < vertexLeftColumnCap source source := by
      simpa [vertexLeftColumnCap, isingNatCappedTent_self] using
        (show (0 : Real) < fullVertexColumnIndex n source by positivity)
    linarith [vertexTopRowRobinCap_nonneg n source source]
  change isingFiniteWeightedPointPoissonBarrier
      (isingFiniteGhostGraph (fkIsingSquareFullVertexGraph n)
        (isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n)))
      (isingFiniteGhostConductance (fkIsingSquareFullVertexGraph n)
        (isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n)))
      (isingFiniteGhostBoundaryWith
        (fkIsingSquareFullVertexFixedBoundary n))
      _ _ _ (some source) (some x) <= _
  apply isingFiniteGhostPointPoissonBarrier_le_splitProduct
    (fkIsingSquareFullVertexGraph n)
    (isingFermionicGhostRate
      (fkIsingSquareFullVertexGhostMultiplicity n))
    (isingFermionicGhostRate (fullVertexRightGhostMultiplicity n))
    (isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n))
    (fkIsingSquareFullVertexFixedBoundary n)
  · exact isingFermionicGhostRate_nonneg _
  · exact fullVertexGhostRate_split n
  · exact hreach
  · exact hfixed
  · exact vertexLeftColumnCap_nonneg source
  · exact vertexTopRowRobinCap_nonneg n source
  · exact hden
  · exact vertexUpperCornerCaps_edgewise n source
  · intro c hc
    exact vertexLeftColumnCap_modifiedLaplacian_nonpos n source c hc
  · intro c _hc
    exact vertexTopRowRobinCap_modifiedLaplacian_nonpos n source c hn htop
  · exact (vertexLeftColumnCap_modifiedLaplacian_source
      n source hfixed hright).le
  · exact (vertexTopRowRobinCap_modifiedLaplacian_source
      n source hn hbottom htop).le



theorem vertexMarkedEndpointLayer_coordinate_cases
    (n radius : Nat) (x : FKIsingSquareFullVertexNode n)
    (hx : vertexMarkedEndpointLayer n radius (some x)) :
    fullVertexColumnIndex n x + fullVertexRowIndex n x <= radius ∨
      fullVertexColumnIndex n x +
        (2 * n - fullVertexRowIndex n x) <= radius := by
  change Int.natAbs (x.1 0 + (n : Int)) +
        Int.natAbs (x.1 1 + (n : Int)) <= radius ∨
      Int.natAbs (x.1 0 + (n : Int)) +
        Int.natAbs (x.1 1 - (n : Int)) <= radius at hx
  have hx0nonneg : 0 <= x.1 0 + (n : Int) := by
    have hb := (fkIsingSquareVertex_coordinate_bounds n x 0).1
    omega
  have hx1nonneg : 0 <= x.1 1 + (n : Int) := by
    have hb := (fkIsingSquareVertex_coordinate_bounds n x 1).1
    omega
  have hx0abs : Int.natAbs (x.1 0 + (n : Int)) =
      fullVertexColumnIndex n x := by
    apply Int.ofNat_inj.mp
    rw [Int.natAbs_of_nonneg hx0nonneg, fullVertexColumnIndex_coe]
  have hx1abs : Int.natAbs (x.1 1 + (n : Int)) =
      fullVertexRowIndex n x := by
    apply Int.ofNat_inj.mp
    rw [Int.natAbs_of_nonneg hx1nonneg, fullVertexRowIndex_coe]
  have htopabs : Int.natAbs (x.1 1 - (n : Int)) =
      2 * n - fullVertexRowIndex n x := by
    have hrow := fullVertexRowIndex_le n x
    have hnonneg : 0 <= (n : Int) - x.1 1 := by
      have hb := (fkIsingSquareVertex_coordinate_bounds n x 1).2
      omega
    apply Int.ofNat_inj.mp
    rw [show x.1 1 - (n : Int) = -((n : Int) - x.1 1) by ring,
      Int.natAbs_neg, Int.natAbs_of_nonneg hnonneg,
      Nat.cast_sub hrow, fullVertexRowIndex_coe]
    push_cast
    ring
  rcases hx with hx | hx
  · exact Or.inl (by simpa [hx0abs, hx1abs] using hx)
  · exact Or.inr (by simpa [hx0abs, htopabs] using hx)



theorem vertexPointPoissonBarrier_le_lowerLeftRadius
    (n radius : Nat) (distance : Real)
    (source x : FKIsingSquareFullVertexNode n)
    (hn : 0 < n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
    (hright : source.1 0 < (n : Int))
    (hbottom : -(n : Int) < source.1 1)
    (htop : source.1 1 < (n : Int))
    (hcorner : fullVertexColumnIndex n x + fullVertexRowIndex n x <= radius)
    (hdistance : 0 < distance)
    (hsourceDistance : distance <=
      (fullVertexColumnIndex n source : Real) +
        (fullVertexRowIndex n source : Real) +
          1 / isingFermionicGhostCoefficient) :
    vertexPointPoissonBarrier n (some source) (some x) <=
      (radius : Real) *
        ((radius : Real) + 1 / isingFermionicGhostCoefficient) / distance := by
  have hgreen := vertexPointPoissonBarrier_le_lowerLeftProduct
    n source x hn hfixed hright hbottom htop
  have hcolCoord : (fullVertexColumnIndex n x : Real) <= radius := by
    exact_mod_cast (show fullVertexColumnIndex n x <= radius by omega)
  have hrowCoord : (fullVertexRowIndex n x : Real) <= radius := by
    exact_mod_cast (show fullVertexRowIndex n x <= radius by omega)
  have hcol : vertexLeftColumnCap source x <= (radius : Real) := by
    exact (isingNatCappedTent_le_coordinate
      (fullVertexColumnIndex n source) (fullVertexColumnIndex n x)).trans
        hcolCoord
  have hrow : vertexBottomRowRobinCap source x <=
      (radius : Real) + 1 / isingFermionicGhostCoefficient := by
    unfold vertexBottomRowRobinCap isingNatCappedRobinTent
    have htent := isingNatCappedTent_le_coordinate
      (fullVertexRowIndex n source) (fullVertexRowIndex n x)
    linarith
  have hrow0 := vertexBottomRowRobinCap_nonneg source x
  have hbound0 : 0 <= (radius : Real) *
      ((radius : Real) + 1 / isingFermionicGhostCoefficient) :=
    mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (Nat.cast_nonneg _)
        (one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le))
  have hnum : vertexLeftColumnCap source x *
      vertexBottomRowRobinCap source x <=
        (radius : Real) *
          ((radius : Real) + 1 / isingFermionicGhostCoefficient) :=
    mul_le_mul hcol hrow hrow0 (Nat.cast_nonneg _)
  have hden : distance <= vertexLeftColumnCap source source +
      vertexBottomRowRobinCap source source := by
    have heq : vertexLeftColumnCap source source +
        vertexBottomRowRobinCap source source =
          (fullVertexColumnIndex n source : Real) +
            (fullVertexRowIndex n source : Real) +
              1 / isingFermionicGhostCoefficient := by
      simp [vertexLeftColumnCap, vertexBottomRowRobinCap,
        isingNatCappedRobinTent, isingNatCappedTent_self]
      ring
    rw [heq]
    exact hsourceDistance
  exact hgreen.trans (div_le_div₀ hbound0 hnum hdistance hden)


theorem vertexPointPoissonBarrier_le_upperLeftRadius
    (n radius : Nat) (distance : Real)
    (source x : FKIsingSquareFullVertexNode n)
    (hn : 0 < n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
    (hright : source.1 0 < (n : Int))
    (hbottom : -(n : Int) < source.1 1)
    (htop : source.1 1 < (n : Int))
    (hcorner : fullVertexColumnIndex n x +
      (2 * n - fullVertexRowIndex n x) <= radius)
    (hdistance : 0 < distance)
    (hsourceDistance : distance <=
      (fullVertexColumnIndex n source : Real) +
        (2 * n - fullVertexRowIndex n source : Nat) +
          1 / isingFermionicGhostCoefficient) :
    vertexPointPoissonBarrier n (some source) (some x) <=
      (radius : Real) *
        ((radius : Real) + 1 / isingFermionicGhostCoefficient) / distance := by
  have hgreen := vertexPointPoissonBarrier_le_upperLeftProduct
    n source x hn hfixed hright hbottom htop
  have hcolCoord : (fullVertexColumnIndex n x : Real) <= radius := by
    exact_mod_cast (show fullVertexColumnIndex n x <= radius by omega)
  have hrowCoord : ((2 * n - fullVertexRowIndex n x : Nat) : Real) <=
      radius := by
    exact_mod_cast (show 2 * n - fullVertexRowIndex n x <= radius by omega)
  have hcol : vertexLeftColumnCap source x <= (radius : Real) := by
    exact (isingNatCappedTent_le_coordinate
      (fullVertexColumnIndex n source) (fullVertexColumnIndex n x)).trans
        hcolCoord
  have hrow : vertexTopRowRobinCap n source x <=
      (radius : Real) + 1 / isingFermionicGhostCoefficient := by
    unfold vertexTopRowRobinCap isingNatReverseCappedRobinTent
    have htent := isingNatReverseCappedTent_le_coordinate
      (2 * n) (fullVertexRowIndex n source) (fullVertexRowIndex n x)
    linarith
  have hrow0 := vertexTopRowRobinCap_nonneg n source x
  have hbound0 : 0 <= (radius : Real) *
      ((radius : Real) + 1 / isingFermionicGhostCoefficient) :=
    mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (Nat.cast_nonneg _)
        (one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le))
  have hnum : vertexLeftColumnCap source x *
      vertexTopRowRobinCap n source x <=
        (radius : Real) *
          ((radius : Real) + 1 / isingFermionicGhostCoefficient) :=
    mul_le_mul hcol hrow hrow0 (Nat.cast_nonneg _)
  have hden : distance <= vertexLeftColumnCap source source +
      vertexTopRowRobinCap n source source := by
    have heq : vertexLeftColumnCap source source +
        vertexTopRowRobinCap n source source =
          (fullVertexColumnIndex n source : Real) +
            (2 * n - fullVertexRowIndex n source : Nat) +
              1 / isingFermionicGhostCoefficient := by
      simp [vertexLeftColumnCap, vertexTopRowRobinCap,
        isingNatReverseCappedRobinTent, isingNatCappedTent_self,
        isingNatReverseCappedTent_self]
      ring
    rw [heq]
    exact hsourceDistance
  exact hgreen.trans (div_le_div₀ hbound0 hnum hdistance hden)


theorem vertexPointPoissonBarrier_le_markedEndpointRadius
    (n radius : Nat) (distance : Real)
    (source x : FKIsingSquareFullVertexNode n)
    (hn : 0 < n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
    (hright : source.1 0 < (n : Int))
    (hbottom : -(n : Int) < source.1 1)
    (htop : source.1 1 < (n : Int))
    (hx : vertexMarkedEndpointLayer n radius (some x))
    (hdistance : 0 < distance)
    (hlowerDistance : distance <=
      (fullVertexColumnIndex n source : Real) +
        (fullVertexRowIndex n source : Real) +
          1 / isingFermionicGhostCoefficient)
    (hupperDistance : distance <=
      (fullVertexColumnIndex n source : Real) +
        (2 * n - fullVertexRowIndex n source : Nat) +
          1 / isingFermionicGhostCoefficient) :
    vertexPointPoissonBarrier n (some source) (some x) <=
      (radius : Real) *
        ((radius : Real) + 1 / isingFermionicGhostCoefficient) / distance := by
  rcases vertexMarkedEndpointLayer_coordinate_cases n radius x hx with
    hlower | hupper
  · exact vertexPointPoissonBarrier_le_lowerLeftRadius
      n radius distance source x hn hfixed hright hbottom htop hlower
        hdistance hlowerDistance
  · exact vertexPointPoissonBarrier_le_upperLeftRadius
      n radius distance source x hn hfixed hright hbottom htop hupper
        hdistance hupperDistance



theorem vertexPointPoissonBarrier_le_exceptionalSourceRadius
    (n radius : Nat) (distance : Real)
    (source : FKIsingSquareFullVertexNode n)
    (hn : 0 < n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
    (hright : source.1 0 < (n : Int))
    (hbottom : -(n : Int) < source.1 1)
    (htop : source.1 1 < (n : Int))
    (hdistance : 0 < distance)
    (hlowerDistance : distance <=
      (fullVertexColumnIndex n source : Real) +
        (fullVertexRowIndex n source : Real) +
          1 / isingFermionicGhostCoefficient)
    (hupperDistance : distance <=
      (fullVertexColumnIndex n source : Real) +
        (2 * n - fullVertexRowIndex n source : Nat) +
          1 / isingFermionicGhostCoefficient) :
    forall z,
      z ∈ isingFiniteWeightedInteriorExceptionalSources
        (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius) ->
      vertexPointPoissonBarrier n (some source) z <=
        (radius : Real) *
          ((radius : Real) + 1 / isingFermionicGhostCoefficient) /
            distance := by
  intro z hz
  have hmarked : vertexMarkedEndpointLayer n radius z := by
    have hz' : Not (vertexDirichletBoundary n z) ∧
        vertexMarkedEndpointLayer n radius z := by
      simpa [isingFiniteWeightedInteriorExceptionalSources] using hz
    exact hz'.2
  cases z with
  | none => exact False.elim hmarked
  | some x =>
      exact vertexPointPoissonBarrier_le_markedEndpointRadius
        n radius distance source x hn hfixed hright hbottom htop hmarked
          hdistance hlowerDistance hupperDistance

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
