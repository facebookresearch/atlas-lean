/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.TriHexFKFiniteWiredSweep
import Code.FK.TriHexFKTorusSweep

open Finset Set

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice
open Universality

noncomputable section



def triHexPlanarTriangleEdgeBaseShift (i : Fin 3) : Site 2 :=
  ![![0, 1], ![1, 0], ![1, 0]] i



def triHexPlanarTriangleIndexEquiv :
    (Site 2 × Fin 3) ≃ (Site 2 × Fin 3) where
  toFun a := (a.1 + triHexPlanarTriangleEdgeBaseShift a.2, a.2)
  invFun a := (a.1 - triHexPlanarTriangleEdgeBaseShift a.2, a.2)
  left_inv := by
    rintro ⟨z, i⟩
    ext <;> simp
  right_inv := by
    rintro ⟨z, i⟩
    ext <;> simp


def triHexPlanarFiniteTriangleEdge (n : Nat)
    (a : TriHexPlanarFiniteCell n × Fin 3) :
    Sym2 (TriHexPlanarFiniteTerminal n) :=
  s(triHexPlanarFiniteTerminalMap n a.1 (triHexTriangleEdgeTerminal1 a.2),
    triHexPlanarFiniteTerminalMap n a.1 (triHexTriangleEdgeTerminal2 a.2))



theorem triHexPlanarFiniteTriangleEdge_val (n : Nat)
    (a : TriHexPlanarFiniteCell n × Fin 3) :
    Sym2.map (fun v : TriHexPlanarFiniteTerminal n => v.1)
        (triHexPlanarFiniteTriangleEdge n a) =
      triangularIndexedEdge
        (triHexPlanarTriangleIndexEquiv (a.1.1, a.2)) := by
  rcases a with ⟨z, i⟩
  rw [triHexPlanarFiniteTriangleEdge, Sym2.map_mk]
  fin_cases i
  · apply Sym2.eq_iff.mpr
    left
    constructor <;> ext k <;> fin_cases k <;>
      simp [triHexPlanarFiniteTerminalMap, triHexPlanarCellTerminal,
        triHexTriangleEdgeTerminal1, triHexTriangleEdgeTerminal2,
        triHexPlanarTriangleIndexEquiv, triHexPlanarTriangleEdgeBaseShift,
        triangularIndexedEdge, triangularStep, hexagonalStep]
  · apply Sym2.eq_iff.mpr
    right
    constructor <;> ext k <;> fin_cases k <;>
      simp [triHexPlanarFiniteTerminalMap, triHexPlanarCellTerminal,
        triHexTriangleEdgeTerminal1, triHexTriangleEdgeTerminal2,
        triHexPlanarTriangleIndexEquiv, triHexPlanarTriangleEdgeBaseShift,
        triangularIndexedEdge, triangularStep, hexagonalStep]
  · apply Sym2.eq_iff.mpr
    left
    constructor <;> ext k <;> fin_cases k <;>
      simp [triHexPlanarFiniteTerminalMap, triHexPlanarCellTerminal,
        triHexTriangleEdgeTerminal1, triHexTriangleEdgeTerminal2,
        triHexPlanarTriangleIndexEquiv, triHexPlanarTriangleEdgeBaseShift,
        triangularIndexedEdge, triangularStep, hexagonalStep]


theorem triHexPlanarFiniteTriangleEdge_injective (n : Nat) :
    Function.Injective (triHexPlanarFiniteTriangleEdge n) := by
  rintro ⟨a, i⟩ ⟨b, j⟩ hab
  have hval := congrArg
    (Sym2.map (fun v : TriHexPlanarFiniteTerminal n => v.1)) hab
  rw [triHexPlanarFiniteTriangleEdge_val,
    triHexPlanarFiniteTriangleEdge_val] at hval
  have hchart : triangularEdgeChart
      (triHexPlanarTriangleIndexEquiv (a.1, i)) =
      triangularEdgeChart
        (triHexPlanarTriangleIndexEquiv (b.1, j)) :=
    Subtype.ext hval
  have hindex := triHexPlanarTriangleIndexEquiv.injective
    (triangularEdgeChart_injective hchart)
  have hz : a.1 = b.1 :=
    congrArg (fun x : Site 2 × Fin 3 => x.1) hindex
  have hi : i = j :=
    congrArg (fun x : Site 2 × Fin 3 => x.2) hindex
  exact Prod.ext (Subtype.ext hz) hi



def triHexPlanarFiniteTriangleGraph (n : Nat) :
    SimpleGraph (TriHexPlanarFiniteTerminal n) :=
  SimpleGraph.fromEdgeSet (Set.range (triHexPlanarFiniteTriangleEdge n))

noncomputable instance triHexPlanarFiniteTriangleGraphDecidable (n : Nat) :
    DecidableRel (triHexPlanarFiniteTriangleGraph n).Adj :=
  Classical.decRel _

theorem triHexPlanarFiniteTriangleEdge_ne (n : Nat)
    (a : TriHexPlanarFiniteCell n × Fin 3) :
    (triHexPlanarFiniteTerminalMap n a.1
        (triHexTriangleEdgeTerminal1 a.2)) ≠
      triHexPlanarFiniteTerminalMap n a.1
        (triHexTriangleEdgeTerminal2 a.2) := by
  intro h
  have hval := congrArg Subtype.val h
  rcases a with ⟨z, i⟩
  fin_cases i <;>
    simp [triHexPlanarFiniteTerminalMap, triHexPlanarCellTerminal,
      triHexTriangleEdgeTerminal1, triHexTriangleEdgeTerminal2,
      hexagonalStep, funext_iff] at hval


theorem triHexPlanarFiniteTriangleEdge_mem (n : Nat)
    (a : TriHexPlanarFiniteCell n × Fin 3) :
    triHexPlanarFiniteTriangleEdge n a ∈
      (triHexPlanarFiniteTriangleGraph n).edgeSet := by
  rw [triHexPlanarFiniteTriangleGraph, SimpleGraph.edgeSet_fromEdgeSet]
  refine ⟨⟨a, rfl⟩, ?_⟩
  rw [Sym2.mem_diagSet]
  exact triHexPlanarFiniteTriangleEdge_ne n a



noncomputable def triHexPlanarFiniteTriangleEdgeChart (n : Nat)
    (a : TriHexPlanarFiniteCell n × Fin 3) :
    (triHexPlanarFiniteTriangleGraph n).edgeSet :=
  ⟨triHexPlanarFiniteTriangleEdge n a,
    triHexPlanarFiniteTriangleEdge_mem n a⟩

theorem triHexPlanarFiniteTriangleEdgeChart_bijective (n : Nat) :
    Function.Bijective (triHexPlanarFiniteTriangleEdgeChart n) := by
  constructor
  · intro a b h
    apply triHexPlanarFiniteTriangleEdge_injective n
    exact congrArg Subtype.val h
  · rintro ⟨e, he⟩
    rw [triHexPlanarFiniteTriangleGraph,
      SimpleGraph.edgeSet_fromEdgeSet] at he
    obtain ⟨⟨a, rfl⟩, _⟩ := he
    exact ⟨a, rfl⟩

noncomputable def triHexPlanarFiniteTriangleEdgeEquiv (n : Nat) :
    (TriHexPlanarFiniteCell n × Fin 3) ≃
      (triHexPlanarFiniteTriangleGraph n).edgeSet :=
  Equiv.ofBijective (triHexPlanarFiniteTriangleEdgeChart n)
    (triHexPlanarFiniteTriangleEdgeChart_bijective n)





abbrev TriHexPlanarFiniteStarVertex (n : Nat) :=
  TriHexPlanarFiniteCell n ⊕ TriHexPlanarFiniteTerminal n


def triHexPlanarFiniteStarEdge (n : Nat)
    (a : TriHexPlanarFiniteCell n × Fin 3) :
    Sym2 (TriHexPlanarFiniteStarVertex n) :=
  s(Sum.inl a.1, Sum.inr (triHexPlanarFiniteTerminalMap n a.1 a.2))

theorem triHexPlanarFiniteStarEdge_injective (n : Nat) :
    Function.Injective (triHexPlanarFiniteStarEdge n) := by
  rintro ⟨z, i⟩ ⟨w, j⟩ h
  change s(Sum.inl z,
      Sum.inr (triHexPlanarFiniteTerminalMap n z i)) =
    s(Sum.inl w,
      Sum.inr (triHexPlanarFiniteTerminalMap n w j)) at h
  rw [Sym2.eq_iff] at h
  rcases h with hdir | hswap
  · have hzw : z = w := Sum.inl.inj hdir.1
    subst w
    have ht : triHexPlanarFiniteTerminalMap n z i =
        triHexPlanarFiniteTerminalMap n z j := Sum.inr.inj hdir.2
    have hsite := congrArg Subtype.val ht
    have hstep : hexagonalStep i = hexagonalStep j := by
      exact add_left_cancel hsite
    exact Prod.ext rfl (hexagonalStep_injective hstep)
  · exact (Sum.inl_ne_inr hswap.1).elim



def triHexPlanarFiniteStarGraph (n : Nat) :
    SimpleGraph (TriHexPlanarFiniteStarVertex n) :=
  SimpleGraph.fromEdgeSet (Set.range (triHexPlanarFiniteStarEdge n))

noncomputable instance triHexPlanarFiniteStarGraphDecidable (n : Nat) :
    DecidableRel (triHexPlanarFiniteStarGraph n).Adj :=
  Classical.decRel _

theorem triHexPlanarFiniteStarEdge_mem (n : Nat)
    (a : TriHexPlanarFiniteCell n × Fin 3) :
    triHexPlanarFiniteStarEdge n a ∈
      (triHexPlanarFiniteStarGraph n).edgeSet := by
  rw [triHexPlanarFiniteStarGraph, SimpleGraph.edgeSet_fromEdgeSet]
  refine ⟨⟨a, rfl⟩, ?_⟩
  rw [Sym2.mem_diagSet]
  change ¬s(Sum.inl a.1,
    Sum.inr (triHexPlanarFiniteTerminalMap n a.1 a.2)).IsDiag
  rw [Sym2.mk_isDiag_iff]
  exact Sum.inl_ne_inr

noncomputable def triHexPlanarFiniteStarEdgeChart (n : Nat)
    (a : TriHexPlanarFiniteCell n × Fin 3) :
    (triHexPlanarFiniteStarGraph n).edgeSet :=
  ⟨triHexPlanarFiniteStarEdge n a, triHexPlanarFiniteStarEdge_mem n a⟩

theorem triHexPlanarFiniteStarEdgeChart_bijective (n : Nat) :
    Function.Bijective (triHexPlanarFiniteStarEdgeChart n) := by
  constructor
  · intro a b h
    apply triHexPlanarFiniteStarEdge_injective n
    exact congrArg Subtype.val h
  · rintro ⟨e, he⟩
    rw [triHexPlanarFiniteStarGraph,
      SimpleGraph.edgeSet_fromEdgeSet] at he
    obtain ⟨⟨a, rfl⟩, _⟩ := he
    exact ⟨a, rfl⟩

noncomputable def triHexPlanarFiniteStarEdgeEquiv (n : Nat) :
    (TriHexPlanarFiniteCell n × Fin 3) ≃
      (triHexPlanarFiniteStarGraph n).edgeSet :=
  Equiv.ofBijective (triHexPlanarFiniteStarEdgeChart n)
    (triHexPlanarFiniteStarEdgeChart_bijective n)



def triHexFiniteCellConfigEquiv (I : Type*) :
    ConfigSpace (I × Fin 3) ≃ (I → LocalConfig) where
  toFun omega z := (omega (z, 0), omega (z, 1), omega (z, 2))
  invFun config a := ![config a.1 |>.1, config a.1 |>.2.1,
    config a.1 |>.2.2] a.2
  left_inv omega := by
    funext a
    rcases a with ⟨z, i⟩
    fin_cases i <;> rfl
  right_inv config := by
    funext z
    rfl



noncomputable def triHexPlanarFiniteTriangleConfigEquiv (n : Nat) :
    ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet ≃
      (TriHexPlanarFiniteCell n → LocalConfig) :=
  (configReindexEquiv (triHexPlanarFiniteTriangleEdgeEquiv n)).trans
    (triHexFiniteCellConfigEquiv _)


noncomputable def triHexPlanarFiniteStarConfigEquiv (n : Nat) :
    ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet ≃
      (TriHexPlanarFiniteCell n → LocalConfig) :=
  (configReindexEquiv (triHexPlanarFiniteStarEdgeEquiv n)).trans
    (triHexFiniteCellConfigEquiv _)

@[simp] theorem triHexPlanarFiniteTriangleConfigEquiv_direction
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet)
    (z : TriHexPlanarFiniteCell n) (i : Fin 3) :
    triHexLocalDirection (triHexPlanarFiniteTriangleConfigEquiv n omega z) i =
      omega (triHexPlanarFiniteTriangleEdgeEquiv n (z, i)) := by
  fin_cases i <;> rfl

@[simp] theorem triHexPlanarFiniteStarConfigEquiv_direction
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    (z : TriHexPlanarFiniteCell n) (i : Fin 3) :
    triHexLocalDirection (triHexPlanarFiniteStarConfigEquiv n omega z) i =
      omega (triHexPlanarFiniteStarEdgeEquiv n (z, i)) := by
  fin_cases i <;> rfl





theorem triHexPlanarFiniteTriangle_openSub_adj_cellEdge
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet)
    (z : TriHexPlanarFiniteCell n) (i : Fin 3)
    (hopen : triHexLocalDirection
      (triHexPlanarFiniteTriangleConfigEquiv n omega z) i = true) :
    (openSub (triHexPlanarFiniteTriangleGraph n)
      (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Adj
        (triHexPlanarFiniteTerminalMap n z (triHexTriangleEdgeTerminal1 i))
        (triHexPlanarFiniteTerminalMap n z
          (triHexTriangleEdgeTerminal2 i)) := by
  rw [openSub_adj]
  constructor
  · rw [← SimpleGraph.mem_edgeSet]
    exact (triHexPlanarFiniteTriangleEdgeEquiv n (z, i)).2
  · change (extendActive (triHexPlanarFiniteTriangleGraph n) omega)
      (triHexPlanarFiniteTriangleEdge n (z, i)) = true
    rw [show triHexPlanarFiniteTriangleEdge n (z, i) =
        (triHexPlanarFiniteTriangleEdgeEquiv n (z, i)).1 from rfl,
      extendActive_apply]
    exact (triHexPlanarFiniteTriangleConfigEquiv_direction n omega z i).symm.trans
      hopen



theorem triHexPlanarFiniteTriangle_openSub_reachable_of_connects
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet)
    (z : TriHexPlanarFiniteCell n) (i j : Fin 3)
    (hconnects : (triangleFKLocalConnectivity
      (triHexPlanarFiniteTriangleConfigEquiv n omega z)).Connects i j) :
    (openSub (triHexPlanarFiniteTriangleGraph n)
      (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Reachable
        (triHexPlanarFiniteTerminalMap n z i)
        (triHexPlanarFiniteTerminalMap n z j) := by
  let config := triHexPlanarFiniteTriangleConfigEquiv n omega z
  let edgeReach (k : Fin 3)
      (h : triHexLocalDirection config k = true) :=
    SimpleGraph.Adj.reachable
      (triHexPlanarFiniteTriangle_openSub_adj_cellEdge n omega z k h)
  have reach01 (h : (triangleFKLocalConnectivity config).Connects 0 1) :
      (openSub (triHexPlanarFiniteTriangleGraph n)
        (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Reachable
          (triHexPlanarFiniteTerminalMap n z 0)
          (triHexPlanarFiniteTerminalMap n z 1) := by
    rcases (triangleFKLocalConnectivity_connects_zero_one config).mp h with
      h2 | ⟨h0, h1⟩
    · exact edgeReach 2 h2
    · exact (edgeReach 1 h1).symm.trans (edgeReach 0 h0).symm
  have reach02 (h : (triangleFKLocalConnectivity config).Connects 0 2) :
      (openSub (triHexPlanarFiniteTriangleGraph n)
        (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Reachable
          (triHexPlanarFiniteTerminalMap n z 0)
          (triHexPlanarFiniteTerminalMap n z 2) := by
    rcases (triangleFKLocalConnectivity_connects_zero_two config).mp h with
      h1 | ⟨h0, h2⟩
    · exact (edgeReach 1 h1).symm
    · exact (edgeReach 2 h2).trans (edgeReach 0 h0)
  have reach12 (h : (triangleFKLocalConnectivity config).Connects 1 2) :
      (openSub (triHexPlanarFiniteTriangleGraph n)
        (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Reachable
          (triHexPlanarFiniteTerminalMap n z 1)
          (triHexPlanarFiniteTerminalMap n z 2) := by
    rcases (triangleFKLocalConnectivity_connects_one_two config).mp h with
      h0 | ⟨h1, h2⟩
    · exact edgeReach 0 h0
    · exact (edgeReach 2 h2).symm.trans (edgeReach 1 h1).symm
  fin_cases i <;> fin_cases j
  · exact SimpleGraph.Reachable.refl _
  · exact reach01 hconnects
  · exact reach02 hconnects
  · exact (reach01
      ((triangleFKLocalConnectivity config).connects_symm 0 1 |>.mpr
        hconnects)).symm
  · exact SimpleGraph.Reachable.refl _
  · exact reach12 hconnects
  · exact (reach02
      ((triangleFKLocalConnectivity config).connects_symm 0 2 |>.mpr
        hconnects)).symm
  · exact (reach12
      ((triangleFKLocalConnectivity config).connects_symm 1 2 |>.mpr
        hconnects)).symm
  · exact SimpleGraph.Reachable.refl _



def triHexPlanarFiniteTriangleSectorGraph (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet) :
    SimpleGraph (TriHexPlanarFiniteTerminal n) :=
  triHexFKTerminalSectorGraph (triHexPlanarFiniteTerminalMap n)
    (fun z => triangleFKLocalConnectivity
      (triHexPlanarFiniteTriangleConfigEquiv n omega z))


theorem triHexPlanarFiniteTriangle_openSub_adj_sector
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet)
    {x y : TriHexPlanarFiniteTerminal n}
    (hxy : (openSub (triHexPlanarFiniteTriangleGraph n)
      (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Adj x y) :
    (triHexPlanarFiniteTriangleSectorGraph n omega).Adj x y := by
  have hmem : s(x, y) ∈ (triHexPlanarFiniteTriangleGraph n).edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    exact hxy.1
  let e : (triHexPlanarFiniteTriangleGraph n).edgeSet := ⟨s(x, y), hmem⟩
  let a := (triHexPlanarFiniteTriangleEdgeEquiv n).symm e
  let z := a.1
  let i := a.2
  have ha : triHexPlanarFiniteTriangleEdgeEquiv n (z, i) = e := by
    simpa [z, i, a] using
      (triHexPlanarFiniteTriangleEdgeEquiv n).apply_symm_apply e
  have hedge : s(x, y) =
      s(triHexPlanarFiniteTerminalMap n z (triHexTriangleEdgeTerminal1 i),
        triHexPlanarFiniteTerminalMap n z
          (triHexTriangleEdgeTerminal2 i)) := by
    calc
      s(x, y) = e.1 := rfl
      _ = (triHexPlanarFiniteTriangleEdgeEquiv n (z, i)).1 :=
        congrArg Subtype.val ha.symm
      _ = _ := rfl
  have hopen : omega e = true := by
    have := hxy.2
    simpa [extendActive, e, hmem] using this
  have hlocal : triHexLocalDirection
      (triHexPlanarFiniteTriangleConfigEquiv n omega z) i = true := by
    rw [triHexPlanarFiniteTriangleConfigEquiv_direction]
    rw [ha]
    exact hopen
  have hconnects := triangleFKLocalConnectivity_connects_of_direction
    (triHexPlanarFiniteTriangleConfigEquiv n omega z) i hlocal
  rw [triHexPlanarFiniteTriangleSectorGraph, triHexFKTerminalSectorGraph,
    SimpleGraph.fromEdgeSet_adj]
  exact ⟨⟨z, triHexTriangleEdgeTerminal1 i,
    triHexTriangleEdgeTerminal2 i, hconnects, hedge⟩, hxy.ne⟩


theorem triHexPlanarFiniteTriangle_sector_adj_openSub_reachable
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet)
    {x y : TriHexPlanarFiniteTerminal n}
    (hxy : (triHexPlanarFiniteTriangleSectorGraph n omega).Adj x y) :
    (openSub (triHexPlanarFiniteTriangleGraph n)
      (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Reachable x y := by
  rw [triHexPlanarFiniteTriangleSectorGraph, triHexFKTerminalSectorGraph,
    SimpleGraph.fromEdgeSet_adj] at hxy
  obtain ⟨⟨z, i, j, hconnects, hedge⟩, _⟩ := hxy
  have hreach := triHexPlanarFiniteTriangle_openSub_reachable_of_connects
    n omega z i j hconnects
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨hxi, hyj⟩ | ⟨hxj, hyi⟩
  · simpa [hxi, hyj] using hreach
  · simpa [hxj, hyi] using hreach.symm



theorem triHexPlanarFiniteTriangle_openSub_reachable_iff_sector
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet)
    (x y : TriHexPlanarFiniteTerminal n) :
    (openSub (triHexPlanarFiniteTriangleGraph n)
      (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Reachable x y ↔
      (triHexPlanarFiniteTriangleSectorGraph n omega).Reachable x y := by
  constructor
  · exact fun h => reachable_map_of_adj_reachable _ _ id
      (fun _ _ hab => SimpleGraph.Adj.reachable
        (triHexPlanarFiniteTriangle_openSub_adj_sector n omega hab)) h
  · exact fun h => reachable_map_of_adj_reachable _ _ id
      (fun _ _ hab =>
        triHexPlanarFiniteTriangle_sector_adj_openSub_reachable n omega hab) h



def triHexPlanarFiniteTriangleWiredSectorGraph (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet) :
    SimpleGraph (TriHexPlanarFiniteTerminal n) :=
  triHexFKTerminalWiredGraph (triHexPlanarFiniteTerminalMap n)
    (triHexPlanarFiniteBoundary n)
    (fun z => triangleFKLocalConnectivity
      (triHexPlanarFiniteTriangleConfigEquiv n omega z))



theorem triHexPlanarFiniteTriangle_wired_reachable_iff_sector
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet)
    (x y : TriHexPlanarFiniteTerminal n) :
    (wiredGraph (triHexPlanarFiniteTriangleGraph n)
      (triHexPlanarFiniteBoundary n)
      (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Reachable x y ↔
      (triHexPlanarFiniteTriangleWiredSectorGraph n omega).Reachable x y := by
  let Gopen := openSub (triHexPlanarFiniteTriangleGraph n)
    (extendActive (triHexPlanarFiniteTriangleGraph n) omega)
  let Gsector := triHexPlanarFiniteTriangleSectorGraph n omega
  let K := boundaryCliqueGraph (triHexPlanarFiniteBoundary n)
  have hopen : openGraph (triHexPlanarFiniteTriangleGraph n)
      (extendActive (triHexPlanarFiniteTriangleGraph n) omega) = Gopen := rfl
  have hsector : triHexPlanarFiniteTriangleWiredSectorGraph n omega =
      Gsector ⊔ K := rfl
  rw [wiredGraph, hopen, hsector]
  constructor
  · intro h
    exact reachable_map_of_adj_reachable (Gopen ⊔ K) (Gsector ⊔ K) id
      (fun _ _ hab => by
        rw [SimpleGraph.sup_adj] at hab
        rcases hab with hopenEdge | hboundary
        · exact (triHexPlanarFiniteTriangle_openSub_reachable_iff_sector
            n omega _ _).mp hopenEdge.reachable |>.mono le_sup_left
        · exact hboundary.reachable.mono le_sup_right) h
  · intro h
    exact reachable_map_of_adj_reachable (Gsector ⊔ K) (Gopen ⊔ K) id
      (fun _ _ hab => by
        rw [SimpleGraph.sup_adj] at hab
        rcases hab with hsectorEdge | hboundary
        · exact (triHexPlanarFiniteTriangle_openSub_reachable_iff_sector
            n omega _ _).mpr hsectorEdge.reachable |>.mono le_sup_left
        · exact hboundary.reachable.mono le_sup_right) h



theorem triHexPlanarFiniteTriangle_numClustersWired_eq_sector
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet) :
    numClustersWired (triHexPlanarFiniteTriangleGraph n)
        (triHexPlanarFiniteBoundary n)
        (extendActive (triHexPlanarFiniteTriangleGraph n) omega) =
      Nat.card
        (triHexPlanarFiniteTriangleWiredSectorGraph n omega).ConnectedComponent := by
  unfold numClustersWired
  exact Nat.card_congr
    (connectedComponentEquivOfReachableIff _ _
      (triHexPlanarFiniteTriangle_wired_reachable_iff_sector n omega))




def triHexPlanarFiniteStarBoundary (n : Nat) :
    TriHexPlanarFiniteStarVertex n → Prop
  | Sum.inl _ => False
  | Sum.inr v => triHexPlanarFiniteBoundary n v

noncomputable instance triHexPlanarFiniteStarBoundaryDecidable (n : Nat) :
    DecidablePred (triHexPlanarFiniteStarBoundary n) :=
  Classical.decPred _


theorem triHexPlanarFiniteStar_openSub_adj_spoke
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    (z : TriHexPlanarFiniteCell n) (i : Fin 3)
    (hopen : triHexLocalDirection
      (triHexPlanarFiniteStarConfigEquiv n omega z) i = true) :
    (openSub (triHexPlanarFiniteStarGraph n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).Adj
        (Sum.inl z)
        (Sum.inr (triHexPlanarFiniteTerminalMap n z i)) := by
  rw [openSub_adj]
  constructor
  · rw [← SimpleGraph.mem_edgeSet]
    exact (triHexPlanarFiniteStarEdgeEquiv n (z, i)).2
  · change (extendActive (triHexPlanarFiniteStarGraph n) omega)
      (triHexPlanarFiniteStarEdge n (z, i)) = true
    rw [show triHexPlanarFiniteStarEdge n (z, i) =
        (triHexPlanarFiniteStarEdgeEquiv n (z, i)).1 from rfl,
      extendActive_apply]
    exact (triHexPlanarFiniteStarConfigEquiv_direction n omega z i).symm.trans
      hopen



theorem triHexPlanarFiniteStar_openSub_reachable_of_connects
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    (z : TriHexPlanarFiniteCell n) (i j : Fin 3)
    (hconnects : (starFKLocalConnectivity
      (triHexPlanarFiniteStarConfigEquiv n omega z)).Connects i j) :
    (openSub (triHexPlanarFiniteStarGraph n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).Reachable
        (Sum.inr (triHexPlanarFiniteTerminalMap n z i))
        (Sum.inr (triHexPlanarFiniteTerminalMap n z j)) := by
  rcases (starFKLocalConnectivity_connects_iff
    (triHexPlanarFiniteStarConfigEquiv n omega z) i j).mp hconnects with
    rfl | ⟨hi, hj⟩
  · exact SimpleGraph.Reachable.refl _
  · exact (SimpleGraph.Adj.reachable
      (triHexPlanarFiniteStar_openSub_adj_spoke n omega z i hi)).symm.trans
        (SimpleGraph.Adj.reachable
          (triHexPlanarFiniteStar_openSub_adj_spoke n omega z j hj))


def triHexPlanarFiniteStarSectorGraph (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    SimpleGraph (TriHexPlanarFiniteTerminal n) :=
  triHexFKTerminalSectorGraph (triHexPlanarFiniteTerminalMap n)
    (fun z => starFKLocalConnectivity
      (triHexPlanarFiniteStarConfigEquiv n omega z))



def triHexPlanarFiniteStarRepresentative (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    TriHexPlanarFiniteStarVertex n → TriHexPlanarFiniteTerminal n
  | Sum.inr v => v
  | Sum.inl z => triHexPlanarFiniteTerminalMap n z
      (starFKRepresentativeDirection
        (triHexPlanarFiniteStarConfigEquiv n omega z))



theorem triHexPlanarFiniteStar_openSub_adj_representative_reachable
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    {u v : TriHexPlanarFiniteStarVertex n}
    (huv : (openSub (triHexPlanarFiniteStarGraph n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).Adj u v) :
    (triHexPlanarFiniteStarSectorGraph n omega).Reachable
      (triHexPlanarFiniteStarRepresentative n omega u)
      (triHexPlanarFiniteStarRepresentative n omega v) := by
  have hmem : s(u, v) ∈ (triHexPlanarFiniteStarGraph n).edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    exact huv.1
  let e : (triHexPlanarFiniteStarGraph n).edgeSet := ⟨s(u, v), hmem⟩
  let a := (triHexPlanarFiniteStarEdgeEquiv n).symm e
  let z := a.1
  let i := a.2
  have ha : triHexPlanarFiniteStarEdgeEquiv n (z, i) = e := by
    simpa [z, i, a] using
      (triHexPlanarFiniteStarEdgeEquiv n).apply_symm_apply e
  have hedge : s(Sum.inl z,
      Sum.inr (triHexPlanarFiniteTerminalMap n z i)) = s(u, v) := by
    calc
      _ = (triHexPlanarFiniteStarEdgeEquiv n (z, i)).1 := rfl
      _ = e.1 := congrArg Subtype.val ha
      _ = _ := rfl
  have hopen : triHexLocalDirection
      (triHexPlanarFiniteStarConfigEquiv n omega z) i = true := by
    rw [triHexPlanarFiniteStarConfigEquiv_direction]
    rw [ha]
    have := huv.2
    rw [← hedge] at this
    change (extendActive (triHexPlanarFiniteStarGraph n) omega)
      ((triHexPlanarFiniteStarEdgeEquiv n (z, i)).1) = true at this
    rw [extendActive_apply, ha] at this
    exact this
  have hselected := starFKRepresentativeDirection_open_of_open
    (triHexPlanarFiniteStarConfigEquiv n omega z) i hopen
  have hconnects : (starFKLocalConnectivity
      (triHexPlanarFiniteStarConfigEquiv n omega z)).Connects
        (starFKRepresentativeDirection
          (triHexPlanarFiniteStarConfigEquiv n omega z)) i :=
    (starFKLocalConnectivity_connects_iff _ _ _).2
      (Or.inr ⟨hselected, hopen⟩)
  have hreach := triHexFKTerminalSectorGraph_reachable_of_connects
    (triHexPlanarFiniteTerminalMap n)
    (fun z => starFKLocalConnectivity
      (triHexPlanarFiniteStarConfigEquiv n omega z)) z _ _ hconnects
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · rw [← hu, ← hv]
    simpa [triHexPlanarFiniteStarRepresentative,
      triHexPlanarFiniteStarSectorGraph] using hreach
  · rw [← hu, ← hv]
    simpa [triHexPlanarFiniteStarRepresentative,
      triHexPlanarFiniteStarSectorGraph] using hreach.symm


theorem triHexPlanarFiniteStar_sector_adj_openSub_reachable
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    {x y : TriHexPlanarFiniteTerminal n}
    (hxy : (triHexPlanarFiniteStarSectorGraph n omega).Adj x y) :
    (openSub (triHexPlanarFiniteStarGraph n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).Reachable
        (Sum.inr x) (Sum.inr y) := by
  rw [triHexPlanarFiniteStarSectorGraph, triHexFKTerminalSectorGraph,
    SimpleGraph.fromEdgeSet_adj] at hxy
  obtain ⟨⟨z, i, j, hconnects, hedge⟩, _⟩ := hxy
  have hreach := triHexPlanarFiniteStar_openSub_reachable_of_connects
    n omega z i j hconnects
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨hxi, hyj⟩ | ⟨hxj, hyi⟩
  · simpa [hxi, hyj] using hreach
  · simpa [hxj, hyi] using hreach.symm



theorem triHexPlanarFiniteStar_openSub_white_reachable_iff_sector
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    (x y : TriHexPlanarFiniteTerminal n) :
    (openSub (triHexPlanarFiniteStarGraph n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).Reachable
        (Sum.inr x) (Sum.inr y) ↔
      (triHexPlanarFiniteStarSectorGraph n omega).Reachable x y := by
  constructor
  · intro h
    have hc := reachable_map_of_adj_reachable _ _
      (triHexPlanarFiniteStarRepresentative n omega)
      (fun _ _ hab =>
        triHexPlanarFiniteStar_openSub_adj_representative_reachable n omega hab) h
    simpa [triHexPlanarFiniteStarRepresentative] using hc
  · intro h
    exact reachable_map_of_adj_reachable _ _ Sum.inr
      (fun _ _ hab =>
        triHexPlanarFiniteStar_sector_adj_openSub_reachable n omega hab) h


def triHexPlanarFiniteStarWiredSectorGraph (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    SimpleGraph (TriHexPlanarFiniteTerminal n) :=
  triHexFKTerminalWiredGraph (triHexPlanarFiniteTerminalMap n)
    (triHexPlanarFiniteBoundary n)
    (fun z => starFKLocalConnectivity
      (triHexPlanarFiniteStarConfigEquiv n omega z))



theorem triHexPlanarFiniteStar_wired_white_reachable_iff_sector
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    (x y : TriHexPlanarFiniteTerminal n) :
    (wiredGraph (triHexPlanarFiniteStarGraph n)
      (triHexPlanarFiniteStarBoundary n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).Reachable
        (Sum.inr x) (Sum.inr y) ↔
      (triHexPlanarFiniteStarWiredSectorGraph n omega).Reachable x y := by
  let Gopen := openSub (triHexPlanarFiniteStarGraph n)
    (extendActive (triHexPlanarFiniteStarGraph n) omega)
  let Gsector := triHexPlanarFiniteStarSectorGraph n omega
  let Kstar := boundaryCliqueGraph (triHexPlanarFiniteStarBoundary n)
  let Kterminal := boundaryCliqueGraph (triHexPlanarFiniteBoundary n)
  have hopen : openGraph (triHexPlanarFiniteStarGraph n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega) = Gopen := rfl
  have hsector : triHexPlanarFiniteStarWiredSectorGraph n omega =
      Gsector ⊔ Kterminal := rfl
  rw [wiredGraph, hopen, hsector]
  constructor
  · intro h
    have hc := reachable_map_of_adj_reachable (Gopen ⊔ Kstar)
      (Gsector ⊔ Kterminal)
      (triHexPlanarFiniteStarRepresentative n omega) (fun u v huv => by
        rw [SimpleGraph.sup_adj] at huv
        rcases huv with hopenEdge | hboundary
        · exact (triHexPlanarFiniteStar_openSub_adj_representative_reachable
            n omega hopenEdge).mono le_sup_left
        · rw [boundaryCliqueGraph_adj] at hboundary
          rcases u with u | u <;> rcases v with v | v
          · exact (hboundary.2.1.elim)
          · exact (hboundary.2.1.elim)
          · exact (hboundary.2.2.elim)
          · change (Gsector ⊔ Kterminal).Reachable u v
            have hb : Kterminal.Adj u v := by
              change (boundaryCliqueGraph
                (triHexPlanarFiniteBoundary n)).Adj u v
              rw [boundaryCliqueGraph_adj]
              exact ⟨fun huv => hboundary.1 (congrArg Sum.inr huv),
                hboundary.2.1, hboundary.2.2⟩
            have hb' : (Gsector ⊔ Kterminal).Adj u v :=
              (show Kterminal ≤ Gsector ⊔ Kterminal from le_sup_right) hb
            exact hb'.reachable) h
    simpa [triHexPlanarFiniteStarRepresentative] using hc
  · intro h
    exact reachable_map_of_adj_reachable (Gsector ⊔ Kterminal)
      (Gopen ⊔ Kstar) Sum.inr (fun u v huv => by
        rw [SimpleGraph.sup_adj] at huv
        rcases huv with hsectorEdge | hboundary
        · exact (triHexPlanarFiniteStar_openSub_white_reachable_iff_sector
            n omega u v).mpr hsectorEdge.reachable |>.mono le_sup_left
        · change (Gopen ⊔ Kstar).Reachable (Sum.inr u) (Sum.inr v)
          have hb : Kstar.Adj (Sum.inr u) (Sum.inr v) := by
            change (boundaryCliqueGraph
              (triHexPlanarFiniteStarBoundary n)).Adj (Sum.inr u) (Sum.inr v)
            rw [boundaryCliqueGraph_adj]
            change (boundaryCliqueGraph
              (triHexPlanarFiniteBoundary n)).Adj u v at hboundary
            rw [boundaryCliqueGraph_adj] at hboundary
            exact ⟨fun huv => hboundary.1 (Sum.inr.inj huv),
              hboundary.2.1, hboundary.2.2⟩
          have hb' : (Gopen ⊔ Kstar).Adj (Sum.inr u) (Sum.inr v) :=
            (show Kstar ≤ Gopen ⊔ Kstar from le_sup_right) hb
          exact hb'.reachable) h


theorem triHexPlanarFiniteStar_openSub_adj_eq_spoke
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    {u v : TriHexPlanarFiniteStarVertex n}
    (huv : (openSub (triHexPlanarFiniteStarGraph n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).Adj u v) :
    ∃ z i, triHexLocalDirection
        (triHexPlanarFiniteStarConfigEquiv n omega z) i = true ∧
      ((u = Sum.inl z ∧
          v = Sum.inr (triHexPlanarFiniteTerminalMap n z i)) ∨
        (v = Sum.inl z ∧
          u = Sum.inr (triHexPlanarFiniteTerminalMap n z i))) := by
  have hmem : s(u, v) ∈ (triHexPlanarFiniteStarGraph n).edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    exact huv.1
  let e : (triHexPlanarFiniteStarGraph n).edgeSet := ⟨s(u, v), hmem⟩
  let a := (triHexPlanarFiniteStarEdgeEquiv n).symm e
  let z := a.1
  let i := a.2
  have ha : triHexPlanarFiniteStarEdgeEquiv n (z, i) = e := by
    simpa [z, i, a] using
      (triHexPlanarFiniteStarEdgeEquiv n).apply_symm_apply e
  have hedge : s(Sum.inl z,
      Sum.inr (triHexPlanarFiniteTerminalMap n z i)) = s(u, v) := by
    calc
      _ = (triHexPlanarFiniteStarEdgeEquiv n (z, i)).1 := rfl
      _ = e.1 := congrArg Subtype.val ha
      _ = _ := rfl
  have hopen : triHexLocalDirection
      (triHexPlanarFiniteStarConfigEquiv n omega z) i = true := by
    rw [triHexPlanarFiniteStarConfigEquiv_direction]
    rw [ha]
    have := huv.2
    rw [← hedge] at this
    change (extendActive (triHexPlanarFiniteStarGraph n) omega)
      ((triHexPlanarFiniteStarEdgeEquiv n (z, i)).1) = true at this
    rw [extendActive_apply, ha] at this
    exact this
  refine ⟨z, i, hopen, ?_⟩
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · exact Or.inl ⟨hu.symm, hv.symm⟩
  · exact Or.inr ⟨hv.symm, hu.symm⟩


def TriHexPlanarFiniteStarIsolatedCenter (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :=
  {z : TriHexPlanarFiniteCell n //
    triHexPlanarFiniteStarConfigEquiv n omega z = (false, false, false)}

noncomputable instance triHexPlanarFiniteStarIsolatedCenterFintype
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    Fintype (TriHexPlanarFiniteStarIsolatedCenter n omega) :=
  @Subtype.fintype (TriHexPlanarFiniteCell n)
    (fun z => triHexPlanarFiniteStarConfigEquiv n omega z =
      (false, false, false)) inferInstance inferInstance



theorem triHexPlanarFiniteStar_isolatedCenter_not_wired_adj
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    (z : TriHexPlanarFiniteStarIsolatedCenter n omega)
    (v : TriHexPlanarFiniteStarVertex n) :
    ¬ (wiredGraph (triHexPlanarFiniteStarGraph n)
      (triHexPlanarFiniteStarBoundary n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).Adj
        (Sum.inl z.1) v := by
  rw [wiredGraph_adj]
  rintro (hopen | hboundary)
  · obtain ⟨cell, i, hi, horient⟩ :=
      triHexPlanarFiniteStar_openSub_adj_eq_spoke n omega hopen
    rcases horient with ⟨hcenter, _⟩ | ⟨_, hcenter⟩
    · have hcell : cell = z.1 := Sum.inl.inj hcenter.symm
      subst cell
      rw [z.2] at hi
      fin_cases i <;> simp [triHexLocalDirection] at hi
    · have : Sum.inl z.1 = Sum.inr
          (triHexPlanarFiniteTerminalMap n cell i) := hcenter
      exact Sum.inl_ne_inr this
  · exact hboundary.2.1.elim



theorem triHexPlanarFiniteStar_wired_adj_representative_reachable
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    {u v : TriHexPlanarFiniteStarVertex n}
    (huv : (wiredGraph (triHexPlanarFiniteStarGraph n)
      (triHexPlanarFiniteStarBoundary n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).Adj u v) :
    (triHexPlanarFiniteStarWiredSectorGraph n omega).Reachable
      (triHexPlanarFiniteStarRepresentative n omega u)
      (triHexPlanarFiniteStarRepresentative n omega v) := by
  rw [wiredGraph_adj] at huv
  rcases huv with hopen | hboundary
  · exact (triHexPlanarFiniteStar_openSub_adj_representative_reachable
      n omega hopen).mono le_sup_left
  · rcases u with u | u <;> rcases v with v | v
    · exact hboundary.2.1.elim
    · exact hboundary.2.1.elim
    · exact hboundary.2.2.elim
    · apply SimpleGraph.Adj.reachable
      apply (show boundaryCliqueGraph (triHexPlanarFiniteBoundary n) ≤
        triHexPlanarFiniteStarWiredSectorGraph n omega from le_sup_right)
      rw [boundaryCliqueGraph_adj]
      exact ⟨fun huv => hboundary.1 (congrArg Sum.inr huv),
        hboundary.2.1, hboundary.2.2⟩


def triHexPlanarFiniteStarVertexComponentLabel (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    TriHexPlanarFiniteStarVertex n →
      (triHexPlanarFiniteStarWiredSectorGraph n omega).ConnectedComponent ⊕
        TriHexPlanarFiniteStarIsolatedCenter n omega
  | Sum.inr v => Sum.inl
      ((triHexPlanarFiniteStarWiredSectorGraph n omega).connectedComponentMk v)
  | Sum.inl z => if h : triHexPlanarFiniteStarConfigEquiv n omega z =
        (false, false, false) then
      Sum.inr ⟨z, h⟩
    else
      Sum.inl ((triHexPlanarFiniteStarWiredSectorGraph n omega).connectedComponentMk
        (triHexPlanarFiniteStarRepresentative n omega (Sum.inl z)))


theorem triHexPlanarFiniteStarVertexComponentLabel_eq_of_wired_adj
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    {u v : TriHexPlanarFiniteStarVertex n}
    (huv : (wiredGraph (triHexPlanarFiniteStarGraph n)
      (triHexPlanarFiniteStarBoundary n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).Adj u v) :
    triHexPlanarFiniteStarVertexComponentLabel n omega u =
      triHexPlanarFiniteStarVertexComponentLabel n omega v := by
  have hreach := triHexPlanarFiniteStar_wired_adj_representative_reachable
    n omega huv
  have hcomponent :
      (triHexPlanarFiniteStarWiredSectorGraph n omega).connectedComponentMk
          (triHexPlanarFiniteStarRepresentative n omega u) =
        (triHexPlanarFiniteStarWiredSectorGraph n omega).connectedComponentMk
          (triHexPlanarFiniteStarRepresentative n omega v) :=
    SimpleGraph.ConnectedComponent.sound hreach
  rw [wiredGraph_adj] at huv
  rcases huv with hopen | hboundary
  · obtain ⟨z, i, hi, horient⟩ :=
      triHexPlanarFiniteStar_openSub_adj_eq_spoke n omega hopen
    have hnot : triHexPlanarFiniteStarConfigEquiv n omega z ≠
        (false, false, false) := by
      intro hclosed
      rw [hclosed] at hi
      fin_cases i <;> simp [triHexLocalDirection] at hi
    rcases horient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [triHexPlanarFiniteStarVertexComponentLabel, dif_neg hnot]
      exact congrArg Sum.inl hcomponent
    · simp only [triHexPlanarFiniteStarVertexComponentLabel, dif_neg hnot]
      exact congrArg Sum.inl hcomponent
  · rcases u with u | u <;> rcases v with v | v
    · exact hboundary.2.1.elim
    · exact hboundary.2.1.elim
    · exact hboundary.2.2.elim
    · simp only [triHexPlanarFiniteStarVertexComponentLabel]
      exact congrArg Sum.inl hcomponent



def triHexPlanarFiniteStarConnectedComponentEquiv (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    (wiredGraph (triHexPlanarFiniteStarGraph n)
      (triHexPlanarFiniteStarBoundary n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).ConnectedComponent ≃
      (triHexPlanarFiniteStarWiredSectorGraph n omega).ConnectedComponent ⊕
        TriHexPlanarFiniteStarIsolatedCenter n omega where
  toFun := SimpleGraph.ConnectedComponent.lift
    (triHexPlanarFiniteStarVertexComponentLabel n omega) (by
      intro x y path _hpath
      clear _hpath
      induction path with
      | nil => rfl
      | cons h rest ih =>
          exact (triHexPlanarFiniteStarVertexComponentLabel_eq_of_wired_adj
            n omega h).trans ih)
  invFun
    | Sum.inl component => SimpleGraph.ConnectedComponent.lift
        (fun v => (wiredGraph (triHexPlanarFiniteStarGraph n)
          (triHexPlanarFiniteStarBoundary n)
          (extendActive (triHexPlanarFiniteStarGraph n) omega)).connectedComponentMk
            (Sum.inr v))
        (by
          intro x y path _
          apply SimpleGraph.ConnectedComponent.sound
          exact (triHexPlanarFiniteStar_wired_white_reachable_iff_sector
            n omega x y).mpr path.reachable) component
    | Sum.inr z => (wiredGraph (triHexPlanarFiniteStarGraph n)
        (triHexPlanarFiniteStarBoundary n)
        (extendActive (triHexPlanarFiniteStarGraph n) omega)).connectedComponentMk
          (Sum.inl z.1)
  left_inv component := by
    induction component using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      rcases v with z | v
      · by_cases hclosed : triHexPlanarFiniteStarConfigEquiv n omega z =
            (false, false, false)
        · simp [triHexPlanarFiniteStarVertexComponentLabel, hclosed]
        · simp only [SimpleGraph.ConnectedComponent.lift_mk,
            triHexPlanarFiniteStarVertexComponentLabel, hclosed, dite_false]
          apply SimpleGraph.ConnectedComponent.sound
          apply SimpleGraph.Adj.reachable
          apply (show openGraph (triHexPlanarFiniteStarGraph n)
              (extendActive (triHexPlanarFiniteStarGraph n) omega) ≤
            wiredGraph (triHexPlanarFiniteStarGraph n)
              (triHexPlanarFiniteStarBoundary n)
              (extendActive (triHexPlanarFiniteStarGraph n) omega) from le_sup_left)
          exact (triHexPlanarFiniteStar_openSub_adj_spoke n omega z
            (starFKRepresentativeDirection
              (triHexPlanarFiniteStarConfigEquiv n omega z))
            (starFKRepresentativeDirection_open_of_not_closed _ hclosed)).symm
      · simp [triHexPlanarFiniteStarVertexComponentLabel]
  right_inv label := by
    rcases label with component | z
    · induction component using SimpleGraph.ConnectedComponent.ind with
      | h v => simp [triHexPlanarFiniteStarVertexComponentLabel]
    · simp [triHexPlanarFiniteStarVertexComponentLabel, z.2]



theorem triHexPlanarFiniteStar_numClustersWired_eq_sector_add_isolated
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    numClustersWired (triHexPlanarFiniteStarGraph n)
        (triHexPlanarFiniteStarBoundary n)
        (extendActive (triHexPlanarFiniteStarGraph n) omega) =
      Nat.card
          (triHexPlanarFiniteStarWiredSectorGraph n omega).ConnectedComponent +
        Fintype.card (TriHexPlanarFiniteStarIsolatedCenter n omega) := by
  unfold numClustersWired
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← Fintype.card_sum]
  exact Fintype.card_congr
    (triHexPlanarFiniteStarConnectedComponentEquiv n omega)

end

end StatMech.FK.PeriodicPlanar
