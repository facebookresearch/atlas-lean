/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.TriHexFKGlobalSweep
import Code.FK.TriHexTorusDuality
import Code.FK.ActiveEdges
import Code.Universality.STTTransport









namespace StatMech.FK.PeriodicPlanar

open Universality
open scoped BigOperators



def triHexTorusTriangleEdgeBaseShift (L : ℕ) (i : Fin 3) : TorusSite L :=
  ![(0, 1), (1, 0), (1, 0)] i




def triHexTorusTriangleIndexEquiv (L : ℕ) :
    TriHexTorusEdgeIndex L ≃ TriHexTorusEdgeIndex L where
  toFun a := (a.1 + triHexTorusTriangleEdgeBaseShift L a.2, a.2)
  invFun a := (a.1 - triHexTorusTriangleEdgeBaseShift L a.2, a.2)
  left_inv := by
    rintro ⟨z, i⟩
    ext <;> simp
  right_inv := by
    rintro ⟨z, i⟩
    ext <;> simp


noncomputable def triHexTorusTriangleSweepEdgeEquiv (L : ℕ) [Fact (2 < L)] :
    TriHexTorusEdgeIndex L ≃ (triangularTorusGraph L).edgeSet :=
  (triHexTorusTriangleIndexEquiv L).trans
    (triangularTorusEdgeChartEquiv L)



noncomputable def triHexTorusStarSweepEdgeEquiv (L : ℕ) [Fact (2 < L)] :
    TriHexTorusEdgeIndex L ≃ (hexagonalTorusGraph L).edgeSet :=
  hexagonalTorusEdgeChartEquiv L



def triHexTorusCellTerminal (L : ℕ) (z : TorusSite L) (i : Fin 3) :
    TorusSite L :=
  z + hexagonalTorusStep L i



def triHexTriangleEdgeTerminal1 (i : Fin 3) : Fin 3 := ![1, 2, 0] i


def triHexTriangleEdgeTerminal2 (i : Fin 3) : Fin 3 := ![2, 0, 1] i


def triHexLocalDirection (config : LocalConfig) (i : Fin 3) : Bool :=
  ![config.1, config.2.1, config.2.2] i



theorem triHexTorusTriangleSweepEdge_val
    (L : ℕ) [Fact (2 < L)] (z : TorusSite L) (i : Fin 3) :
    ((triHexTorusTriangleSweepEdgeEquiv L (z, i) :
      (triangularTorusGraph L).edgeSet) : Sym2 (TorusSite L)) =
        s(triHexTorusCellTerminal L z (triHexTriangleEdgeTerminal1 i),
          triHexTorusCellTerminal L z (triHexTriangleEdgeTerminal2 i)) := by
  fin_cases i <;>
    simp [triHexTorusTriangleSweepEdgeEquiv,
      triHexTorusTriangleIndexEquiv, triHexTorusTriangleEdgeBaseShift,
      triangularTorusEdgeChartEquiv, triangularTorusEdgeChart,
      triangularTorusIndexedEdge, triHexTorusCellTerminal,
      triHexTriangleEdgeTerminal1, triHexTriangleEdgeTerminal2,
      triangularTorusStep, hexagonalTorusStep, Prod.ext_iff, add_assoc]



theorem triHexTorusStarSweepEdge_val
    (L : ℕ) [Fact (2 < L)] (z : TorusSite L) (i : Fin 3) :
    ((triHexTorusStarSweepEdgeEquiv L (z, i) :
      (hexagonalTorusGraph L).edgeSet) : Sym2 (HexTorusVertex L)) =
        s((z, false), (triHexTorusCellTerminal L z i, true)) := by
  rfl



theorem triangleFKLocalConnectivity_connects_of_direction
    (config : LocalConfig) (i : Fin 3)
    (h : triHexLocalDirection config i = true) :
    (triangleFKLocalConnectivity config).Connects
      (triHexTriangleEdgeTerminal1 i) (triHexTriangleEdgeTerminal2 i) := by
  rcases config with ⟨b0, b1, b2⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases i <;>
    simp_all [triHexLocalDirection, triangleFKLocalConnectivity,
      triHexTriangleEdgeTerminal1, triHexTriangleEdgeTerminal2,
      ThreeTerminalConnectivity.Connects]


def configReindexEquiv {E I : Type*} (e : I ≃ E) :
    ConfigSpace E ≃ ConfigSpace I where
  toFun omega i := omega (e i)
  invFun config a := config (e.symm a)
  left_inv omega := by
    funext a
    simp
  right_inv config := by
    funext i
    simp



def triHexTorusCellConfigEquiv (L : ℕ) :
    ConfigSpace (TriHexTorusEdgeIndex L) ≃
      (TorusSite L → LocalConfig) where
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



noncomputable def triangularTorusActiveConfigEquiv (L : ℕ) [Fact (2 < L)] :
    ConfigSpace (triangularTorusGraph L).edgeSet ≃
      (TorusSite L → LocalConfig) :=
  (configReindexEquiv (triHexTorusTriangleSweepEdgeEquiv L)).trans
    (triHexTorusCellConfigEquiv L)



noncomputable def hexagonalTorusActiveConfigEquiv (L : ℕ) [Fact (2 < L)] :
    ConfigSpace (hexagonalTorusGraph L).edgeSet ≃
      (TorusSite L → LocalConfig) :=
  (configReindexEquiv (triHexTorusStarSweepEdgeEquiv L)).trans
    (triHexTorusCellConfigEquiv L)

@[simp] theorem triangularTorusActiveConfigEquiv_apply
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet)
    (z : TorusSite L) :
    triangularTorusActiveConfigEquiv L omega z =
      (omega (triHexTorusTriangleSweepEdgeEquiv L (z, 0)),
        omega (triHexTorusTriangleSweepEdgeEquiv L (z, 1)),
        omega (triHexTorusTriangleSweepEdgeEquiv L (z, 2))) := rfl

@[simp] theorem triangularTorusActiveConfigEquiv_direction
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet)
    (z : TorusSite L) (i : Fin 3) :
    triHexLocalDirection (triangularTorusActiveConfigEquiv L omega z) i =
      omega (triHexTorusTriangleSweepEdgeEquiv L (z, i)) := by
  fin_cases i <;> rfl

@[simp] theorem hexagonalTorusActiveConfigEquiv_apply
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    (z : TorusSite L) :
    hexagonalTorusActiveConfigEquiv L omega z =
      (omega (triHexTorusStarSweepEdgeEquiv L (z, 0)),
        omega (triHexTorusStarSweepEdgeEquiv L (z, 1)),
        omega (triHexTorusStarSweepEdgeEquiv L (z, 2))) := rfl

@[simp] theorem hexagonalTorusActiveConfigEquiv_direction
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    (z : TorusSite L) (i : Fin 3) :
    triHexLocalDirection (hexagonalTorusActiveConfigEquiv L omega z) i =
      omega (triHexTorusStarSweepEdgeEquiv L (z, i)) := by
  fin_cases i <;> rfl



theorem triangularTorus_openSub_adj_cellEdge
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet)
    (z : TorusSite L) (i : Fin 3)
    (hopen : triHexLocalDirection
      (triangularTorusActiveConfigEquiv L omega z) i = true) :
    (openSub (triangularTorusGraph L)
      (extendActive (triangularTorusGraph L) omega)).Adj
        (triHexTorusCellTerminal L z (triHexTriangleEdgeTerminal1 i))
        (triHexTorusCellTerminal L z (triHexTriangleEdgeTerminal2 i)) := by
  rw [openSub_adj]
  let e := triHexTorusTriangleSweepEdgeEquiv L (z, i)
  have heq : (e.1 : Sym2 (TorusSite L)) =
      s(triHexTorusCellTerminal L z (triHexTriangleEdgeTerminal1 i),
        triHexTorusCellTerminal L z (triHexTriangleEdgeTerminal2 i)) :=
    triHexTorusTriangleSweepEdge_val L z i
  constructor
  · rw [← SimpleGraph.mem_edgeSet, ← heq]
    exact e.2
  · rw [← heq, extendActive_apply]
    fin_cases i <;> exact hopen



theorem hexagonalTorus_openSub_adj_spoke
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    (z : TorusSite L) (i : Fin 3)
    (hopen : triHexLocalDirection
      (hexagonalTorusActiveConfigEquiv L omega z) i = true) :
    (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Adj
        (z, false) (triHexTorusCellTerminal L z i, true) := by
  rw [openSub_adj]
  let e := triHexTorusStarSweepEdgeEquiv L (z, i)
  have heq : (e.1 : Sym2 (HexTorusVertex L)) =
      s((z, false), (triHexTorusCellTerminal L z i, true)) :=
    triHexTorusStarSweepEdge_val L z i
  constructor
  · rw [← SimpleGraph.mem_edgeSet, ← heq]
    exact e.2
  · rw [← heq, extendActive_apply]
    change omega (triHexTorusStarSweepEdgeEquiv L (z, i)) = true
    exact (hexagonalTorusActiveConfigEquiv_direction L omega z i).symm.trans hopen


theorem hexagonalTorus_openSub_adj_center_iff
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    (z : TorusSite L) (v : HexTorusVertex L) :
    (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Adj (z, false) v ↔
      ∃ i : Fin 3,
        triHexLocalDirection (hexagonalTorusActiveConfigEquiv L omega z) i = true ∧
          v = (triHexTorusCellTerminal L z i, true) := by
  constructor
  · intro h
    obtain ⟨⟨a, i⟩, ha⟩ := h.1
    rw [hexagonalTorusIndexedEdge, Sym2.eq_iff] at ha
    rcases ha with ⟨hcenter, hterminal⟩ | ⟨hbad, _hbad'⟩
    · have haz : a = z := congrArg Prod.fst hcenter
      subst a
      refine ⟨i, ?_, hterminal.symm⟩
      rw [hexagonalTorusActiveConfigEquiv_direction]
      let e := triHexTorusStarSweepEdgeEquiv L (z, i)
      have heq : (e.1 : Sym2 (HexTorusVertex L)) = s((z, false), v) := by
        rw [triHexTorusStarSweepEdge_val]
        exact congrArg (fun w => s((z, false), w)) hterminal
      have hopen := h.2
      rw [← heq, extendActive_apply] at hopen
      exact hopen
    · have : (true : Bool) = false := by
        exact congrArg Prod.snd _hbad'
      simp at this
  · rintro ⟨i, hopen, rfl⟩
    exact hexagonalTorus_openSub_adj_spoke L omega z i hopen



theorem triangleFKLocalConnectivity_connects_zero_one
    (config : LocalConfig) :
    (triangleFKLocalConnectivity config).Connects 0 1 ↔
      triHexLocalDirection config 2 = true ∨
        (triHexLocalDirection config 0 = true ∧
          triHexLocalDirection config 1 = true) := by
  rcases config with ⟨b0, b1, b2⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp [triangleFKLocalConnectivity, ThreeTerminalConnectivity.Connects,
      triHexLocalDirection]


theorem triangleFKLocalConnectivity_connects_zero_two
    (config : LocalConfig) :
    (triangleFKLocalConnectivity config).Connects 0 2 ↔
      triHexLocalDirection config 1 = true ∨
        (triHexLocalDirection config 0 = true ∧
          triHexLocalDirection config 2 = true) := by
  rcases config with ⟨b0, b1, b2⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp [triangleFKLocalConnectivity, ThreeTerminalConnectivity.Connects,
      triHexLocalDirection]


theorem triangleFKLocalConnectivity_connects_one_two
    (config : LocalConfig) :
    (triangleFKLocalConnectivity config).Connects 1 2 ↔
      triHexLocalDirection config 0 = true ∨
        (triHexLocalDirection config 1 = true ∧
          triHexLocalDirection config 2 = true) := by
  rcases config with ⟨b0, b1, b2⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp [triangleFKLocalConnectivity, ThreeTerminalConnectivity.Connects,
      triHexLocalDirection]



theorem triangularTorus_openSub_reachable_of_connects
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet)
    (z : TorusSite L) (i j : Fin 3)
    (hconnects : (triangleFKLocalConnectivity
      (triangularTorusActiveConfigEquiv L omega z)).Connects i j) :
    (openSub (triangularTorusGraph L)
      (extendActive (triangularTorusGraph L) omega)).Reachable
        (triHexTorusCellTerminal L z i)
        (triHexTorusCellTerminal L z j) := by
  let config := triangularTorusActiveConfigEquiv L omega z
  let edgeReach (k : Fin 3)
      (h : triHexLocalDirection config k = true) :=
    SimpleGraph.Adj.reachable
      (triangularTorus_openSub_adj_cellEdge L omega z k h)
  have reach01 (h : (triangleFKLocalConnectivity config).Connects 0 1) :
      (openSub (triangularTorusGraph L)
        (extendActive (triangularTorusGraph L) omega)).Reachable
          (triHexTorusCellTerminal L z 0) (triHexTorusCellTerminal L z 1) := by
    rcases (triangleFKLocalConnectivity_connects_zero_one config).mp h with
      h2 | ⟨h0, h1⟩
    · exact edgeReach 2 h2
    · exact (edgeReach 1 h1).symm.trans (edgeReach 0 h0).symm
  have reach02 (h : (triangleFKLocalConnectivity config).Connects 0 2) :
      (openSub (triangularTorusGraph L)
        (extendActive (triangularTorusGraph L) omega)).Reachable
          (triHexTorusCellTerminal L z 0) (triHexTorusCellTerminal L z 2) := by
    rcases (triangleFKLocalConnectivity_connects_zero_two config).mp h with
      h1 | ⟨h0, h2⟩
    · exact (edgeReach 1 h1).symm
    · exact (edgeReach 2 h2).trans (edgeReach 0 h0)
  have reach12 (h : (triangleFKLocalConnectivity config).Connects 1 2) :
      (openSub (triangularTorusGraph L)
        (extendActive (triangularTorusGraph L) omega)).Reachable
          (triHexTorusCellTerminal L z 1) (triHexTorusCellTerminal L z 2) := by
    rcases (triangleFKLocalConnectivity_connects_one_two config).mp h with
      h0 | ⟨h1, h2⟩
    · exact edgeReach 0 h0
    · exact (edgeReach 2 h2).symm.trans (edgeReach 1 h1).symm
  fin_cases i <;> fin_cases j
  · exact SimpleGraph.Reachable.refl _
  · exact reach01 hconnects
  · exact reach02 hconnects
  · exact (reach01
      ((triangleFKLocalConnectivity config).connects_symm 0 1 |>.mpr hconnects)).symm
  · exact SimpleGraph.Reachable.refl _
  · exact reach12 hconnects
  · exact (reach02
      ((triangleFKLocalConnectivity config).connects_symm 0 2 |>.mpr hconnects)).symm
  · exact (reach12
      ((triangleFKLocalConnectivity config).connects_symm 1 2 |>.mpr hconnects)).symm
  · exact SimpleGraph.Reachable.refl _



noncomputable def triangularTorusTerminalSectorGraph
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet) :
    SimpleGraph (TorusSite L) :=
  triHexFKTerminalSectorGraph (triHexTorusCellTerminal L)
    (fun z => triangleFKLocalConnectivity
      (triangularTorusActiveConfigEquiv L omega z))



theorem triangularTorus_openSub_adj_terminalSectorGraph
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet)
    {x y : TorusSite L}
    (hxy : (openSub (triangularTorusGraph L)
      (extendActive (triangularTorusGraph L) omega)).Adj x y) :
    (triangularTorusTerminalSectorGraph L omega).Adj x y := by
  have hmem : s(x, y) ∈ (triangularTorusGraph L).edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    exact hxy.1
  let e : (triangularTorusGraph L).edgeSet := ⟨s(x, y), hmem⟩
  let a := (triHexTorusTriangleSweepEdgeEquiv L).symm e
  let z := a.1
  let i := a.2
  have ha : triHexTorusTriangleSweepEdgeEquiv L (z, i) = e := by
    simpa [z, i, a] using
      (triHexTorusTriangleSweepEdgeEquiv L).apply_symm_apply e
  have hedge : s(x, y) =
      s(triHexTorusCellTerminal L z (triHexTriangleEdgeTerminal1 i),
        triHexTorusCellTerminal L z (triHexTriangleEdgeTerminal2 i)) := by
    calc
      s(x, y) = e.1 := rfl
      _ = (triHexTorusTriangleSweepEdgeEquiv L (z, i)).1 :=
        congrArg Subtype.val ha.symm
      _ = _ := triHexTorusTriangleSweepEdge_val L z i
  have hopen : omega e = true := by
    have := hxy.2
    simpa [extendActive, e, hmem] using this
  have hlocal : triHexLocalDirection
      (triangularTorusActiveConfigEquiv L omega z) i = true := by
    have hopen' : omega (triHexTorusTriangleSweepEdgeEquiv L (z, i)) = true := by
      rw [ha]
      exact hopen
    rw [triangularTorusActiveConfigEquiv_direction]
    exact hopen'
  have hconnects := triangleFKLocalConnectivity_connects_of_direction
    (triangularTorusActiveConfigEquiv L omega z) i hlocal
  rw [triangularTorusTerminalSectorGraph, triHexFKTerminalSectorGraph,
    SimpleGraph.fromEdgeSet_adj]
  exact ⟨⟨z, triHexTriangleEdgeTerminal1 i, triHexTriangleEdgeTerminal2 i,
    hconnects, hedge⟩, hxy.ne⟩



theorem triangularTorus_terminalSectorGraph_adj_openSub_reachable
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet)
    {x y : TorusSite L}
    (hxy : (triangularTorusTerminalSectorGraph L omega).Adj x y) :
    (openSub (triangularTorusGraph L)
      (extendActive (triangularTorusGraph L) omega)).Reachable x y := by
  rw [triangularTorusTerminalSectorGraph, triHexFKTerminalSectorGraph,
    SimpleGraph.fromEdgeSet_adj] at hxy
  obtain ⟨⟨z, i, j, hconnects, hedge⟩, _hxyne⟩ := hxy
  have hreach := triangularTorus_openSub_reachable_of_connects
    L omega z i j hconnects
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨hxi, hyj⟩ | ⟨hxj, hyi⟩
  · simpa [hxi, hyj] using hreach
  · simpa [hxj, hyi] using hreach.symm



theorem triangularTorus_openSub_reachable_iff_terminalSectorGraph
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet)
    (x y : TorusSite L) :
    (openSub (triangularTorusGraph L)
      (extendActive (triangularTorusGraph L) omega)).Reachable x y ↔
      (triangularTorusTerminalSectorGraph L omega).Reachable x y := by
  constructor
  · exact fun h => Universality.reach_collapse _ _ id
      (fun a b hab => SimpleGraph.Adj.reachable
        (triangularTorus_openSub_adj_terminalSectorGraph L omega hab))
      rfl rfl h
  · exact fun h => Universality.reach_collapse _ _ id
      (fun _a _b hab =>
        triangularTorus_terminalSectorGraph_adj_openSub_reachable L omega hab)
      rfl rfl h



noncomputable def connectedComponentEquivOfReachableIff
    {V : Type*} (G H : SimpleGraph V)
    (h : ∀ x y, G.Reachable x y ↔ H.Reachable x y) :
    G.ConnectedComponent ≃ H.ConnectedComponent where
  toFun := SimpleGraph.ConnectedComponent.lift
    (fun x => H.connectedComponentMk x) (by
      intro x y path _hpath
      exact SimpleGraph.ConnectedComponent.sound
        ((h x y).mp path.reachable))
  invFun := SimpleGraph.ConnectedComponent.lift
    (fun x => G.connectedComponentMk x) (by
      intro x y path _hpath
      exact SimpleGraph.ConnectedComponent.sound
        ((h x y).mpr path.reachable))
  left_inv component := by
    induction component using SimpleGraph.ConnectedComponent.ind with
    | h x => simp only [SimpleGraph.ConnectedComponent.lift_mk]
  right_inv component := by
    induction component using SimpleGraph.ConnectedComponent.ind with
    | h x => simp only [SimpleGraph.ConnectedComponent.lift_mk]



theorem reachable_map_of_adj_reachable
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (f : V → W) (hedge : ∀ x y, G.Adj x y → H.Reachable (f x) (f y))
    {x y : V} (hxy : G.Reachable x y) : H.Reachable (f x) (f y) := by
  obtain ⟨walk⟩ := hxy
  induction walk with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons h rest ih => exact (hedge _ _ h).trans ih



theorem triangularTorus_numClusters_eq_terminalSector
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet) :
    numClusters (triangularTorusGraph L)
        (extendActive (triangularTorusGraph L) omega) =
      Fintype.card (triangularTorusTerminalSectorGraph L omega).ConnectedComponent := by
  unfold numClusters
  exact Fintype.card_congr
    (connectedComponentEquivOfReachableIff _ _
      (triangularTorus_openSub_reachable_iff_terminalSectorGraph L omega))





theorem starFKLocalConnectivity_connects_iff
    (config : LocalConfig) (i j : Fin 3) :
    (starFKLocalConnectivity config).Connects i j ↔
      i = j ∨ (triHexLocalDirection config i = true ∧
        triHexLocalDirection config j = true) := by
  rcases config with ⟨b0, b1, b2⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;>
    fin_cases i <;> fin_cases j <;>
    simp [starFKLocalConnectivity, ThreeTerminalConnectivity.Connects,
      triHexLocalDirection]



theorem hexagonalTorus_openSub_reachable_of_connects
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    (z : TorusSite L) (i j : Fin 3)
    (hconnects : (starFKLocalConnectivity
      (hexagonalTorusActiveConfigEquiv L omega z)).Connects i j) :
    (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Reachable
        (triHexTorusCellTerminal L z i, true)
        (triHexTorusCellTerminal L z j, true) := by
  rcases (starFKLocalConnectivity_connects_iff
    (hexagonalTorusActiveConfigEquiv L omega z) i j).mp hconnects with
    rfl | ⟨hi, hj⟩
  · exact SimpleGraph.Reachable.refl _
  · exact (SimpleGraph.Adj.reachable
      (hexagonalTorus_openSub_adj_spoke L omega z i hi)).symm.trans
        (SimpleGraph.Adj.reachable
          (hexagonalTorus_openSub_adj_spoke L omega z j hj))



noncomputable def hexagonalTorusTerminalSectorGraph
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) :
    SimpleGraph (TorusSite L) :=
  triHexFKTerminalSectorGraph (triHexTorusCellTerminal L)
    (fun z => starFKLocalConnectivity
      (hexagonalTorusActiveConfigEquiv L omega z))



theorem triHexFKTerminalSectorGraph_reachable_of_connects
    {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (terminal : I → Fin 3 → V)
    (sector : I → ThreeTerminalConnectivity)
    (cell : I) (i j : Fin 3) (hconnects : (sector cell).Connects i j) :
    (triHexFKTerminalSectorGraph terminal sector).Reachable
      (terminal cell i) (terminal cell j) := by
  by_cases hterm : terminal cell i = terminal cell j
  · simpa [hterm] using
      (SimpleGraph.Reachable.refl (G := triHexFKTerminalSectorGraph terminal sector)
        (terminal cell i))
  · apply SimpleGraph.Adj.reachable
    rw [triHexFKTerminalSectorGraph, SimpleGraph.fromEdgeSet_adj]
    exact ⟨⟨cell, i, j, hconnects, rfl⟩, hterm⟩



def starFKRepresentativeDirection (config : LocalConfig) : Fin 3 :=
  if config.1 then 0 else if config.2.1 then 1 else 2

theorem starFKRepresentativeDirection_open_of_open
    (config : LocalConfig) (i : Fin 3)
    (hi : triHexLocalDirection config i = true) :
    triHexLocalDirection config (starFKRepresentativeDirection config) = true := by
  rcases config with ⟨b0, b1, b2⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases i <;>
    simp_all [triHexLocalDirection, starFKRepresentativeDirection]



noncomputable def hexagonalTorusOpenRepresentative
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) :
    HexTorusVertex L → TorusSite L
  | (z, true) => z
  | (z, false) => triHexTorusCellTerminal L z
      (starFKRepresentativeDirection
        (hexagonalTorusActiveConfigEquiv L omega z))



theorem hexagonalTorus_openSub_adj_representative_reachable
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    {u v : HexTorusVertex L}
    (huv : (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Adj u v) :
    (hexagonalTorusTerminalSectorGraph L omega).Reachable
      (hexagonalTorusOpenRepresentative L omega u)
      (hexagonalTorusOpenRepresentative L omega v) := by
  obtain ⟨⟨z, i⟩, hedge⟩ := huv.1
  rw [hexagonalTorusIndexedEdge, Sym2.eq_iff] at hedge
  have hopen : triHexLocalDirection
      (hexagonalTorusActiveConfigEquiv L omega z) i = true := by
    rw [hexagonalTorusActiveConfigEquiv_direction]
    let e := triHexTorusStarSweepEdgeEquiv L (z, i)
    have heq : (e.1 : Sym2 (HexTorusVertex L)) = s(u, v) := by
      rw [triHexTorusStarSweepEdge_val]
      exact (Sym2.eq_iff).2 hedge
    have := huv.2
    rw [← heq, extendActive_apply] at this
    exact this
  have hselected := starFKRepresentativeDirection_open_of_open
    (hexagonalTorusActiveConfigEquiv L omega z) i hopen
  have hconnects : (starFKLocalConnectivity
      (hexagonalTorusActiveConfigEquiv L omega z)).Connects
        (starFKRepresentativeDirection
          (hexagonalTorusActiveConfigEquiv L omega z)) i :=
    (starFKLocalConnectivity_connects_iff _ _ _).2
      (Or.inr ⟨hselected, hopen⟩)
  have hreach := triHexFKTerminalSectorGraph_reachable_of_connects
    (triHexTorusCellTerminal L)
    (fun z => starFKLocalConnectivity
      (hexagonalTorusActiveConfigEquiv L omega z)) z _ _ hconnects
  rcases hedge with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · subst u
    subst v
    simpa [hexagonalTorusOpenRepresentative,
      hexagonalTorusTerminalSectorGraph] using hreach
  · subst u
    subst v
    simpa [hexagonalTorusOpenRepresentative,
      hexagonalTorusTerminalSectorGraph] using hreach.symm



theorem hexagonalTorus_terminalSectorGraph_adj_openSub_reachable
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    {x y : TorusSite L}
    (hxy : (hexagonalTorusTerminalSectorGraph L omega).Adj x y) :
    (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Reachable
        (x, true) (y, true) := by
  rw [hexagonalTorusTerminalSectorGraph, triHexFKTerminalSectorGraph,
    SimpleGraph.fromEdgeSet_adj] at hxy
  obtain ⟨⟨z, i, j, hconnects, hedge⟩, _hxyne⟩ := hxy
  have hreach := hexagonalTorus_openSub_reachable_of_connects
    L omega z i j hconnects
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨hxi, hyj⟩ | ⟨hxj, hyi⟩
  · simpa [hxi, hyj] using hreach
  · simpa [hxj, hyi] using hreach.symm



theorem hexagonalTorus_openSub_white_reachable_iff_terminalSectorGraph
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    (x y : TorusSite L) :
    (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Reachable (x, true) (y, true) ↔
      (hexagonalTorusTerminalSectorGraph L omega).Reachable x y := by
  constructor
  · intro h
    have hc := reachable_map_of_adj_reachable
      (openSub (hexagonalTorusGraph L)
        (extendActive (hexagonalTorusGraph L) omega))
      (hexagonalTorusTerminalSectorGraph L omega)
      (hexagonalTorusOpenRepresentative L omega)
      (fun _ _ hab =>
        hexagonalTorus_openSub_adj_representative_reachable L omega hab)
      h
    simpa [hexagonalTorusOpenRepresentative] using hc
  · intro h
    exact reachable_map_of_adj_reachable
      (hexagonalTorusTerminalSectorGraph L omega)
      (openSub (hexagonalTorusGraph L)
        (extendActive (hexagonalTorusGraph L) omega))
      (fun z => (z, true))
      (fun _ _ hab =>
        hexagonalTorus_terminalSectorGraph_adj_openSub_reachable L omega hab)
      h


theorem hexagonalTorus_openSub_adj_eq_spoke
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    {u v : HexTorusVertex L}
    (huv : (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Adj u v) :
    ∃ z i, triHexLocalDirection
        (hexagonalTorusActiveConfigEquiv L omega z) i = true ∧
      ((u = (z, false) ∧ v = (triHexTorusCellTerminal L z i, true)) ∨
        (v = (z, false) ∧ u = (triHexTorusCellTerminal L z i, true))) := by
  obtain ⟨⟨z, i⟩, hedge⟩ := huv.1
  rw [hexagonalTorusIndexedEdge, Sym2.eq_iff] at hedge
  have hopen : triHexLocalDirection
      (hexagonalTorusActiveConfigEquiv L omega z) i = true := by
    rw [hexagonalTorusActiveConfigEquiv_direction]
    let e := triHexTorusStarSweepEdgeEquiv L (z, i)
    have heq : (e.1 : Sym2 (HexTorusVertex L)) = s(u, v) := by
      rw [triHexTorusStarSweepEdge_val]
      exact (Sym2.eq_iff).2 hedge
    have := huv.2
    rw [← heq, extendActive_apply] at this
    exact this
  refine ⟨z, i, hopen, ?_⟩
  rcases hedge with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · exact Or.inl ⟨hu.symm, by
      simpa [triHexTorusCellTerminal] using hv.symm⟩
  · exact Or.inr ⟨hv.symm, by
      simpa [triHexTorusCellTerminal] using hu.symm⟩



def HexagonalTorusIsolatedCenter
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) :=
  {z : TorusSite L //
    hexagonalTorusActiveConfigEquiv L omega z = (false, false, false)}

noncomputable instance hexagonalTorusIsolatedCenterFintype
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) :
    Fintype (HexagonalTorusIsolatedCenter L omega) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

theorem starFKRepresentativeDirection_open_of_not_closed
    (config : LocalConfig) (h : config ≠ (false, false, false)) :
    triHexLocalDirection config (starFKRepresentativeDirection config) = true := by
  rcases config with ⟨b0, b1, b2⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp_all [triHexLocalDirection, starFKRepresentativeDirection]


theorem hexagonalTorus_isolatedCenter_not_adj
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    (z : HexagonalTorusIsolatedCenter L omega) (v : HexTorusVertex L) :
    ¬ (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Adj (z.1, false) v := by
  rw [hexagonalTorus_openSub_adj_center_iff]
  rintro ⟨i, hi, _hv⟩
  rw [z.2] at hi
  fin_cases i <;> simp [triHexLocalDirection] at hi



noncomputable def hexagonalTorusVertexComponentLabel
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) :
    HexTorusVertex L →
      (hexagonalTorusTerminalSectorGraph L omega).ConnectedComponent ⊕
        HexagonalTorusIsolatedCenter L omega
  | (z, true) => Sum.inl
      ((hexagonalTorusTerminalSectorGraph L omega).connectedComponentMk z)
  | (z, false) => if h : hexagonalTorusActiveConfigEquiv L omega z =
        (false, false, false) then
      Sum.inr ⟨z, h⟩
    else
      Sum.inl ((hexagonalTorusTerminalSectorGraph L omega).connectedComponentMk
        (hexagonalTorusOpenRepresentative L omega (z, false)))


theorem hexagonalTorusVertexComponentLabel_eq_of_adj
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    {u v : HexTorusVertex L}
    (huv : (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Adj u v) :
    hexagonalTorusVertexComponentLabel L omega u =
      hexagonalTorusVertexComponentLabel L omega v := by
  obtain ⟨z, i, hi, horient⟩ :=
    hexagonalTorus_openSub_adj_eq_spoke L omega huv
  have hnot : hexagonalTorusActiveConfigEquiv L omega z ≠
      (false, false, false) := by
    intro hclosed
    rw [hclosed] at hi
    fin_cases i <;> simp [triHexLocalDirection] at hi
  have hreach := hexagonalTorus_openSub_adj_representative_reachable L omega huv
  have hcomponent :
      (hexagonalTorusTerminalSectorGraph L omega).connectedComponentMk
          (hexagonalTorusOpenRepresentative L omega u) =
        (hexagonalTorusTerminalSectorGraph L omega).connectedComponentMk
          (hexagonalTorusOpenRepresentative L omega v) :=
    SimpleGraph.ConnectedComponent.sound hreach
  rcases horient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [hexagonalTorusVertexComponentLabel, dif_neg hnot]
    exact congrArg Sum.inl hcomponent
  · simp only [hexagonalTorusVertexComponentLabel, dif_neg hnot]
    exact congrArg Sum.inl hcomponent



noncomputable def hexagonalTorusConnectedComponentEquiv
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) :
    (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).ConnectedComponent ≃
      (hexagonalTorusTerminalSectorGraph L omega).ConnectedComponent ⊕
        HexagonalTorusIsolatedCenter L omega where
  toFun := SimpleGraph.ConnectedComponent.lift
    (hexagonalTorusVertexComponentLabel L omega) (by
      intro x y path _hpath
      clear _hpath
      induction path with
      | nil => rfl
      | cons h rest ih =>
          exact (hexagonalTorusVertexComponentLabel_eq_of_adj L omega h).trans ih)
  invFun
    | Sum.inl component => SimpleGraph.ConnectedComponent.lift
        (fun z => (openSub (hexagonalTorusGraph L)
          (extendActive (hexagonalTorusGraph L) omega)).connectedComponentMk (z, true))
        (by
          intro x y path _hpath
          apply SimpleGraph.ConnectedComponent.sound
          exact (hexagonalTorus_openSub_white_reachable_iff_terminalSectorGraph
            L omega x y).mpr path.reachable) component
    | Sum.inr z => (openSub (hexagonalTorusGraph L)
        (extendActive (hexagonalTorusGraph L) omega)).connectedComponentMk (z.1, false)
  left_inv component := by
    induction component using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      rcases v with ⟨z, b⟩
      cases b
      · by_cases hclosed : hexagonalTorusActiveConfigEquiv L omega z =
            (false, false, false)
        · simp [hexagonalTorusVertexComponentLabel, hclosed]
        · simp only [SimpleGraph.ConnectedComponent.lift_mk,
            hexagonalTorusVertexComponentLabel, hclosed, dite_false]
          apply SimpleGraph.ConnectedComponent.sound
          apply SimpleGraph.Adj.reachable
          simpa [hexagonalTorusOpenRepresentative] using
            (hexagonalTorus_openSub_adj_spoke L omega z
              (starFKRepresentativeDirection
                (hexagonalTorusActiveConfigEquiv L omega z))
              (starFKRepresentativeDirection_open_of_not_closed _ hclosed)).symm
      · simp [hexagonalTorusVertexComponentLabel]
  right_inv label := by
    rcases label with component | z
    · induction component using SimpleGraph.ConnectedComponent.ind with
      | h x => simp [hexagonalTorusVertexComponentLabel]
    · simp [hexagonalTorusVertexComponentLabel, z.2]



theorem hexagonalTorus_numClusters_eq_terminalSector_add_isolated
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) :
    numClusters (hexagonalTorusGraph L)
        (extendActive (hexagonalTorusGraph L) omega) =
      Fintype.card (hexagonalTorusTerminalSectorGraph L omega).ConnectedComponent +
        Fintype.card (HexagonalTorusIsolatedCenter L omega) := by
  unfold numClusters
  rw [← Fintype.card_sum]
  exact Fintype.card_congr (hexagonalTorusConnectedComponentEquiv L omega)

section ActiveOdds

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



theorem edgeProductW_extendActive_eq_activeProduct
    (pf : Sym2 V → ℝ) (omega : ConfigSpace G.edgeSet) :
    edgeProductW G pf (extendActive G omega) =
      ∏ e : G.edgeSet, if omega e then pf e.1 else 1 - pf e.1 := by
  unfold edgeProductW
  rw [Finset.prod_subtype (p := fun e => e ∈ G.edgeSet)
    G.edgeFinset (fun e => by
    simpa [SimpleGraph.mem_edgeFinset])]
  apply Fintype.prod_congr
  intro e
  rw [extendActive_apply]



theorem edgeProductW_extendActive_odds_factor
    (pf : Sym2 V → ℝ) (odds : G.edgeSet → ℝ)
    (h : ∀ e : G.edgeSet, pf e.1 = (1 - pf e.1) * odds e)
    (omega : ConfigSpace G.edgeSet) :
    edgeProductW G pf (extendActive G omega) =
      (∏ e : G.edgeSet, (1 - pf e.1)) *
        ∏ e : G.edgeSet, if omega e then odds e else 1 := by
  rw [edgeProductW_extendActive_eq_activeProduct]
  calc
    (∏ e : G.edgeSet, if omega e then pf e.1 else 1 - pf e.1) =
        ∏ e : G.edgeSet,
          (1 - pf e.1) * (if omega e then odds e else 1) := by
      apply Fintype.prod_congr
      intro e
      by_cases he : omega e
      · rw [if_pos he, if_pos he]
        exact h e
      · rw [if_neg he, if_neg he, mul_one]
    _ = (∏ e : G.edgeSet, (1 - pf e.1)) *
          ∏ e : G.edgeSet, if omega e then odds e else 1 := by
      rw [Finset.prod_mul_distrib]

end ActiveOdds




def triHexDirectionOdds (y0 y1 y2 : ℝ) (i : Fin 3) : ℝ :=
  ![y0, y1, y2] i


def starFKIsolatedCenterFactor (q : ℝ) (config : LocalConfig) : ℝ :=
  if config = (false, false, false) then q else 1

theorem triangleFKLocalOddsWeight_eq_directionProduct
    (y0 y1 y2 : ℝ) (config : LocalConfig) :
    triangleFKLocalOddsWeight y0 y1 y2 config =
      ∏ i : Fin 3, if triHexLocalDirection config i then
        triHexDirectionOdds y0 y1 y2 i else 1 := by
  rcases config with ⟨b0, b1, b2⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp [triangleFKLocalOddsWeight, triHexLocalDirection,
      triHexDirectionOdds, Fin.prod_univ_succ] <;> ring

theorem starFKLocalOddsWeight_eq_isolated_mul_directionProduct
    (q y0 y1 y2 : ℝ) (config : LocalConfig) :
    starFKLocalOddsWeight q y0 y1 y2 config =
      starFKIsolatedCenterFactor q config *
        ∏ i : Fin 3, if triHexLocalDirection config i then
          triHexDirectionOdds y0 y1 y2 i else 1 := by
  rcases config with ⟨b0, b1, b2⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp [starFKLocalOddsWeight, starFKIsolatedCenterFactor,
      triHexLocalDirection, triHexDirectionOdds, Fin.prod_univ_succ] <;> ring

theorem triangleFKGlobalLocalOdds_eq_directionProduct
    {I : Type*} [Fintype I] (y0 y1 y2 : ℝ)
    (config : I → LocalConfig) :
    (∏ z, triangleFKLocalOddsWeight y0 y1 y2 (config z)) =
      ∏ a : I × Fin 3, if triHexLocalDirection (config a.1) a.2 then
        triHexDirectionOdds y0 y1 y2 a.2 else 1 := by
  rw [Fintype.prod_prod_type]
  apply Fintype.prod_congr
  intro z
  exact triangleFKLocalOddsWeight_eq_directionProduct y0 y1 y2 (config z)

theorem starFKGlobalLocalOdds_eq_isolated_mul_directionProduct
    {I : Type*} [Fintype I] (q y0 y1 y2 : ℝ)
    (config : I → LocalConfig) :
    (∏ z, starFKLocalOddsWeight q y0 y1 y2 (config z)) =
      (∏ z, starFKIsolatedCenterFactor q (config z)) *
        ∏ a : I × Fin 3, if triHexLocalDirection (config a.1) a.2 then
          triHexDirectionOdds y0 y1 y2 a.2 else 1 := by
  calc
    (∏ z, starFKLocalOddsWeight q y0 y1 y2 (config z)) =
        ∏ z, starFKIsolatedCenterFactor q (config z) *
          (∏ i : Fin 3, if triHexLocalDirection (config z) i then
            triHexDirectionOdds y0 y1 y2 i else 1) := by
      apply Fintype.prod_congr
      intro z
      exact starFKLocalOddsWeight_eq_isolated_mul_directionProduct
        q y0 y1 y2 (config z)
    _ = (∏ z, starFKIsolatedCenterFactor q (config z)) *
        ∏ z, ∏ i : Fin 3, if triHexLocalDirection (config z) i then
          triHexDirectionOdds y0 y1 y2 i else 1 := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ z, starFKIsolatedCenterFactor q (config z)) *
        ∏ a : I × Fin 3, if triHexLocalDirection (config a.1) a.2 then
          triHexDirectionOdds y0 y1 y2 a.2 else 1 := by
      rw [Fintype.prod_prod_type]


noncomputable def triangularTorusSweepEdgeOdds
    (L : ℕ) [Fact (2 < L)] (y0 y1 y2 : ℝ)
    (e : (triangularTorusGraph L).edgeSet) : ℝ :=
  triHexDirectionOdds y0 y1 y2
    ((triHexTorusTriangleSweepEdgeEquiv L).symm e).2


noncomputable def hexagonalTorusSweepEdgeOdds
    (L : ℕ) [Fact (2 < L)] (y0 y1 y2 : ℝ)
    (e : (hexagonalTorusGraph L).edgeSet) : ℝ :=
  triHexDirectionOdds y0 y1 y2
    ((triHexTorusStarSweepEdgeEquiv L).symm e).2

theorem triangularTorus_localOddsProduct_eq_activeOddsProduct
    (L : ℕ) [Fact (2 < L)] (y0 y1 y2 : ℝ)
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet) :
    (∏ z, triangleFKLocalOddsWeight y0 y1 y2
      (triangularTorusActiveConfigEquiv L omega z)) =
        ∏ e : (triangularTorusGraph L).edgeSet,
          if omega e then triangularTorusSweepEdgeOdds L y0 y1 y2 e else 1 := by
  rw [triangleFKGlobalLocalOdds_eq_directionProduct]
  calc
    (∏ a : TorusSite L × Fin 3,
        if triHexLocalDirection (triangularTorusActiveConfigEquiv L omega a.1) a.2 then
          triHexDirectionOdds y0 y1 y2 a.2 else 1) =
      ∏ a : TriHexTorusEdgeIndex L,
        if omega (triHexTorusTriangleSweepEdgeEquiv L a) then
          triHexDirectionOdds y0 y1 y2 a.2 else 1 := by
      apply Fintype.prod_congr
      rintro ⟨z, i⟩
      fin_cases i <;> rfl
    _ = ∏ e : (triangularTorusGraph L).edgeSet,
          if omega e then triangularTorusSweepEdgeOdds L y0 y1 y2 e else 1 := by
      simpa [triangularTorusSweepEdgeOdds] using
        (triHexTorusTriangleSweepEdgeEquiv L).prod_comp
          (fun e => if omega e then
            triangularTorusSweepEdgeOdds L y0 y1 y2 e else 1)

theorem hexagonalTorus_localOddsProduct_eq_activeOddsProduct
    (L : ℕ) [Fact (2 < L)] (q y0 y1 y2 : ℝ)
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) :
    (∏ z, starFKLocalOddsWeight q y0 y1 y2
      (hexagonalTorusActiveConfigEquiv L omega z)) =
      (∏ z, starFKIsolatedCenterFactor q
        (hexagonalTorusActiveConfigEquiv L omega z)) *
        ∏ e : (hexagonalTorusGraph L).edgeSet,
          if omega e then hexagonalTorusSweepEdgeOdds L y0 y1 y2 e else 1 := by
  rw [starFKGlobalLocalOdds_eq_isolated_mul_directionProduct]
  congr 1
  calc
    (∏ a : TorusSite L × Fin 3,
        if triHexLocalDirection (hexagonalTorusActiveConfigEquiv L omega a.1) a.2 then
          triHexDirectionOdds y0 y1 y2 a.2 else 1) =
      ∏ a : TriHexTorusEdgeIndex L,
        if omega (triHexTorusStarSweepEdgeEquiv L a) then
          triHexDirectionOdds y0 y1 y2 a.2 else 1 := by
      apply Fintype.prod_congr
      rintro ⟨z, i⟩
      fin_cases i <;> rfl
    _ = ∏ e : (hexagonalTorusGraph L).edgeSet,
          if omega e then hexagonalTorusSweepEdgeOdds L y0 y1 y2 e else 1 := by
      simpa [hexagonalTorusSweepEdgeOdds] using
        (triHexTorusStarSweepEdgeEquiv L).prod_comp
          (fun e => if omega e then
            hexagonalTorusSweepEdgeOdds L y0 y1 y2 e else 1)



theorem fintype_prod_ite_eq_pow_card_subtype
    {I : Type*} [Fintype I] (P : I → Prop) [DecidablePred P]
    [Fintype {i // P i}] (q : ℝ) :
    (∏ i, if P i then q else 1) = q ^ Fintype.card {i // P i} := by
  classical
  rw [Fintype.card_subtype P]
  change Finset.univ.prod (fun i => if P i then q else 1) = _
  rw [Finset.prod_ite]
  simp



theorem hexagonalTorus_isolatedCenterFactor_product
    (L : ℕ) [Fact (2 < L)] (q : ℝ)
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) :
    (∏ z, starFKIsolatedCenterFactor q
      (hexagonalTorusActiveConfigEquiv L omega z)) =
        q ^ Fintype.card (HexagonalTorusIsolatedCenter L omega) := by
  unfold starFKIsolatedCenterFactor HexagonalTorusIsolatedCenter
  exact @fintype_prod_ite_eq_pow_card_subtype (TorusSite L) inferInstance
    (fun z => hexagonalTorusActiveConfigEquiv L omega z =
      (false, false, false)) inferInstance
    (hexagonalTorusIsolatedCenterFintype L omega) q



noncomputable def triHexTorusSectorClusterWeight
    (L : ℕ) [Fact (2 < L)] (q : ℝ)
    (sector : TorusSite L → ThreeTerminalConnectivity) : ℝ :=
  q ^ Fintype.card
    (triHexFKTerminalSectorGraph (triHexTorusCellTerminal L) sector).ConnectedComponent



theorem triangularTorus_activeWeight_eq_closedProduct_mul_cellWeight
    (L : ℕ) [Fact (2 < L)] (pf : Sym2 (TorusSite L) → ℝ)
    (q y0 y1 y2 : ℝ)
    (hodds : ∀ e : (triangularTorusGraph L).edgeSet,
      pf e.1 = (1 - pf e.1) * triangularTorusSweepEdgeOdds L y0 y1 y2 e)
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet) :
    activeWeight (triangularTorusGraph L) pf q omega =
      (∏ e : (triangularTorusGraph L).edgeSet, (1 - pf e.1)) *
        (triHexTorusSectorClusterWeight L q
            (fun z => triangleFKLocalConnectivity
              (triangularTorusActiveConfigEquiv L omega z)) *
          ∏ z, triangleFKLocalOddsWeight y0 y1 y2
            (triangularTorusActiveConfigEquiv L omega z)) := by
  unfold activeWeight fkWeightW triHexTorusSectorClusterWeight
  rw [edgeProductW_extendActive_odds_factor _ _ _ hodds,
    triangularTorus_numClusters_eq_terminalSector,
    ← triangularTorus_localOddsProduct_eq_activeOddsProduct]
  unfold triangularTorusTerminalSectorGraph
  ring



theorem hexagonalTorus_activeWeight_eq_closedProduct_mul_cellWeight
    (L : ℕ) [Fact (2 < L)] (pf : Sym2 (HexTorusVertex L) → ℝ)
    (q y0 y1 y2 : ℝ)
    (hodds : ∀ e : (hexagonalTorusGraph L).edgeSet,
      pf e.1 = (1 - pf e.1) * hexagonalTorusSweepEdgeOdds L y0 y1 y2 e)
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) :
    activeWeight (hexagonalTorusGraph L) pf q omega =
      (∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pf e.1)) *
        (triHexTorusSectorClusterWeight L q
            (fun z => starFKLocalConnectivity
              (hexagonalTorusActiveConfigEquiv L omega z)) *
          ∏ z, starFKLocalOddsWeight q y0 y1 y2
            (hexagonalTorusActiveConfigEquiv L omega z)) := by
  unfold activeWeight fkWeightW triHexTorusSectorClusterWeight
  rw [edgeProductW_extendActive_odds_factor _ _ _ hodds,
    hexagonalTorus_numClusters_eq_terminalSector_add_isolated,
    pow_add, ← hexagonalTorus_isolatedCenterFactor_product,
    hexagonalTorus_localOddsProduct_eq_activeOddsProduct]
  unfold hexagonalTorusTerminalSectorGraph
  ring



theorem triangularTorus_activeZ_eq_closedProduct_mul_globalConfigSum
    (L : ℕ) [Fact (2 < L)] (pf : Sym2 (TorusSite L) → ℝ)
    (q y0 y1 y2 : ℝ)
    (hodds : ∀ e : (triangularTorusGraph L).edgeSet,
      pf e.1 = (1 - pf e.1) * triangularTorusSweepEdgeOdds L y0 y1 y2 e) :
    activeZ (triangularTorusGraph L) pf q =
      (∏ e : (triangularTorusGraph L).edgeSet, (1 - pf e.1)) *
        triangleFKGlobalConfigSum y0 y1 y2
          (triHexTorusSectorClusterWeight L q) := by
  classical
  unfold activeZ triangleFKGlobalConfigSum
  rw [← (triangularTorusActiveConfigEquiv L).symm.sum_comp
    (fun omega => activeWeight (triangularTorusGraph L) pf q omega)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro config _
  rw [triangularTorus_activeWeight_eq_closedProduct_mul_cellWeight
    L pf q y0 y1 y2 hodds]
  rw [(triangularTorusActiveConfigEquiv L).apply_symm_apply config]



theorem hexagonalTorus_activeZ_eq_closedProduct_mul_globalConfigSum
    (L : ℕ) [Fact (2 < L)] (pf : Sym2 (HexTorusVertex L) → ℝ)
    (q y0 y1 y2 : ℝ)
    (hodds : ∀ e : (hexagonalTorusGraph L).edgeSet,
      pf e.1 = (1 - pf e.1) * hexagonalTorusSweepEdgeOdds L y0 y1 y2 e) :
    activeZ (hexagonalTorusGraph L) pf q =
      (∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pf e.1)) *
        starFKGlobalConfigSum q y0 y1 y2
          (triHexTorusSectorClusterWeight L q) := by
  classical
  unfold activeZ starFKGlobalConfigSum
  rw [← (hexagonalTorusActiveConfigEquiv L).symm.sum_comp
    (fun omega => activeWeight (hexagonalTorusGraph L) pf q omega)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro config _
  rw [hexagonalTorus_activeWeight_eq_closedProduct_mul_cellWeight
    L pf q y0 y1 y2 hodds]
  rw [(hexagonalTorusActiveConfigEquiv L).apply_symm_apply config]



theorem triHexFK_globalConfigSum_identity
    {I : Type*} [Fintype I] [DecidableEq I]
    {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0)
    (external : (I → ThreeTerminalConnectivity) → ℝ) :
    (y0 * y1 * y2) ^ Fintype.card I *
        starFKGlobalConfigSum q y0Star y1Star y2Star external =
      (q ^ 2) ^ Fintype.card I *
        triangleFKGlobalConfigSum y0 y1 y2 external := by
  rw [starFKGlobalConfigSum_eq_sweepSum,
    triangleFKGlobalConfigSum_eq_sweepSum]
  exact triHexFK_globalSweepSum_identity h0 h1 h2 hsurface external





theorem triHexFK_torus_activeZ_identity
    (L : ℕ) [Fact (2 < L)]
    (pfTri : Sym2 (TorusSite L) → ℝ)
    (pfStar : Sym2 (HexTorusVertex L) → ℝ)
    {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
    (hoddsTri : ∀ e : (triangularTorusGraph L).edgeSet,
      pfTri e.1 = (1 - pfTri e.1) *
        triangularTorusSweepEdgeOdds L y0 y1 y2 e)
    (hoddsStar : ∀ e : (hexagonalTorusGraph L).edgeSet,
      pfStar e.1 = (1 - pfStar e.1) *
        hexagonalTorusSweepEdgeOdds L y0Star y1Star y2Star e)
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0) :
    (y0 * y1 * y2) ^ Fintype.card (TorusSite L) *
        (∏ e : (triangularTorusGraph L).edgeSet, (1 - pfTri e.1)) *
          activeZ (hexagonalTorusGraph L) pfStar q =
      (q ^ 2) ^ Fintype.card (TorusSite L) *
        (∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pfStar e.1)) *
          activeZ (triangularTorusGraph L) pfTri q := by
  rw [triangularTorus_activeZ_eq_closedProduct_mul_globalConfigSum
      L pfTri q y0 y1 y2 hoddsTri,
    hexagonalTorus_activeZ_eq_closedProduct_mul_globalConfigSum
      L pfStar q y0Star y1Star y2Star hoddsStar]
  have hglobal := triHexFK_globalConfigSum_identity
    (I := TorusSite L) h0 h1 h2 hsurface (triHexTorusSectorClusterWeight L q)
  calc
    (y0 * y1 * y2) ^ Fintype.card (TorusSite L) *
        (∏ e : (triangularTorusGraph L).edgeSet, (1 - pfTri e.1)) *
        ((∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pfStar e.1)) *
          starFKGlobalConfigSum q y0Star y1Star y2Star
            (triHexTorusSectorClusterWeight L q)) =
      ((∏ e : (triangularTorusGraph L).edgeSet, (1 - pfTri e.1)) *
        (∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pfStar e.1))) *
          ((y0 * y1 * y2) ^ Fintype.card (TorusSite L) *
            starFKGlobalConfigSum q y0Star y1Star y2Star
              (triHexTorusSectorClusterWeight L q)) := by ring
    _ = ((∏ e : (triangularTorusGraph L).edgeSet, (1 - pfTri e.1)) *
        (∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pfStar e.1))) *
          ((q ^ 2) ^ Fintype.card (TorusSite L) *
            triangleFKGlobalConfigSum y0 y1 y2
              (triHexTorusSectorClusterWeight L q)) := by rw [hglobal]
    _ = (q ^ 2) ^ Fintype.card (TorusSite L) *
        (∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pfStar e.1)) *
          ((∏ e : (triangularTorusGraph L).edgeSet, (1 - pfTri e.1)) *
            triangleFKGlobalConfigSum y0 y1 y2
              (triHexTorusSectorClusterWeight L q)) := by ring



noncomputable def triangularTorusSectorObservable
    (L : ℕ) [Fact (2 < L)]
    (observable : (TorusSite L → ThreeTerminalConnectivity) → ℝ)
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet) : ℝ :=
  observable (fun z => triangleFKLocalConnectivity
    (triangularTorusActiveConfigEquiv L omega z))


noncomputable def hexagonalTorusSectorObservable
    (L : ℕ) [Fact (2 < L)]
    (observable : (TorusSite L → ThreeTerminalConnectivity) → ℝ)
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) : ℝ :=
  observable (fun z => starFKLocalConnectivity
    (hexagonalTorusActiveConfigEquiv L omega z))



theorem triangularTorus_activeNumer_sector_eq
    (L : ℕ) [Fact (2 < L)] (pf : Sym2 (TorusSite L) → ℝ)
    (q y0 y1 y2 : ℝ)
    (hodds : ∀ e : (triangularTorusGraph L).edgeSet,
      pf e.1 = (1 - pf e.1) * triangularTorusSweepEdgeOdds L y0 y1 y2 e)
    (observable : (TorusSite L → ThreeTerminalConnectivity) → ℝ) :
    activeNumer (triangularTorusGraph L) pf q
        (triangularTorusSectorObservable L observable) =
      (∏ e : (triangularTorusGraph L).edgeSet, (1 - pf e.1)) *
        triangleFKGlobalConfigSum y0 y1 y2
          (fun sector => triHexTorusSectorClusterWeight L q sector *
            observable sector) := by
  classical
  unfold activeNumer triangleFKGlobalConfigSum triangularTorusSectorObservable
  rw [← (triangularTorusActiveConfigEquiv L).symm.sum_comp
    (fun omega => observable (fun z => triangleFKLocalConnectivity
      (triangularTorusActiveConfigEquiv L omega z)) *
        activeWeight (triangularTorusGraph L) pf q omega)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro config _
  rw [triangularTorus_activeWeight_eq_closedProduct_mul_cellWeight
    L pf q y0 y1 y2 hodds]
  rw [(triangularTorusActiveConfigEquiv L).apply_symm_apply config]
  ring


theorem hexagonalTorus_activeNumer_sector_eq
    (L : ℕ) [Fact (2 < L)] (pf : Sym2 (HexTorusVertex L) → ℝ)
    (q y0 y1 y2 : ℝ)
    (hodds : ∀ e : (hexagonalTorusGraph L).edgeSet,
      pf e.1 = (1 - pf e.1) * hexagonalTorusSweepEdgeOdds L y0 y1 y2 e)
    (observable : (TorusSite L → ThreeTerminalConnectivity) → ℝ) :
    activeNumer (hexagonalTorusGraph L) pf q
        (hexagonalTorusSectorObservable L observable) =
      (∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pf e.1)) *
        starFKGlobalConfigSum q y0 y1 y2
          (fun sector => triHexTorusSectorClusterWeight L q sector *
            observable sector) := by
  classical
  unfold activeNumer starFKGlobalConfigSum hexagonalTorusSectorObservable
  rw [← (hexagonalTorusActiveConfigEquiv L).symm.sum_comp
    (fun omega => observable (fun z => starFKLocalConnectivity
      (hexagonalTorusActiveConfigEquiv L omega z)) *
        activeWeight (hexagonalTorusGraph L) pf q omega)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro config _
  rw [hexagonalTorus_activeWeight_eq_closedProduct_mul_cellWeight
    L pf q y0 y1 y2 hodds]
  rw [(hexagonalTorusActiveConfigEquiv L).apply_symm_apply config]
  ring



theorem triHexFK_torus_activeSectorRatio_eq
    (L : ℕ) [Fact (2 < L)]
    (pfTri : Sym2 (TorusSite L) → ℝ)
    (pfStar : Sym2 (HexTorusVertex L) → ℝ)
    {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
    (hq : q ≠ 0) (hyprod : y0 * y1 * y2 ≠ 0)
    (hpfTri : ∀ e : (triangularTorusGraph L).edgeSet, pfTri e.1 ≠ 1)
    (hpfStar : ∀ e : (hexagonalTorusGraph L).edgeSet, pfStar e.1 ≠ 1)
    (hoddsTri : ∀ e : (triangularTorusGraph L).edgeSet,
      pfTri e.1 = (1 - pfTri e.1) *
        triangularTorusSweepEdgeOdds L y0 y1 y2 e)
    (hoddsStar : ∀ e : (hexagonalTorusGraph L).edgeSet,
      pfStar e.1 = (1 - pfStar e.1) *
        hexagonalTorusSweepEdgeOdds L y0Star y1Star y2Star e)
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0)
    (observable : (TorusSite L → ThreeTerminalConnectivity) → ℝ) :
    activeNumer (hexagonalTorusGraph L) pfStar q
        (hexagonalTorusSectorObservable L observable) /
        activeZ (hexagonalTorusGraph L) pfStar q =
      activeNumer (triangularTorusGraph L) pfTri q
        (triangularTorusSectorObservable L observable) /
        activeZ (triangularTorusGraph L) pfTri q := by
  have hclosedTri :
      (∏ e : (triangularTorusGraph L).edgeSet, (1 - pfTri e.1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro e _
    exact sub_ne_zero.mpr (Ne.symm (hpfTri e))
  have hclosedStar :
      (∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pfStar e.1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro e _
    exact sub_ne_zero.mpr (Ne.symm (hpfStar e))
  rw [hexagonalTorus_activeNumer_sector_eq L pfStar q y0Star y1Star y2Star
      hoddsStar observable,
    hexagonalTorus_activeZ_eq_closedProduct_mul_globalConfigSum
      L pfStar q y0Star y1Star y2Star hoddsStar,
    triangularTorus_activeNumer_sector_eq L pfTri q y0 y1 y2 hoddsTri observable,
    triangularTorus_activeZ_eq_closedProduct_mul_globalConfigSum
      L pfTri q y0 y1 y2 hoddsTri]
  rw [mul_div_mul_left _ _ hclosedStar, mul_div_mul_left _ _ hclosedTri]
  rw [starFKGlobalConfigSum_eq_sweepSum,
    starFKGlobalConfigSum_eq_sweepSum,
    triangleFKGlobalConfigSum_eq_sweepSum,
    triangleFKGlobalConfigSum_eq_sweepSum]
  exact triHexFK_globalSweepRatio_eq hq hyprod h0 h1 h2 hsurface
    (triHexTorusSectorClusterWeight L q) observable


noncomputable def triangularTorusActiveTwoPointIndicator
    (L : ℕ) [Fact (2 < L)] (x y : TorusSite L)
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet) : ℝ :=
  if (openSub (triangularTorusGraph L)
    (extendActive (triangularTorusGraph L) omega)).Reachable x y then 1 else 0



noncomputable def hexagonalTorusActiveWhiteTwoPointIndicator
    (L : ℕ) [Fact (2 < L)] (x y : TorusSite L)
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) : ℝ :=
  if (openSub (hexagonalTorusGraph L)
    (extendActive (hexagonalTorusGraph L) omega)).Reachable
      (x, true) (y, true) then 1 else 0

theorem triangularTorusSectorTwoPointObservable_eq_indicator
    (L : ℕ) [Fact (2 < L)] (x y : TorusSite L)
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet) :
    triangularTorusSectorObservable L
        (triHexFKTerminalTwoPointObservable (triHexTorusCellTerminal L) x y) omega =
      triangularTorusActiveTwoPointIndicator L x y omega := by
  classical
  unfold triangularTorusSectorObservable triHexFKTerminalTwoPointObservable
    triangularTorusActiveTwoPointIndicator
  change (if (triangularTorusTerminalSectorGraph L omega).Reachable x y then
      (1 : ℝ) else 0) =
    if (openSub (triangularTorusGraph L)
      (extendActive (triangularTorusGraph L) omega)).Reachable x y then 1 else 0
  have hiff := triangularTorus_openSub_reachable_iff_terminalSectorGraph
    L omega x y
  by_cases h : (openSub (triangularTorusGraph L)
      (extendActive (triangularTorusGraph L) omega)).Reachable x y
  · have hs := hiff.mp h
    simp [h, hs]
  · have hs : ¬ (triangularTorusTerminalSectorGraph L omega).Reachable x y :=
      fun hs => h (hiff.mpr hs)
    simp [h, hs]

theorem hexagonalTorusSectorTwoPointObservable_eq_indicator
    (L : ℕ) [Fact (2 < L)] (x y : TorusSite L)
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) :
    hexagonalTorusSectorObservable L
        (triHexFKTerminalTwoPointObservable (triHexTorusCellTerminal L) x y) omega =
      hexagonalTorusActiveWhiteTwoPointIndicator L x y omega := by
  classical
  unfold hexagonalTorusSectorObservable triHexFKTerminalTwoPointObservable
    hexagonalTorusActiveWhiteTwoPointIndicator
  change (if (hexagonalTorusTerminalSectorGraph L omega).Reachable x y then
      (1 : ℝ) else 0) =
    if (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Reachable
        (x, true) (y, true) then 1 else 0
  have hiff := hexagonalTorus_openSub_white_reachable_iff_terminalSectorGraph
    L omega x y
  by_cases h : (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Reachable (x, true) (y, true)
  · have hs := hiff.mp h
    simp [h, hs]
  · have hs : ¬ (hexagonalTorusTerminalSectorGraph L omega).Reachable x y :=
      fun hs => h (hiff.mpr hs)
    simp [h, hs]



theorem triHexFK_torus_activeTwoPointRatio_eq
    (L : ℕ) [Fact (2 < L)]
    (pfTri : Sym2 (TorusSite L) → ℝ)
    (pfStar : Sym2 (HexTorusVertex L) → ℝ)
    {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
    (hq : q ≠ 0) (hyprod : y0 * y1 * y2 ≠ 0)
    (hpfTri : ∀ e : (triangularTorusGraph L).edgeSet, pfTri e.1 ≠ 1)
    (hpfStar : ∀ e : (hexagonalTorusGraph L).edgeSet, pfStar e.1 ≠ 1)
    (hoddsTri : ∀ e : (triangularTorusGraph L).edgeSet,
      pfTri e.1 = (1 - pfTri e.1) *
        triangularTorusSweepEdgeOdds L y0 y1 y2 e)
    (hoddsStar : ∀ e : (hexagonalTorusGraph L).edgeSet,
      pfStar e.1 = (1 - pfStar e.1) *
        hexagonalTorusSweepEdgeOdds L y0Star y1Star y2Star e)
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0)
    (x y : TorusSite L) :
    activeNumer (hexagonalTorusGraph L) pfStar q
        (hexagonalTorusActiveWhiteTwoPointIndicator L x y) /
        activeZ (hexagonalTorusGraph L) pfStar q =
      activeNumer (triangularTorusGraph L) pfTri q
        (triangularTorusActiveTwoPointIndicator L x y) /
        activeZ (triangularTorusGraph L) pfTri q := by
  have hratio := triHexFK_torus_activeSectorRatio_eq L pfTri pfStar
    hq hyprod hpfTri hpfStar hoddsTri hoddsStar h0 h1 h2 hsurface
    (triHexFKTerminalTwoPointObservable (triHexTorusCellTerminal L) x y)
  have htri : triangularTorusSectorObservable L
      (triHexFKTerminalTwoPointObservable (triHexTorusCellTerminal L) x y) =
        triangularTorusActiveTwoPointIndicator L x y := by
    funext omega
    exact triangularTorusSectorTwoPointObservable_eq_indicator L x y omega
  have hstar : hexagonalTorusSectorObservable L
      (triHexFKTerminalTwoPointObservable (triHexTorusCellTerminal L) x y) =
        hexagonalTorusActiveWhiteTwoPointIndicator L x y := by
    funext omega
    exact hexagonalTorusSectorTwoPointObservable_eq_indicator L x y omega
  simpa [htri, hstar] using hratio

end StatMech.FK.PeriodicPlanar
