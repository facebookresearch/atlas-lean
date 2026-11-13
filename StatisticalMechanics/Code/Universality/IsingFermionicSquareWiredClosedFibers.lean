/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.IsingFermionicSquareWiredEndpoints

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

private theorem fkIsingSquareNextDirection_reaches
    (n : Nat) (hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V)
    (d e : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    (he : fkIsingSquareDirectionAvailable n u e) :
    ∃ k : Nat, k ≤ 3 ∧
      (fkIsingSquareNextDirection n u)^[k] d = e := by
  by_cases hE : fkIsingSquareDirectionAvailable n u .east <;>
    by_cases hN : fkIsingSquareDirectionAvailable n u .north <;>
    by_cases hW : fkIsingSquareDirectionAvailable n u .west <;>
    by_cases hS : fkIsingSquareDirectionAvailable n u .south
  all_goals
    let f := fkIsingSquareNextDirection n u
    have hor : d = e ∨ f d = e ∨ f (f d) = e ∨ f (f (f d)) = e := by
      cases d <;> cases e <;> simp_all [f, fkIsingSquareNextDirection]
    rcases hor with h | h | h | h
    · exact ⟨0, by decide, h⟩
    · exact ⟨1, by decide, h⟩
    · exact ⟨2, by decide, by simpa [f, Function.iterate_succ_apply] using h⟩
    · exact ⟨3, by decide, by simpa [f, Function.iterate_succ_apply] using h⟩

private theorem fkIsingSquareWiredBondMate_eq_of_not_wired
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hd : ¬ fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n d)) :
    fkIsingSquareWiredBondMate n hn d = fkIsingSquareBondMate n hn d := by
  classical
  let sigma := fkIsingSquareWiredShiftDartEquiv n hn
  have hfix : sigma d = d := by
    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
    intro hrange
    obtain ⟨i, rfl⟩ := hrange
    exact hd (fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i)
  have hfix' : sigma.symm d = d := by
    calc
      sigma.symm d = sigma.symm (sigma d) := congrArg sigma.symm hfix.symm
      _ = d := sigma.symm_apply_apply d
  simp only [fkIsingSquareWiredBondMate,
    fkIsingSquareWiredBondMateEquiv, Equiv.Perm.mul_apply]
  rw [show (fkIsingSquareWiredShiftDartEquiv n hn).symm d = d by exact hfix']
  have hBnot : ¬ fkIsingSquareWiredArc n
      (fkIsingSquareDartEndpoint n (fkIsingSquareBondMate n hn d)) := by
    simpa using hd
  have hBfix : sigma (fkIsingSquareBondMate n hn d) =
      fkIsingSquareBondMate n hn d := by
    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
    intro hrange
    obtain ⟨i, hi⟩ := hrange
    apply hBnot
    rw [← hi]
    exact fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  exact hBfix

private theorem fkIsingSquareWiredBondMate_eq_of_notMem
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hd : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn))
    (hBd : fkIsingSquareBondMate n hn d ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    fkIsingSquareWiredBondMate n hn d = fkIsingSquareBondMate n hn d := by
  let sigma := fkIsingSquareWiredShiftDartEquiv n hn
  have hfix : sigma d = d := by
    exact Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hd
  have hfix' : sigma.symm d = d := by
    calc
      sigma.symm d = sigma.symm (sigma d) := congrArg sigma.symm hfix.symm
      _ = d := sigma.symm_apply_apply d
  have hBfix : sigma (fkIsingSquareBondMate n hn d) =
      fkIsingSquareBondMate n hn d := by
    exact Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hBd
  simp only [fkIsingSquareWiredBondMate,
    fkIsingSquareWiredBondMateEquiv, Equiv.Perm.mul_apply]
  rw [show (fkIsingSquareWiredShiftDartEquiv n hn).symm d = d by exact hfix']
  exact hBfix

private theorem fkIsingSquareWiredBondMate_bottom_east_counterclockwise
    (n : Nat) (hn : 0 < n) :
    let hE := fkIsingSquareMarkedA_east_available n hn
    let hN : fkIsingSquareDirectionAvailable n
        (fkIsingSquareMarkedA n) .north := by
      simp [fkIsingSquareDirectionAvailable, fkIsingSquareMarkedA]
      omega
    fkIsingSquareWiredBondMate n hn
        (fkIsingSquareDirectionDart n (fkIsingSquareMarkedA n) .east hE
          .counterclockwise) =
      fkIsingSquareDirectionDart n (fkIsingSquareMarkedA n) .north hN
        .clockwise := by
  dsimp only
  have hx : fkIsingSquareDirectionDart n (fkIsingSquareMarkedA n) .east
      (fkIsingSquareMarkedA_east_available n hn) .counterclockwise ∉
        Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
    rintro ⟨i, hi⟩
    have hkey := congrArg (fun d : FKIsingMedialDart (fkSquareBoxPlanar n) =>
        (fkIsingSquareDartEndpoint n d, fkIsingSquareDartDirection n d,
          (fkIsingSquareSideCorner d.2).2)) hi
    cases i <;>
      simp [fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart] at hkey
    have hcoord := congrArg (fun u : (fkSquareBoxPlanar n).V => u.1 1) hkey
    simp [fkIsingSquareMarkedA, fkIsingSquareMarkedB] at hcoord
    omega
  have hBx : fkIsingSquareBondMate n hn
      (fkIsingSquareDirectionDart n (fkIsingSquareMarkedA n) .east
        (fkIsingSquareMarkedA_east_available n hn) .counterclockwise) ∉
        Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
    simp only [fkIsingSquareBondMate,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    rintro ⟨i, hi⟩
    have hkey := congrArg (fun d : FKIsingMedialDart (fkSquareBoxPlanar n) =>
        (fkIsingSquareDartEndpoint n d, fkIsingSquareDartDirection n d,
          (fkIsingSquareSideCorner d.2).2)) hi
    cases i <;>
      simp [fkIsingSquareNextDirection,
        fkIsingSquareDirectionAvailable, fkIsingSquareMarkedA,
        fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart, hn] at hkey
  rw [fkIsingSquareWiredBondMate_eq_of_notMem n hn _ hx hBx]
  simp [fkIsingSquareBondMate, fkIsingSquareNextDirection,
    fkIsingSquareDirectionAvailable, fkIsingSquareMarkedA, hn]

private theorem fkIsingSquareWiredBondMate_upper_south_counterclockwise
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    let u := fkIsingSquareLeftVerticalUpper n hn k
    let hS := fkIsingSquareLeftVerticalUpper_south_available n hn k
    let hE : fkIsingSquareDirectionAvailable n u .east := by
      simp [u, fkIsingSquareDirectionAvailable,
        fkIsingSquareLeftVerticalUpper]
      omega
    fkIsingSquareWiredBondMate n hn
        (fkIsingSquareDirectionDart n u .south hS .counterclockwise) =
      fkIsingSquareDirectionDart n u .east hE .clockwise := by
  dsimp only
  have hx : fkIsingSquareDirectionDart n
      (fkIsingSquareLeftVerticalUpper n hn k) .south
      (fkIsingSquareLeftVerticalUpper_south_available n hn k)
      .counterclockwise ∉
        Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
    rintro ⟨i, hi⟩
    have hkey := congrArg (fun d : FKIsingMedialDart (fkSquareBoxPlanar n) =>
        (fkIsingSquareDartEndpoint n d, fkIsingSquareDartDirection n d,
          (fkIsingSquareSideCorner d.2).2)) hi
    cases i <;>
      simp [fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart] at hkey
  have hBx : fkIsingSquareBondMate n hn
      (fkIsingSquareDirectionDart n
        (fkIsingSquareLeftVerticalUpper n hn k) .south
        (fkIsingSquareLeftVerticalUpper_south_available n hn k)
        .counterclockwise) ∉
        Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
    simp only [fkIsingSquareBondMate,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    rintro ⟨i, hi⟩
    have hkey := congrArg (fun d : FKIsingMedialDart (fkSquareBoxPlanar n) =>
        (fkIsingSquareDartEndpoint n d, fkIsingSquareDartDirection n d,
          (fkIsingSquareSideCorner d.2).2)) hi
    cases i <;>
      simp [fkIsingSquareNextDirection,
        fkIsingSquareDirectionAvailable,
        fkIsingSquareLeftVerticalUpper,
        fkIsingSquareMarkedA, fkIsingSquareMarkedB,
        fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart, hn] at hkey
    have hcoord := congrArg (fun u : (fkSquareBoxPlanar n).V => u.1 1) hkey
    simp at hcoord
    omega
  rw [fkIsingSquareWiredBondMate_eq_of_notMem n hn _ hx hBx]
  simp [fkIsingSquareBondMate, fkIsingSquareNextDirection,
    fkIsingSquareDirectionAvailable, fkIsingSquareLeftVerticalUpper, hn]

private theorem fkIsingSquareWiredBondMate_upper_east_counterclockwise
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n))
    (hk : k.val + 1 < 2 * n) :
    let u := fkIsingSquareLeftVerticalUpper n hn k
    let hE : fkIsingSquareDirectionAvailable n u .east := by
      simp [u, fkIsingSquareDirectionAvailable,
        fkIsingSquareLeftVerticalUpper]
      omega
    let hN : fkIsingSquareDirectionAvailable n u .north := by
      simp [u, fkIsingSquareDirectionAvailable,
        fkIsingSquareLeftVerticalUpper]
      omega
    fkIsingSquareWiredBondMate n hn
        (fkIsingSquareDirectionDart n u .east hE .counterclockwise) =
      fkIsingSquareDirectionDart n u .north hN .clockwise := by
  dsimp only
  have hnorth : -(n : Int) + (k.val : Int) + 1 < (n : Int) := by
    have hk' : (k.val : Int) + 1 < 2 * (n : Int) := by exact_mod_cast hk
    omega
  have hx : fkIsingSquareDirectionDart n
      (fkIsingSquareLeftVerticalUpper n hn k) .east
      (by simp [fkIsingSquareDirectionAvailable,
        fkIsingSquareLeftVerticalUpper]; omega) .counterclockwise ∉
        Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
    rintro ⟨i, hi⟩
    have hkey := congrArg (fun d : FKIsingMedialDart (fkSquareBoxPlanar n) =>
        (fkIsingSquareDartEndpoint n d, fkIsingSquareDartDirection n d,
          (fkIsingSquareSideCorner d.2).2)) hi
    cases i <;>
      simp [fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart] at hkey
    have hcoord := congrArg (fun u : (fkSquareBoxPlanar n).V => u.1 1) hkey
    simp [fkIsingSquareLeftVerticalUpper, fkIsingSquareMarkedB] at hcoord
    omega
  have hBx : fkIsingSquareBondMate n hn
      (fkIsingSquareDirectionDart n
        (fkIsingSquareLeftVerticalUpper n hn k) .east
        (by simp [fkIsingSquareDirectionAvailable,
          fkIsingSquareLeftVerticalUpper]; omega) .counterclockwise) ∉
        Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
    simp only [fkIsingSquareBondMate,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    rintro ⟨i, hi⟩
    have hkey := congrArg (fun d : FKIsingMedialDart (fkSquareBoxPlanar n) =>
        (fkIsingSquareDartEndpoint n d, fkIsingSquareDartDirection n d,
          (fkIsingSquareSideCorner d.2).2)) hi
    cases i <;>
      simp [fkIsingSquareNextDirection,
        fkIsingSquareDirectionAvailable,
        fkIsingSquareLeftVerticalUpper,
        fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart, hnorth] at hkey
  rw [fkIsingSquareWiredBondMate_eq_of_notMem n hn _ hx hBx]
  simp [fkIsingSquareBondMate, fkIsingSquareNextDirection,
    fkIsingSquareDirectionAvailable, fkIsingSquareLeftVerticalUpper, hnorth]

private theorem fkIsingSquareWiredCompleted_bond_reachable_mate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
      (.bond d) (.bond (fkIsingSquareWiredBondMate n hn d)) := by
  let G := fkIsingSquareWiredCompletedLoopGraph n hn omega
  let a := fkIsingSquareWiredSourceDart n hn
  let b := fkIsingSquareWiredTerminalDart n hn
  by_cases ha : d = a
  · subst d
    have hab : fkIsingSquareWiredBondMate n hn a = b := by
      simpa [a, b, fkIsingSquareWiredSourceDart,
        fkIsingSquareWiredTerminalDart] using
          fkIsingSquareWiredBondMate_bottom n hn
    rw [hab]
    apply (show G.Adj (.bond a) .source by
      left; right; simp [fkIsingSquareWiredTransitionMate, a]) |>.reachable.trans
    apply (show G.Adj .source .terminal by
      right; simp [G, fkIsingSquareWiredCompletedLoopGraph,
        SimpleGraph.edge_adj]) |>.reachable.trans
    exact (show G.Adj .terminal (.bond b) by
      left; right; simp [fkIsingSquareWiredTransitionMate, b]).reachable
  by_cases hb : d = b
  · subst d
    have hba : fkIsingSquareWiredBondMate n hn b = a := by
      simpa [a, b, fkIsingSquareWiredSourceDart,
        fkIsingSquareWiredTerminalDart] using
          fkIsingSquareWiredBondMate_top n hn
    rw [hba]
    apply (show G.Adj (.bond b) .terminal by
      left; right; simp [fkIsingSquareWiredTransitionMate, a, b,
        fkIsingSquareWiredSourceDart_ne_terminalDart n hn |>.symm]) |>.reachable.trans
    apply (show G.Adj .terminal .source by
      right; simp [G, fkIsingSquareWiredCompletedLoopGraph,
        SimpleGraph.edge_adj]) |>.reachable.trans
    exact (show G.Adj .source (.bond a) by
      left; right; simp [fkIsingSquareWiredTransitionMate, a]).reachable
  · exact (show G.Adj (.bond d)
        (.bond (fkIsingSquareWiredBondMate n hn d)) by
      have ha' : d ≠ fkIsingSquareWiredSourceDart n hn := by simpa [a] using ha
      have hb' : d ≠ fkIsingSquareWiredTerminalDart n hn := by simpa [b] using hb
      left; right
      simp [fkIsingSquareWiredTransitionMate, ha', hb']).reachable

private theorem fkIsingSquareWiredCompleted_incidence_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
      (.dart d) (.bond d) := by
  exact (show (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj
      (.dart d) (.bond d) by
    left; left
    simp [fkIsingSquareWiredLoopGraph,
      fkIsingSquareWiredIncidenceMate]).reachable

private theorem fkIsingSquareWiredCompleted_closed_local_turn_reachable
    (n : Nat) (hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
      (.dart (fkIsingSquareDirectionDart n u d hd .counterclockwise))
      (.dart (fkIsingSquareDirectionDart n u d hd .clockwise)) := by
  exact (show (fkIsingSquareWiredCompletedLoopGraph n hn
      (FK.edgeSetConfig ∅)).Adj
      (.dart (fkIsingSquareDirectionDart n u d hd .counterclockwise))
      (.dart (fkIsingSquareDirectionDart n u d hd .clockwise)) by
    left; right
    cases d <;>
      simp [fkIsingSquareWiredTransitionMate,
        FKIsingMedialDart.localMate, FK.edgeSetConfig,
        fkIsingSquareDirectionDart, fkIsingSquareCornerSide,
        fkIsingSquareEndpointForDirection]).reachable

private theorem fkIsingSquareWiredCompleted_closed_next_reachable_of_not_wired
    (n : Nat) (hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V)
    (hu : ¬ fkIsingSquareWiredArc n u)
    (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    let e := fkIsingSquareNextDirection n u d
    let he := fkIsingSquareNextDirection_available n hn u d hd
    (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
      (.dart (fkIsingSquareDirectionDart n u d hd .counterclockwise))
      (.dart (fkIsingSquareDirectionDart n u e he .counterclockwise)) := by
  dsimp only
  let x := fkIsingSquareDirectionDart n u d hd .counterclockwise
  let e := fkIsingSquareNextDirection n u d
  let he := fkIsingSquareNextDirection_available n hn u d hd
  let y := fkIsingSquareDirectionDart n u e he .clockwise
  have hxendpoint : fkIsingSquareDartEndpoint n x = u := by simp [x]
  have hB : fkIsingSquareWiredBondMate n hn x = y := by
    rw [fkIsingSquareWiredBondMate_eq_of_not_wired n hn x
      (by simpa [hxendpoint])]
    simp [x, y, e, he, fkIsingSquareBondMate]
  have h1 := fkIsingSquareWiredCompleted_incidence_reachable
    n hn (FK.edgeSetConfig ∅) x
  have h2 := fkIsingSquareWiredCompleted_bond_reachable_mate
    n hn (FK.edgeSetConfig ∅) x
  have h3 := fkIsingSquareWiredCompleted_incidence_reachable
    n hn (FK.edgeSetConfig ∅)
    (fkIsingSquareWiredBondMate n hn x)
  have h4 := fkIsingSquareWiredCompleted_closed_local_turn_reachable n hn u e he
  rw [hB] at h2 h3
  exact h1.trans (h2.trans (h3.symm.trans (by simpa [y] using h4.symm)))

private theorem fkIsingSquareWiredCompleted_closed_directions_reachable_of_not_wired
    (n : Nat) (hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V)
    (hu : ¬ fkIsingSquareWiredArc n u)
    (d e : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    (he : fkIsingSquareDirectionAvailable n u e) :
    (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
      (.dart (fkIsingSquareDirectionDart n u d hd .counterclockwise))
      (.dart (fkIsingSquareDirectionDart n u e he .counterclockwise)) := by
  obtain ⟨k, hk, hiter⟩ := fkIsingSquareNextDirection_reaches n hn u d e hd he
  interval_cases k
  · have hde : d = e := by simpa using hiter
    subst e
    simpa using SimpleGraph.Reachable.refl
      (G := fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅))
      (.dart (fkIsingSquareDirectionDart n u d hd .counterclockwise))
  · have h1 := fkIsingSquareWiredCompleted_closed_next_reachable_of_not_wired
      n hn u hu d hd
    simpa [Function.iterate_succ_apply] using hiter ▸ h1
  · let d1 := fkIsingSquareNextDirection n u d
    let hd1 := fkIsingSquareNextDirection_available n hn u d hd
    have h1 := fkIsingSquareWiredCompleted_closed_next_reachable_of_not_wired
      n hn u hu d hd
    have h2 := fkIsingSquareWiredCompleted_closed_next_reachable_of_not_wired
      n hn u hu d1 hd1
    have h12 := h1.trans h2
    simpa [d1, hd1, Function.iterate_succ_apply] using hiter ▸ h12
  · let d1 := fkIsingSquareNextDirection n u d
    let hd1 := fkIsingSquareNextDirection_available n hn u d hd
    let d2 := fkIsingSquareNextDirection n u d1
    let hd2 := fkIsingSquareNextDirection_available n hn u d1 hd1
    have h1 := fkIsingSquareWiredCompleted_closed_next_reachable_of_not_wired
      n hn u hu d hd
    have h2 := fkIsingSquareWiredCompleted_closed_next_reachable_of_not_wired
      n hn u hu d1 hd1
    have h3 := fkIsingSquareWiredCompleted_closed_next_reachable_of_not_wired
      n hn u hu d2 hd2
    have h123 := (h1.trans h2).trans h3
    simpa [d1, hd1, d2, hd2, Function.iterate_succ_apply] using hiter ▸ h123



theorem fkIsingSquareWiredCompleted_closed_darts_reachable_of_not_wired
    (n : Nat) (hn : 0 < n)
    (d f : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hlabel : fkIsingSquareDartEndpoint n d = fkIsingSquareDartEndpoint n f)
    (hnot : ¬ fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n d)) :
    (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
      (.dart d) (.dart f) := by
  let u := fkIsingSquareDartEndpoint n d
  let dd := fkIsingSquareDartDirection n d
  let df := fkIsingSquareDartDirection n f
  let hdd := fkIsingSquareDartDirection_available n d
  let hdf0 := fkIsingSquareDartDirection_available n f
  have hdf : fkIsingSquareDirectionAvailable n u df := by
    simpa only [u, df, hlabel] using hdf0
  have hdrec := fkIsingSquareDirectionDart_reconstruct n d
  have hfrec := fkIsingSquareDirectionDart_reconstruct n f
  have hdrecU : fkIsingSquareDirectionDart n u dd hdd
      (fkIsingSquareSideCorner d.2).2 = d := by
    simpa only [u, dd, hdd] using hdrec
  have hfrecU : fkIsingSquareDirectionDart n u df hdf
      (fkIsingSquareSideCorner f.2).2 = f := by
    simpa only [u, df, hlabel] using hfrec
  have hdirs := fkIsingSquareWiredCompleted_closed_directions_reachable_of_not_wired
    n hn u (by simpa only [u] using hnot) dd df hdd hdf
  have hlocalD := fkIsingSquareWiredCompleted_closed_local_turn_reachable
    n hn u dd hdd
  have hlocalF := fkIsingSquareWiredCompleted_closed_local_turn_reachable
    n hn u df hdf
  rw [← hdrecU, ← hfrecU]
  cases htd : (fkIsingSquareSideCorner d.2).2 <;>
    cases htf : (fkIsingSquareSideCorner f.2).2
  · simpa only [htd, htf] using hdirs
  · have h := hdirs.trans hlocalF
    simpa only [htd, htf] using h
  · have h := hlocalD.symm.trans hdirs
    simpa only [htd, htf] using h
  · have h := (hlocalD.symm.trans hdirs).trans hlocalF
    simpa only [htd, htf] using h



theorem fkIsingSquareWiredCompleted_reachable_dart_same_label
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n) :
    ∃ d : FKIsingMedialDart (fkSquareBoxPlanar n),
      (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable x (.dart d) ∧
      fkIsingSquareWiredCarrierPrimalLabel n hn x =
        fkIsingSquareDartEndpoint n d := by
  cases x with
  | dart d =>
      exact ⟨d, SimpleGraph.Reachable.refl _, rfl⟩
  | bond d =>
      exact ⟨d,
        (fkIsingSquareWiredCompleted_incidence_reachable
          n hn omega d).symm, rfl⟩
  | source =>
      let d := fkIsingSquareWiredSourceDart n hn
      have hsb : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj
          (.source : FKIsingSquareWiredCarrier n) (.bond d) := by
        left
        right
        simp [d, fkIsingSquareWiredTransitionMate]
      refine ⟨d, hsb.reachable.trans
        (fkIsingSquareWiredCompleted_incidence_reachable n hn omega d).symm,
        ?_⟩
      simp [d, fkIsingSquareWiredCarrierPrimalLabel,
        fkIsingSquareWiredSourceDart, fkIsingSquareWiredBoundaryDart]
  | terminal =>
      let d := fkIsingSquareWiredTerminalDart n hn
      have htb : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj
          (.terminal : FKIsingSquareWiredCarrier n) (.bond d) := by
        left
        right
        simp [d, fkIsingSquareWiredTransitionMate]
      refine ⟨d, htb.reachable.trans
        (fkIsingSquareWiredCompleted_incidence_reachable n hn omega d).symm,
        ?_⟩
      simp [d, fkIsingSquareWiredCarrierPrimalLabel,
        fkIsingSquareWiredTerminalDart, fkIsingSquareWiredBoundaryDart]



theorem fkIsingSquareWiredCompleted_closed_reachable_of_label_eq_not_wired
    (n : Nat) (hn : 0 < n)
    (x y : FKIsingSquareWiredCarrier n)
    (hlabel : fkIsingSquareWiredCarrierPrimalLabel n hn x =
      fkIsingSquareWiredCarrierPrimalLabel n hn y)
    (hnot : ¬ fkIsingSquareWiredArc n
      (fkIsingSquareWiredCarrierPrimalLabel n hn x)) :
    (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
      x y := by
  obtain ⟨d, hxd, hdx⟩ :=
    fkIsingSquareWiredCompleted_reachable_dart_same_label
      n hn (FK.edgeSetConfig ∅) x
  obtain ⟨f, hyf, hfy⟩ :=
    fkIsingSquareWiredCompleted_reachable_dart_same_label
      n hn (FK.edgeSetConfig ∅) y
  have hdf : fkIsingSquareDartEndpoint n d =
      fkIsingSquareDartEndpoint n f := hdx.symm.trans (hlabel.trans hfy)
  have hdnot : ¬ fkIsingSquareWiredArc n
      (fkIsingSquareDartEndpoint n d) := by simpa only [← hdx] using hnot
  exact hxd.trans
    ((fkIsingSquareWiredCompleted_closed_darts_reachable_of_not_wired
      n hn d f hdf hdnot).trans hyf.symm)

private theorem fkIsingSquareWiredBondMate_eq_of_off_boundary_pair
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hd : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn))
    (hBd : fkIsingSquareBondMate n hn d ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    fkIsingSquareWiredBondMate n hn d = fkIsingSquareBondMate n hn d := by
  have hfix : (fkIsingSquareWiredShiftDartEquiv n hn).symm d = d := by
    have hforward : fkIsingSquareWiredShiftDartEquiv n hn d = d :=
      Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hd
    calc
      (fkIsingSquareWiredShiftDartEquiv n hn).symm d =
          (fkIsingSquareWiredShiftDartEquiv n hn).symm
            (fkIsingSquareWiredShiftDartEquiv n hn d) :=
        congrArg _ hforward.symm
      _ = d := (fkIsingSquareWiredShiftDartEquiv n hn).symm_apply_apply d
  simp only [fkIsingSquareWiredBondMate,
    fkIsingSquareWiredBondMateEquiv, Equiv.Perm.mul_apply]
  rw [hfix]
  exact Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hBd

private theorem fkIsingSquareWired_north_clockwise_not_boundary
    (n : Nat) (hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V)
    (hu : fkIsingSquareWiredArc n u)
    (hN : fkIsingSquareDirectionAvailable n u .north) :
    fkIsingSquareDirectionDart n u .north hN .clockwise ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  rintro ⟨i, hi⟩
  have hkey := congrArg (fun d : FKIsingMedialDart (fkSquareBoxPlanar n) =>
    (fkIsingSquareDartEndpoint n d, fkIsingSquareDartDirection n d,
      (fkIsingSquareSideCorner d.2).2)) hi
  cases i <;>
    simp [fkIsingSquareWiredBoundaryEmbedding,
      fkIsingSquareWiredBoundaryDart] at hkey

private theorem fkIsingSquareWired_south_counterclockwise_not_boundary
    (n : Nat) (hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V)
    (hu : fkIsingSquareWiredArc n u)
    (hS : fkIsingSquareDirectionAvailable n u .south) :
    fkIsingSquareDirectionDart n u .south hS .counterclockwise ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  rintro ⟨i, hi⟩
  have hkey := congrArg (fun d : FKIsingMedialDart (fkSquareBoxPlanar n) =>
    (fkIsingSquareDartEndpoint n d, fkIsingSquareDartDirection n d,
      (fkIsingSquareSideCorner d.2).2)) hi
  cases i <;>
    simp [fkIsingSquareWiredBoundaryEmbedding,
      fkIsingSquareWiredBoundaryDart] at hkey

private theorem fkIsingSquareWired_east_counterclockwise_not_boundary_of_north
    (n : Nat) (hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V)
    (hu : fkIsingSquareWiredArc n u)
    (hN : fkIsingSquareDirectionAvailable n u .north)
    (hE : fkIsingSquareDirectionAvailable n u .east) :
    fkIsingSquareDirectionDart n u .east hE .counterclockwise ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  rintro ⟨i, hi⟩
  have hkey := congrArg (fun d : FKIsingMedialDart (fkSquareBoxPlanar n) =>
    (fkIsingSquareDartEndpoint n d, fkIsingSquareDartDirection n d,
      (fkIsingSquareSideCorner d.2).2)) hi
  cases i with
  | bottom => simp [fkIsingSquareWiredBoundaryEmbedding,
      fkIsingSquareWiredBoundaryDart] at hkey
  | west k => simp [fkIsingSquareWiredBoundaryEmbedding,
      fkIsingSquareWiredBoundaryDart] at hkey
  | north k => simp [fkIsingSquareWiredBoundaryEmbedding,
      fkIsingSquareWiredBoundaryDart] at hkey
  | top =>
      have huTop : fkIsingSquareMarkedB n = u := by
        simpa [fkIsingSquareWiredBoundaryEmbedding,
          fkIsingSquareWiredBoundaryDart] using
            congrArg (fun x => x.1) hkey
      subst u
      simp [fkIsingSquareDirectionAvailable, fkIsingSquareMarkedB] at hN

private theorem fkIsingSquareWired_east_clockwise_not_boundary_of_south
    (n : Nat) (hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V)
    (hu : fkIsingSquareWiredArc n u)
    (hS : fkIsingSquareDirectionAvailable n u .south)
    (hE : fkIsingSquareDirectionAvailable n u .east) :
    fkIsingSquareDirectionDart n u .east hE .clockwise ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  rintro ⟨i, hi⟩
  have hkey := congrArg (fun d : FKIsingMedialDart (fkSquareBoxPlanar n) =>
    (fkIsingSquareDartEndpoint n d, fkIsingSquareDartDirection n d,
      (fkIsingSquareSideCorner d.2).2)) hi
  cases i with
  | bottom =>
      have huBottom : fkIsingSquareMarkedA n = u := by
        simpa [fkIsingSquareWiredBoundaryEmbedding,
          fkIsingSquareWiredBoundaryDart] using
            congrArg (fun x => x.1) hkey
      subst u
      simp [fkIsingSquareDirectionAvailable, fkIsingSquareMarkedA] at hS
  | west k => simp [fkIsingSquareWiredBoundaryEmbedding,
      fkIsingSquareWiredBoundaryDart] at hkey
  | north k => simp [fkIsingSquareWiredBoundaryEmbedding,
      fkIsingSquareWiredBoundaryDart] at hkey
  | top => simp [fkIsingSquareWiredBoundaryEmbedding,
      fkIsingSquareWiredBoundaryDart] at hkey

private theorem fkIsingSquareWiredCompleted_closed_north_reachable_east
    (n : Nat) (hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V)
    (hu : fkIsingSquareWiredArc n u)
    (hN : fkIsingSquareDirectionAvailable n u .north)
    (hE : fkIsingSquareDirectionAvailable n u .east) :
    (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
      (.dart (fkIsingSquareDirectionDart n u .north hN .counterclockwise))
      (.dart (fkIsingSquareDirectionDart n u .east hE .counterclockwise)) := by
  let nC := fkIsingSquareDirectionDart n u .north hN .counterclockwise
  let nW := fkIsingSquareDirectionDart n u .north hN .clockwise
  let eC := fkIsingSquareDirectionDart n u .east hE .counterclockwise
  have hlocal := fkIsingSquareWiredCompleted_closed_local_turn_reachable
    n hn u .north hN
  have hB0 : fkIsingSquareBondMate n hn nW = eC := by
    simp [nW, eC, fkIsingSquareBondMate,
      fkIsingSquarePreviousDirection, hE]
  have hnWoff := fkIsingSquareWired_north_clockwise_not_boundary
    n hn u hu hN
  have heCoff := fkIsingSquareWired_east_counterclockwise_not_boundary_of_north
    n hn u hu hN hE
  have hB : fkIsingSquareWiredBondMate n hn nW = eC := by
    rw [fkIsingSquareWiredBondMate_eq_of_off_boundary_pair
      n hn nW hnWoff (by simpa [hB0] using heCoff), hB0]
  exact hlocal.trans
    ((fkIsingSquareWiredCompleted_incidence_reachable
      n hn (FK.edgeSetConfig ∅) nW).trans
      ((fkIsingSquareWiredCompleted_bond_reachable_mate
        n hn (FK.edgeSetConfig ∅) nW).trans
        (by simpa [hB] using
          (fkIsingSquareWiredCompleted_incidence_reachable
            n hn (FK.edgeSetConfig ∅) eC).symm)))

private theorem fkIsingSquareWiredCompleted_closed_south_reachable_east
    (n : Nat) (hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V)
    (hu : fkIsingSquareWiredArc n u)
    (hS : fkIsingSquareDirectionAvailable n u .south)
    (hE : fkIsingSquareDirectionAvailable n u .east) :
    (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
      (.dart (fkIsingSquareDirectionDart n u .south hS .counterclockwise))
      (.dart (fkIsingSquareDirectionDart n u .east hE .counterclockwise)) := by
  let sC := fkIsingSquareDirectionDart n u .south hS .counterclockwise
  let eW := fkIsingSquareDirectionDart n u .east hE .clockwise
  let eC := fkIsingSquareDirectionDart n u .east hE .counterclockwise
  have hB0 : fkIsingSquareBondMate n hn sC = eW := by
    simp [sC, eW, fkIsingSquareBondMate,
      fkIsingSquareNextDirection, hE]
  have hsCoff := fkIsingSquareWired_south_counterclockwise_not_boundary
    n hn u hu hS
  have heWoff := fkIsingSquareWired_east_clockwise_not_boundary_of_south
    n hn u hu hS hE
  have hB : fkIsingSquareWiredBondMate n hn sC = eW := by
    rw [fkIsingSquareWiredBondMate_eq_of_off_boundary_pair
      n hn sC hsCoff (by simpa [hB0] using heWoff), hB0]
  have hlocal := fkIsingSquareWiredCompleted_closed_local_turn_reachable
    n hn u .east hE
  have hinc :
      (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
        (.bond eW) (.dart eW) :=
    (fkIsingSquareWiredCompleted_incidence_reachable
      n hn (FK.edgeSetConfig ∅) eW).symm
  have hinc' :
      (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
        (.bond (fkIsingSquareWiredBondMate n hn sC)) (.dart eW) := by
    rw [hB]
    exact hinc
  exact (fkIsingSquareWiredCompleted_incidence_reachable
      n hn (FK.edgeSetConfig ∅) sC).trans
    ((fkIsingSquareWiredCompleted_bond_reachable_mate
      n hn (FK.edgeSetConfig ∅) sC).trans
      (hinc'.trans hlocal.symm))

private theorem fkIsingSquareWired_east_available_of_wired
    (n : Nat) (hn : 0 < n) (u : (fkSquareBoxPlanar n).V)
    (hu : fkIsingSquareWiredArc n u) :
    fkIsingSquareDirectionAvailable n u .east := by
  have hb := fkIsingSquareVertex_coordinate_bounds n u 0
  simp only [fkIsingSquareWiredArc] at hu
  simp [fkIsingSquareDirectionAvailable, hu]
  omega



private theorem fkIsingSquareWiredCompleted_closed_dart_reachable_east_of_wired
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hu : fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n d)) :
    let u := fkIsingSquareDartEndpoint n d
    let hE := fkIsingSquareWired_east_available_of_wired n hn u hu
    (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
      (.dart d)
      (.dart (fkIsingSquareDirectionDart n u .east hE .counterclockwise)) := by
  dsimp only
  let u := fkIsingSquareDartEndpoint n d
  let dir := fkIsingSquareDartDirection n d
  let hd := fkIsingSquareDartDirection_available n d
  let hE := fkIsingSquareWired_east_available_of_wired n hn u hu
  have hrec := fkIsingSquareDirectionDart_reconstruct n d
  have hrec' : fkIsingSquareDirectionDart n u dir hd
      (fkIsingSquareSideCorner d.2).2 = d := by
    simpa only [u, dir, hd] using hrec
  suffices hcore :
      (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
        (.dart (fkIsingSquareDirectionDart n u dir hd
          (fkIsingSquareSideCorner d.2).2))
        (.dart (fkIsingSquareDirectionDart n u .east hE .counterclockwise)) by
    simpa only [hrec'] using hcore
  have hW : ¬ fkIsingSquareDirectionAvailable n u .west := by
    simp [fkIsingSquareDirectionAvailable, u,
      fkIsingSquareWiredArc] at hu ⊢
    omega
  have hdirection : ∀ (q : FKIsingSquareDirection)
      (hq : fkIsingSquareDirectionAvailable n u q)
      (turn : FKIsingSquareCornerTurn),
      (fkIsingSquareWiredCompletedLoopGraph n hn
        (FK.edgeSetConfig ∅)).Reachable
        (.dart (fkIsingSquareDirectionDart n u q hq turn))
        (.dart (fkIsingSquareDirectionDart n u .east hE
          .counterclockwise)) := by
    intro q hq turn
    cases q <;> cases turn
    · exact SimpleGraph.Reachable.refl _
    · exact (fkIsingSquareWiredCompleted_closed_local_turn_reachable
        n hn u .east hE).symm
    · exact fkIsingSquareWiredCompleted_closed_north_reachable_east
        n hn u hu hq hE
    · exact (fkIsingSquareWiredCompleted_closed_local_turn_reachable
        n hn u .north hq).symm.trans
          (fkIsingSquareWiredCompleted_closed_north_reachable_east
            n hn u hu hq hE)
    · exact False.elim (hW hq)
    · exact False.elim (hW hq)
    · exact fkIsingSquareWiredCompleted_closed_south_reachable_east
        n hn u hu hq hE
    · exact (fkIsingSquareWiredCompleted_closed_local_turn_reachable
        n hn u .south hq).symm.trans
          (fkIsingSquareWiredCompleted_closed_south_reachable_east
            n hn u hu hq hE)
  exact hdirection dir hd (fkIsingSquareSideCorner d.2).2

theorem fkIsingSquareWiredCompleted_closed_darts_reachable_of_same_wired_label
    (n : Nat) (hn : 0 < n)
    (d f : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hlabel : fkIsingSquareDartEndpoint n d = fkIsingSquareDartEndpoint n f)
    (hwired : fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n d)) :
    (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
      (.dart d) (.dart f) := by
  have hd := fkIsingSquareWiredCompleted_closed_dart_reachable_east_of_wired
    n hn d hwired
  have hfwired : fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n f) := by
    simpa only [← hlabel] using hwired
  have hf := fkIsingSquareWiredCompleted_closed_dart_reachable_east_of_wired
    n hn f hfwired
  dsimp only at hd hf
  have heast :
      fkIsingSquareDirectionDart n (fkIsingSquareDartEndpoint n d) .east
          (fkIsingSquareWired_east_available_of_wired n hn _ hwired)
          .counterclockwise =
        fkIsingSquareDirectionDart n (fkIsingSquareDartEndpoint n f) .east
          (fkIsingSquareWired_east_available_of_wired n hn _ hfwired)
          .counterclockwise := by
    apply fkIsingSquareDirectionDart_endpoint_congr n hlabel
  have hjoin :
      (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
        (.dart (fkIsingSquareDirectionDart n
          (fkIsingSquareDartEndpoint n d) .east
          (fkIsingSquareWired_east_available_of_wired n hn _ hwired)
          .counterclockwise))
        (.dart (fkIsingSquareDirectionDart n
          (fkIsingSquareDartEndpoint n f) .east
          (fkIsingSquareWired_east_available_of_wired n hn _ hfwired)
          .counterclockwise)) := by
    rw [heast]
  exact hd.trans (hjoin.trans hf.symm)

private theorem fkIsingSquareWiredCompleted_closed_left_edge_reachable
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
      (.dart (fkIsingSquareWiredBoundaryDart n hn (.west k)))
      (.dart (fkIsingSquareWiredBoundaryDart n hn (.north k))) := by
  let w := fkIsingSquareWiredBoundaryDart n hn (.west k)
  let s := fkIsingSquareWiredBoundaryDart n hn (.north k)
  have hB : fkIsingSquareWiredBondMate n hn w = s :=
    fkIsingSquareWiredBondMate_west n hn k
  exact (fkIsingSquareWiredCompleted_incidence_reachable
      n hn (FK.edgeSetConfig ∅) w).trans
    ((fkIsingSquareWiredCompleted_bond_reachable_mate
      n hn (FK.edgeSetConfig ∅) w).trans (by
        rw [hB]
        exact (fkIsingSquareWiredCompleted_incidence_reachable
          n hn (FK.edgeSetConfig ∅) s).symm))

private theorem fkIsingSquareWiredCompleted_closed_east_lower_reachable_upper
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    let lower := fkIsingSquareLeftVerticalLower n hn k
    let upper := fkIsingSquareLeftVerticalUpper n hn k
    let hEL := fkIsingSquareWired_east_available_of_wired n hn lower (by
      simp [lower, fkIsingSquareWiredArc,
        fkIsingSquareLeftVerticalLower])
    let hEU := fkIsingSquareWired_east_available_of_wired n hn upper (by
      simp [upper, fkIsingSquareWiredArc,
        fkIsingSquareLeftVerticalUpper])
    (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
      (.dart (fkIsingSquareDirectionDart n lower .east hEL .counterclockwise))
      (.dart (fkIsingSquareDirectionDart n upper .east hEU .counterclockwise)) := by
  dsimp only
  let w := fkIsingSquareWiredBoundaryDart n hn (.west k)
  let s := fkIsingSquareWiredBoundaryDart n hn (.north k)
  have hwiredL : fkIsingSquareWiredArc n
      (fkIsingSquareDartEndpoint n w) :=
    fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn (.west k)
  have hwiredU : fkIsingSquareWiredArc n
      (fkIsingSquareDartEndpoint n s) :=
    fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn (.north k)
  have hw := fkIsingSquareWiredCompleted_closed_dart_reachable_east_of_wired
    n hn w hwiredL
  have hs := fkIsingSquareWiredCompleted_closed_dart_reachable_east_of_wired
    n hn s hwiredU
  dsimp only at hw hs
  have hedge := fkIsingSquareWiredCompleted_closed_left_edge_reachable n hn k
  have hLower : fkIsingSquareDartEndpoint n w =
      fkIsingSquareLeftVerticalLower n hn k := by
    simp [w, fkIsingSquareWiredBoundaryDart]
  have hUpper : fkIsingSquareDartEndpoint n s =
      fkIsingSquareLeftVerticalUpper n hn k := by
    simp [s, fkIsingSquareWiredBoundaryDart]
  have hw' :
      (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
        (.dart w)
        (.dart (fkIsingSquareDirectionDart n
          (fkIsingSquareLeftVerticalLower n hn k) .east
          (fkIsingSquareWired_east_available_of_wired n hn _ (by
            simp [fkIsingSquareWiredArc, fkIsingSquareLeftVerticalLower]))
          .counterclockwise)) := by
    simpa only [hLower] using hw
  have hs' :
      (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
        (.dart s)
        (.dart (fkIsingSquareDirectionDart n
          (fkIsingSquareLeftVerticalUpper n hn k) .east
          (fkIsingSquareWired_east_available_of_wired n hn _ (by
            simp [fkIsingSquareWiredArc, fkIsingSquareLeftVerticalUpper]))
          .counterclockwise)) := by
    simpa only [hUpper] using hs
  exact hw'.symm.trans (hedge.trans hs')

private theorem fkIsingSquareWiredArc_eq_markedA_or_upper
    (n : Nat) (hn : 0 < n) (u : (fkSquareBoxPlanar n).V)
    (hu : fkIsingSquareWiredArc n u) :
    u = fkIsingSquareMarkedA n ∨
      ∃ k : Fin (2 * n), u = fkIsingSquareLeftVerticalUpper n hn k := by
  by_cases hA : u = fkIsingSquareMarkedA n
  · exact Or.inl hA
  right
  have hb := fkIsingSquareVertex_coordinate_bounds n u 1
  have hgt : -(n : Int) < u.1 1 := by
    have hne : u.1 1 ≠ -(n : Int) := by
      intro h
      apply hA
      apply Subtype.ext
      funext i
      fin_cases i
      · simpa [fkIsingSquareMarkedA, fkIsingSquareWiredArc] using hu
      · simpa [fkIsingSquareMarkedA] using h
    omega
  have hzpos : 0 < u.1 1 + (n : Int) := by omega
  have hzle : u.1 1 + (n : Int) ≤ 2 * (n : Int) := by omega
  let z : Nat := (u.1 1 + (n : Int)).natAbs
  have hzcast : (z : Int) = u.1 1 + (n : Int) := by
    simp [z, Int.natAbs_of_nonneg (le_of_lt hzpos)]
  have hzposN : 0 < z := by
    omega
  have hzleN : z ≤ 2 * n := by
    omega
  let k : Fin (2 * n) := ⟨z - 1, by omega⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  funext i
  fin_cases i
  · simpa [fkIsingSquareLeftVerticalUpper,
      fkIsingSquareWiredArc] using hu
  · simp only [fkIsingSquareLeftVerticalUpper]
    rw [Nat.cast_sub (by omega : 1 ≤ z)]
    push_cast
    omega

private theorem fkIsingSquareWiredCompleted_closed_markedA_reachable_upper_east
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    let hEA := fkIsingSquareWired_east_available_of_wired n hn
      (fkIsingSquareMarkedA n) (by simp [fkIsingSquareWiredArc,
        fkIsingSquareMarkedA])
    let hEU := fkIsingSquareWired_east_available_of_wired n hn
      (fkIsingSquareLeftVerticalUpper n hn k) (by
        simp [fkIsingSquareWiredArc, fkIsingSquareLeftVerticalUpper])
    (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
      (.dart (fkIsingSquareDirectionDart n (fkIsingSquareMarkedA n)
        .east hEA .counterclockwise))
      (.dart (fkIsingSquareDirectionDart n
        (fkIsingSquareLeftVerticalUpper n hn k)
        .east hEU .counterclockwise)) := by
  dsimp only
  induction kval : k.val using Nat.strong_induction_on generalizing k with
  | h m ih =>
      have hstep :=
        fkIsingSquareWiredCompleted_closed_east_lower_reachable_upper n hn k
      dsimp only at hstep
      by_cases hk0 : k.val = 0
      · have hLower : fkIsingSquareLeftVerticalLower n hn k =
            fkIsingSquareMarkedA n := by
          apply Subtype.ext
          funext i
          fin_cases i <;>
            simp [fkIsingSquareLeftVerticalLower,
              fkIsingSquareMarkedA, hk0]
        simpa only [hLower] using hstep
      · let j : Fin (2 * n) := ⟨k.val - 1, by omega⟩
        have hj : j.val < m := by simp [j, kval]; omega
        have hprev := ih j.val hj j rfl
        have hLower : fkIsingSquareLeftVerticalLower n hn k =
            fkIsingSquareLeftVerticalUpper n hn j := by
          apply Subtype.ext
          funext i
          fin_cases i
          · simp [fkIsingSquareLeftVerticalLower,
              fkIsingSquareLeftVerticalUpper]
          · simp only [fkIsingSquareLeftVerticalLower,
              fkIsingSquareLeftVerticalUpper, j]
            rw [Nat.cast_sub (by omega : 1 ≤ k.val)]
            push_cast
            ring
        have hstep' :
            (fkIsingSquareWiredCompletedLoopGraph n hn
              (FK.edgeSetConfig ∅)).Reachable
              (.dart (fkIsingSquareDirectionDart n
                (fkIsingSquareLeftVerticalUpper n hn j) .east
                (fkIsingSquareWired_east_available_of_wired n hn _ (by
                  simp [fkIsingSquareWiredArc,
                    fkIsingSquareLeftVerticalUpper])) .counterclockwise))
              (.dart (fkIsingSquareDirectionDart n
                (fkIsingSquareLeftVerticalUpper n hn k) .east
                (fkIsingSquareWired_east_available_of_wired n hn _ (by
                  simp [fkIsingSquareWiredArc,
                    fkIsingSquareLeftVerticalUpper])) .counterclockwise)) := by
          simpa only [hLower] using hstep
        exact hprev.trans hstep'

private theorem fkIsingSquareWiredCompleted_closed_dart_reachable_markedA_east
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hwired : fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n d)) :
    let hEA := fkIsingSquareWired_east_available_of_wired n hn
      (fkIsingSquareMarkedA n) (by
        simp [fkIsingSquareWiredArc, fkIsingSquareMarkedA])
    (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
      (.dart d)
      (.dart (fkIsingSquareDirectionDart n (fkIsingSquareMarkedA n)
        .east hEA .counterclockwise)) := by
  dsimp only
  have hd := fkIsingSquareWiredCompleted_closed_dart_reachable_east_of_wired
    n hn d hwired
  dsimp only at hd
  rcases fkIsingSquareWiredArc_eq_markedA_or_upper
      n hn (fkIsingSquareDartEndpoint n d) hwired with hA | ⟨k, hk⟩
  · have heast :
        fkIsingSquareDirectionDart n (fkIsingSquareDartEndpoint n d)
            .east (fkIsingSquareWired_east_available_of_wired n hn _ hwired)
            .counterclockwise =
          fkIsingSquareDirectionDart n (fkIsingSquareMarkedA n)
            .east (fkIsingSquareWired_east_available_of_wired n hn _ (by
              simp [fkIsingSquareWiredArc, fkIsingSquareMarkedA]))
            .counterclockwise := by
      apply fkIsingSquareDirectionDart_endpoint_congr n hA
    have hjoin :
        (fkIsingSquareWiredCompletedLoopGraph n hn
          (FK.edgeSetConfig ∅)).Reachable
          (.dart (fkIsingSquareDirectionDart n
            (fkIsingSquareDartEndpoint n d) .east
            (fkIsingSquareWired_east_available_of_wired n hn _ hwired)
            .counterclockwise))
          (.dart (fkIsingSquareDirectionDart n (fkIsingSquareMarkedA n)
            .east (fkIsingSquareWired_east_available_of_wired n hn _ (by
              simp [fkIsingSquareWiredArc, fkIsingSquareMarkedA]))
            .counterclockwise)) := by rw [heast]
    exact hd.trans hjoin
  · have hchain :=
      fkIsingSquareWiredCompleted_closed_markedA_reachable_upper_east n hn k
    dsimp only at hchain
    have heast :
        fkIsingSquareDirectionDart n (fkIsingSquareDartEndpoint n d)
            .east (fkIsingSquareWired_east_available_of_wired n hn _ hwired)
            .counterclockwise =
          fkIsingSquareDirectionDart n
            (fkIsingSquareLeftVerticalUpper n hn k)
            .east (fkIsingSquareWired_east_available_of_wired n hn _ (by
              simp [fkIsingSquareWiredArc,
                fkIsingSquareLeftVerticalUpper]))
            .counterclockwise := by
      apply fkIsingSquareDirectionDart_endpoint_congr n hk
    have hjoin :
        (fkIsingSquareWiredCompletedLoopGraph n hn
          (FK.edgeSetConfig ∅)).Reachable
          (.dart (fkIsingSquareDirectionDart n
            (fkIsingSquareDartEndpoint n d) .east
            (fkIsingSquareWired_east_available_of_wired n hn _ hwired)
            .counterclockwise))
          (.dart (fkIsingSquareDirectionDart n
            (fkIsingSquareLeftVerticalUpper n hn k)
            .east (fkIsingSquareWired_east_available_of_wired n hn _ (by
              simp [fkIsingSquareWiredArc,
                fkIsingSquareLeftVerticalUpper]))
            .counterclockwise)) := by rw [heast]
    exact hd.trans (hjoin.trans hchain.symm)



theorem fkIsingSquareWiredCompleted_closed_reachable_of_wired_labels
    (n : Nat) (hn : 0 < n)
    (x y : FKIsingSquareWiredCarrier n)
    (hx : fkIsingSquareWiredArc n
      (fkIsingSquareWiredCarrierPrimalLabel n hn x))
    (hy : fkIsingSquareWiredArc n
      (fkIsingSquareWiredCarrierPrimalLabel n hn y)) :
    (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
      x y := by
  obtain ⟨d, hxd, hdx⟩ :=
    fkIsingSquareWiredCompleted_reachable_dart_same_label
      n hn (FK.edgeSetConfig ∅) x
  obtain ⟨f, hyf, hfy⟩ :=
    fkIsingSquareWiredCompleted_reachable_dart_same_label
      n hn (FK.edgeSetConfig ∅) y
  have hdwired : fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n d) := by
    simpa only [← hdx] using hx
  have hfwired : fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n f) := by
    simpa only [← hfy] using hy
  have hd := fkIsingSquareWiredCompleted_closed_dart_reachable_markedA_east
    n hn d hdwired
  have hf := fkIsingSquareWiredCompleted_closed_dart_reachable_markedA_east
    n hn f hfwired
  dsimp only at hd hf
  exact hxd.trans (hd.trans (hf.symm.trans hyf.symm))

private theorem boundaryCliqueGraph_reachable_iff_eq_or_both
    {V : Type*} [Fintype V] [DecidableEq V]
    (bdry : V → Prop) [DecidablePred bdry] (x y : V) :
    (boundaryCliqueGraph bdry).Reachable x y ↔
      x = y ∨ (bdry x ∧ bdry y) := by
  classical
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact Or.inl rfl
    | @cons u v w huv p ih =>
        have huv' := (boundaryCliqueGraph_adj bdry u v).1 huv
        rcases ih with rfl | ⟨hv, hw⟩
        · exact Or.inr ⟨huv'.2.1, huv'.2.2⟩
        · exact Or.inr ⟨huv'.2.1, hw⟩
  · rintro (rfl | ⟨hx, hy⟩)
    · exact SimpleGraph.Reachable.refl _
    · by_cases hxy : x = y
      · subst y
        exact SimpleGraph.Reachable.refl _
      · exact ((boundaryCliqueGraph_adj bdry x y).2
          ⟨hxy, hx, hy⟩).reachable

private theorem fkIsingSquareWired_empty_primal_reachable_iff
    (n : Nat) (hn : 0 < n) (u v : (fkSquareBoxPlanar n).V) :
    (openSub (fkSquareBoxPlanar n).G (FK.edgeSetConfig ∅) ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable u v ↔
      u = v ∨ (fkIsingSquareWiredArc n u ∧
        fkIsingSquareWiredArc n v) := by
  classical
  have hopen : openSub (fkSquareBoxPlanar n).G (FK.edgeSetConfig ∅) = ⊥ := by
    ext a b
    simp [FK.edgeSetConfig]
  rw [hopen, bot_sup_eq, FKIsingDobrushinDomain.wiring,
    fkIsingSquareWiredDobrushinDomain]
  exact boundaryCliqueGraph_reachable_iff_eq_or_both
    (fkIsingSquareWiredArc n) u v



theorem fkIsingSquareWiredCompleted_closed_reachable_iff_primal
    (n : Nat) (hn : 0 < n) (x y : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
        x y ↔
      (openSub (fkSquareBoxPlanar n).G (FK.edgeSetConfig ∅) ⊔
          (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
        (fkIsingSquareWiredCarrierPrimalLabel n hn x)
        (fkIsingSquareWiredCarrierPrimalLabel n hn y) := by
  constructor
  · intro hxy
    have hloop := (fkIsingSquareWiredCompletedLoopGraph_reachable_iff
      n hn (FK.edgeSetConfig ∅) x y).1 hxy
    exact fkIsingSquareWiredLoopGraph_reachable_primalLabel_reachable
      n hn (FK.edgeSetConfig ∅) hloop
  · intro hxy
    rw [fkIsingSquareWired_empty_primal_reachable_iff] at hxy
    rcases hxy with hlabel | ⟨hx, hy⟩
    · by_cases hwired : fkIsingSquareWiredArc n
          (fkIsingSquareWiredCarrierPrimalLabel n hn x)
      · exact fkIsingSquareWiredCompleted_closed_reachable_of_wired_labels
          n hn x y hwired (by simpa only [← hlabel] using hwired)
      · exact fkIsingSquareWiredCompleted_closed_reachable_of_label_eq_not_wired
          n hn x y hlabel hwired
    · exact fkIsingSquareWiredCompleted_closed_reachable_of_wired_labels
        n hn x y hx hy

private noncomputable def fkIsingSquareWiredClosedComponentToPrimal
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquareWiredCompletedLoopGraph n hn
        (FK.edgeSetConfig ∅)).ConnectedComponent →
      (openSub (fkSquareBoxPlanar n).G (FK.edgeSetConfig ∅) ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).ConnectedComponent :=
  fun C => (openSub (fkSquareBoxPlanar n).G (FK.edgeSetConfig ∅) ⊔
    (fkIsingSquareWiredDobrushinDomain n hn).wiring).connectedComponentMk
      (fkIsingSquareWiredCarrierPrimalLabel n hn C.out)

private theorem fkIsingSquare_exists_dart_endpoint
    (n : Nat) (hn : 0 < n) (u : (fkSquareBoxPlanar n).V) :
    ∃ d : FKIsingMedialDart (fkSquareBoxPlanar n),
      fkIsingSquareDartEndpoint n d = u := by
  by_cases hE : fkIsingSquareDirectionAvailable n u .east
  · exact ⟨fkIsingSquareDirectionDart n u .east hE .counterclockwise, by simp⟩
  · have hW : fkIsingSquareDirectionAvailable n u .west := by
      have hb := fkIsingSquareVertex_coordinate_bounds n u 0
      simp [fkIsingSquareDirectionAvailable] at hE ⊢
      omega
    exact ⟨fkIsingSquareDirectionDart n u .west hW .counterclockwise, by simp⟩

private theorem fkIsingSquareWiredClosedComponentToPrimal_bijective
    (n : Nat) (hn : 0 < n) :
    Function.Bijective (fkIsingSquareWiredClosedComponentToPrimal n hn) := by
  constructor
  · intro C D hCD
    rw [← C.out_eq, ← D.out_eq]
    apply SimpleGraph.ConnectedComponent.sound
    apply (fkIsingSquareWiredCompleted_closed_reachable_iff_primal
      n hn C.out D.out).2
    exact SimpleGraph.ConnectedComponent.eq.mp hCD
  · intro C
    obtain ⟨d, hd⟩ := fkIsingSquare_exists_dart_endpoint n hn C.out
    let G := fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)
    let D := G.connectedComponentMk (.dart d)
    refine ⟨D, ?_⟩
    change (openSub (fkSquareBoxPlanar n).G (FK.edgeSetConfig ∅) ⊔
      (fkIsingSquareWiredDobrushinDomain n hn).wiring).connectedComponentMk
        (fkIsingSquareWiredCarrierPrimalLabel n hn D.out) = C
    rw [← C.out_eq]
    apply SimpleGraph.ConnectedComponent.sound
    have hmed : G.Reachable D.out (.dart d) := by
      apply SimpleGraph.ConnectedComponent.eq.mp
      exact D.out_eq
    have hprim := (fkIsingSquareWiredCompleted_closed_reachable_iff_primal
      n hn D.out (.dart d)).1 hmed
    have hend :
        (openSub (fkSquareBoxPlanar n).G (FK.edgeSetConfig ∅) ⊔
          (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
            (fkIsingSquareWiredCarrierPrimalLabel n hn (.dart d)) C.out := by
      rw [fkIsingSquareWiredCarrierPrimalLabel, hd]
    exact hprim.trans hend



theorem fkIsingSquareWired_empty_completed_componentCount
    (n : Nat) (hn : 0 < n) :
    Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
        (FK.edgeSetConfig ∅)).ConnectedComponent =
      (2 * n + 1) ^ 2 - 2 * n := by
  rw [Nat.card_congr (Equiv.ofBijective
    (fkIsingSquareWiredClosedComponentToPrimal n hn)
    (fkIsingSquareWiredClosedComponentToPrimal_bijective n hn))]
  exact fkIsingSquareWired_empty_clusterCount n hn

private theorem fkIsingSquareWiredCompleted_closed_markedA_reachable_wired_dart
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hd : fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n d)) :
    let hEA := fkIsingSquareWired_east_available_of_wired n hn
      (fkIsingSquareMarkedA n) (by
        simp [fkIsingSquareWiredArc, fkIsingSquareMarkedA])
    (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
      (.dart (fkIsingSquareDirectionDart n (fkIsingSquareMarkedA n)
        .east hEA .counterclockwise))
      (.dart d) := by
  dsimp only
  have hrotate :=
    fkIsingSquareWiredCompleted_closed_dart_reachable_east_of_wired
      n hn d hd
  dsimp only at hrotate
  rcases fkIsingSquareWiredArc_eq_markedA_or_upper n hn
    (fkIsingSquareDartEndpoint n d) hd with hA | ⟨k, hk⟩
  · have heq :
        fkIsingSquareDirectionDart n (fkIsingSquareMarkedA n) .east
            (fkIsingSquareWired_east_available_of_wired n hn _ (by
              simp [fkIsingSquareWiredArc, fkIsingSquareMarkedA]))
            .counterclockwise =
          fkIsingSquareDirectionDart n (fkIsingSquareDartEndpoint n d) .east
            (fkIsingSquareWired_east_available_of_wired n hn _ hd)
            .counterclockwise := by
      apply fkIsingSquareDirectionDart_endpoint_congr n hA.symm
    rw [heq]
    exact hrotate.symm
  · have hchain :=
        fkIsingSquareWiredCompleted_closed_markedA_reachable_upper_east
          n hn k
    dsimp only at hchain
    have heq :
        fkIsingSquareDirectionDart n
            (fkIsingSquareLeftVerticalUpper n hn k) .east
            (fkIsingSquareWired_east_available_of_wired n hn _ (by
              simp [fkIsingSquareWiredArc,
                fkIsingSquareLeftVerticalUpper])) .counterclockwise =
          fkIsingSquareDirectionDart n (fkIsingSquareDartEndpoint n d) .east
            (fkIsingSquareWired_east_available_of_wired n hn _ hd)
            .counterclockwise := by
      apply fkIsingSquareDirectionDart_endpoint_congr n hk.symm
    rw [heq] at hchain
    exact hchain.trans hrotate.symm



theorem fkIsingSquareWiredCompleted_closed_darts_reachable_of_wired
    (n : Nat) (hn : 0 < n)
    (d f : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hd : fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n d))
    (hf : fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n f)) :
    (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
      (.dart d) (.dart f) := by
  exact (fkIsingSquareWiredCompleted_closed_markedA_reachable_wired_dart
    n hn d hd).symm.trans
      (fkIsingSquareWiredCompleted_closed_markedA_reachable_wired_dart
        n hn f hf)



theorem fkIsingSquareWiredCompleted_closed_reachable_of_wired
    (n : Nat) (hn : 0 < n)
    (x y : FKIsingSquareWiredCarrier n)
    (hx : fkIsingSquareWiredArc n
      (fkIsingSquareWiredCarrierPrimalLabel n hn x))
    (hy : fkIsingSquareWiredArc n
      (fkIsingSquareWiredCarrierPrimalLabel n hn y)) :
    (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
      x y := by
  obtain ⟨d, hxd, hdx⟩ :=
    fkIsingSquareWiredCompleted_reachable_dart_same_label
      n hn (FK.edgeSetConfig ∅) x
  obtain ⟨f, hyf, hfy⟩ :=
    fkIsingSquareWiredCompleted_reachable_dart_same_label
      n hn (FK.edgeSetConfig ∅) y
  have hd : fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n d) := by
    simpa only [← hdx] using hx
  have hf : fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n f) := by
    simpa only [← hfy] using hy
  exact hxd.trans
    ((fkIsingSquareWiredCompleted_closed_darts_reachable_of_wired
      n hn d f hd hf).trans hyf.symm)

end StatMech.Universality
