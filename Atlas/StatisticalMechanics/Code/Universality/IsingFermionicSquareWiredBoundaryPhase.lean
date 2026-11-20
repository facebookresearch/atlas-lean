/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareBoundaryGeometry
import Code.Universality.IsingFermionicSquareWiredTangentCode












namespace StatMech.Universality

open Finset Complex SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareSignedEighthTurn_modEq
    (a b : Int) :
    fkIsingSquareSignedEighthTurn a b ≡ b - a [ZMOD 8] := by
  simpa [fkIsingSquareSignedEighthTurn] using
    (Int.mod_modEq (b - a + 4) 8).sub (Int.ModEq.refl 4)

@[simp] theorem fkIsingSquareWiredDirectedTangentCode_incidenceMate
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareWiredCarrier n) :
    fkIsingSquareWiredDirectedTangentCode n hn
        (fkIsingSquareWiredIncidenceMate n x) =
      fkIsingSquareWiredDirectedTangentCode n hn x := by
  cases x <;> rfl

set_option maxHeartbeats 800000 in

theorem fkIsingSquareWiredBondTurn_modEq_directedTangent
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredBondTurn n hn d
        (fkIsingSquareWiredBondMate n hn d) ≡
      fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d)) -
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d) [ZMOD 8] := by
  let f := fkIsingSquareWiredBondMate n hn d
  change fkIsingSquareWiredBondTurn n hn d f ≡
    fkIsingSquareWiredDirectedTangentCode n hn (.bond f) -
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d) [ZMOD 8]
  by_cases hforward : fkIsingSquareWiredBoundaryForward n hn d f
  · rw [fkIsingSquareWiredBondTurn, if_pos hforward]
    rcases hforward with ⟨hd, hf⟩ | ⟨k, hd, hf⟩
    · rw [hd, hf]
      norm_num [fkIsingSquareWiredSourceDart,
        fkIsingSquareWiredTerminalDart]
    · rw [hd, hf]
      norm_num
  · by_cases hreverse : fkIsingSquareWiredBoundaryReverse n hn d f
    · rw [fkIsingSquareWiredBondTurn, if_neg hforward, if_pos hreverse]
      rcases hreverse with ⟨hf, hd⟩ | ⟨k, hf, hd⟩
      · rw [hd, hf]
        norm_num [fkIsingSquareWiredSourceDart,
          fkIsingSquareWiredTerminalDart]
      · rw [hd, hf]
        norm_num
    · have hturn := fkIsingSquareWiredBondMate_turn_ne n hn d
      have hprincipal :
          fkIsingSquareOrientedPrincipalBondTurn n hn d f ≡
            fkIsingSquareWiredCarrierTangentCode n hn (.bond f) + 4 -
              fkIsingSquareWiredCarrierTangentCode n hn (.bond d) [ZMOD 8] := by
        unfold fkIsingSquareOrientedPrincipalBondTurn
        dsimp only
        split_ifs with hhalf
        · have hsigned := fkIsingSquareSignedEighthTurn_modEq
            (fkIsingSquareWiredCarrierTangentCode n hn (.bond d))
            (fkIsingSquareWiredCarrierTangentCode n hn (.bond f) + 4)
          have hfour : (4 : Int) ≡ -4 [ZMOD 8] := by decide
          exact hfour.trans (hhalf.1.symm ▸ hsigned)
        · exact fkIsingSquareSignedEighthTurn_modEq
            (fkIsingSquareWiredCarrierTangentCode n hn (.bond d))
            (fkIsingSquareWiredCarrierTangentCode n hn (.bond f) + 4)
      rw [fkIsingSquareWiredBondTurn, if_neg hforward, if_neg hreverse]
      apply hprincipal.trans
      rcases htd : (fkIsingSquareSideCorner d.2).2 with _ | _ <;>
        rcases htf : (fkIsingSquareSideCorner f.2).2 with _ | _
      · exact False.elim (hturn (htf.trans htd.symm))
      · simp [fkIsingSquareWiredDirectedTangentCode,
          fkIsingSquareWiredObservationCorrection, htd, htf]
      · rw [Int.modEq_iff_dvd]
        refine ⟨-1, ?_⟩
        simp [fkIsingSquareWiredDirectedTangentCode,
          fkIsingSquareWiredObservationCorrection, htd, htf]
        ring
      · exact False.elim (hturn (htf.trans htd.symm))

@[simp] theorem fkIsingSquareWiredDirectedTangentCode_source
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredDirectedTangentCode n hn .source = 9 := by
  simpa [fkIsingSquareWiredDirectedTangentCode,
    fkIsingSquareWiredObservationCorrection,
    fkIsingSquareWiredCarrierTangentCode,
    fkIsingSquareWiredSourceDart] using
      (fkIsingSquareWiredDirectedTangentCode_boundaryDart n hn .bottom)

@[simp] theorem fkIsingSquareWiredDirectedTangentCode_terminal
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredDirectedTangentCode n hn .terminal = 3 := by
  have hturn : (fkIsingSquareSideCorner
      (fkIsingSquareWiredTerminalDart n hn).2).2 =
      FKIsingSquareCornerTurn.counterclockwise := by
    simp [fkIsingSquareWiredTerminalDart,
      fkIsingSquareWiredBoundaryDart]
  have h := fkIsingSquareWiredDirectedTangentCode_boundaryDart n hn .top
  change (fkIsingSquareSideCorner
    (fkIsingSquareWiredBoundaryDart n hn .top).2).2 =
      FKIsingSquareCornerTurn.counterclockwise at hturn
  simp only [fkIsingSquareWiredDirectedTangentCode,
    fkIsingSquareWiredObservationCorrection,
    fkIsingSquareWiredCarrierTangentCode,
    fkIsingSquareWiredTerminalDart] at h ⊢
  rw [hturn] at h
  simpa using h

set_option maxHeartbeats 800000 in


theorem fkIsingSquareWiredTransitionTurn_modEq_directedTangent
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hxy : (fkIsingSquareWiredLoopGraph n hn omega).Adj x y) :
    fkIsingSquareWiredTransitionTurn n hn omega x y ≡
      fkIsingSquareWiredDirectedTangentCode n hn y -
        fkIsingSquareWiredDirectedTangentCode n hn x [ZMOD 8] := by
  rcases hxy with ⟨hxs, hxt, rfl⟩ | rfl
  · rw [fkIsingSquareWiredDirectedTangentCode_incidenceMate]
    cases x <;> simp_all [fkIsingSquareWiredTransitionTurn,
      fkIsingSquareWiredIncidenceMate]
  · cases x with
    | source =>
        simp [fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredTransitionTurn,
          fkIsingSquareWiredSourceDart]
    | terminal =>
        simp [fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredTransitionTurn,
          fkIsingSquareWiredTerminalDart]
    | dart d =>
        rcases d with ⟨e, side⟩
        cases homega : omega e.1 <;> cases side <;>
          cases haxis : (fkIsingSquareOrientedEdge n e).axis <;>
          norm_num [fkIsingSquareWiredTransitionMate,
            fkIsingSquareWiredTransitionTurn,
            fkIsingSquareWiredDirectedTangentCode,
            fkIsingSquareWiredObservationCorrection,
            fkIsingSquareWiredCarrierTangentCode,
            fkIsingSquareCornerTangentCode,
            fkIsingSquareSignedEighthTurn,
            FKIsingMedialDart.localMate, fkIsingSquareDartDirection,
            fkIsingSquareSideCorner, FKIsingSquareDirection.eighthTurn,
            homega, haxis, Int.ModEq]
    | bond d =>
        by_cases ha : d = fkIsingSquareWiredSourceDart n hn
        · subst d
          simp [fkIsingSquareWiredTransitionMate,
            fkIsingSquareWiredTransitionTurn,
            fkIsingSquareWiredSourceDart]
        by_cases hb : d = fkIsingSquareWiredTerminalDart n hn
        · subst d
          have hne : fkIsingSquareWiredBoundaryDart n hn .top ≠
              fkIsingSquareWiredSourceDart n hn := by
            simpa [fkIsingSquareWiredTerminalDart] using ha
          simp [fkIsingSquareWiredTransitionMate,
            fkIsingSquareWiredTransitionTurn,
            fkIsingSquareWiredTerminalDart, hne]
        · simpa [fkIsingSquareWiredTransitionMate,
            fkIsingSquareWiredTransitionTurn, ha, hb] using
            fkIsingSquareWiredBondTurn_modEq_directedTangent n hn d

@[simp] theorem fkIsingSquareWiredRawTurnCount_source
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    fkIsingSquareWiredRawTurnCount n hn omega .source = 0 := by
  let p : (fkIsingSquareWiredLoopGraph n hn omega).Walk
      (.source : FKIsingSquareWiredCarrier n) .terminal :=
    fkIsingSquareWiredExplorationPath n hn omega
  have hidx : p.support.idxOf (.source : FKIsingSquareWiredCarrier n) = 0 :=
    (List.idxOf_eq_zero_iff_head_eq p.support_ne_nil).2 p.head_support
  simp [fkIsingSquareWiredRawTurnCount,
    fkIsingSquareWiredExplorationOrder, p, hidx]

theorem fkIsingSquareWiredExplorationOrder_adj_succ
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (i : Nat)
    (hi : i + 1 < (fkIsingSquareWiredExplorationOrder n hn omega).length) :
    (fkIsingSquareWiredLoopGraph n hn omega).Adj
      (fkIsingSquareWiredExplorationOrder n hn omega)[i]
      (fkIsingSquareWiredExplorationOrder n hn omega)[i + 1] := by
  let p : (fkIsingSquareWiredLoopGraph n hn omega).Walk
      (.source : FKIsingSquareWiredCarrier n) .terminal :=
    fkIsingSquareWiredExplorationPath n hn omega
  have hiWalk : i < p.length := by
    change i + 1 < p.support.length at hi
    rw [p.length_support] at hi
    omega
  have h := p.adj_getVert_succ hiWalk
  rw [p.getVert_eq_support_getElem (by omega),
    p.getVert_eq_support_getElem (by omega)] at h
  simpa only [fkIsingSquareWiredExplorationOrder, p] using h



theorem fkIsingSquareWiredRawTurnCount_getElem_modEq
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (i : Nat)
    (hi : i < (fkIsingSquareWiredExplorationOrder n hn omega).length) :
    fkIsingSquareWiredRawTurnCount n hn omega
        (fkIsingSquareWiredExplorationOrder n hn omega)[i] ≡
      fkIsingSquareWiredDirectedTangentCode n hn
          (fkIsingSquareWiredExplorationOrder n hn omega)[i] -
        fkIsingSquareWiredDirectedTangentCode n hn .source [ZMOD 8] := by
  induction i with
  | zero =>
      let p : (fkIsingSquareWiredLoopGraph n hn omega).Walk
          (.source : FKIsingSquareWiredCarrier n) .terminal :=
        fkIsingSquareWiredExplorationPath n hn omega
      have hzero : (fkIsingSquareWiredExplorationOrder n hn omega)[0] =
          (.source : FKIsingSquareWiredCarrier n) := by
        simpa only [fkIsingSquareWiredExplorationOrder, p] using
          p.support_getElem_zero
      rw [hzero, fkIsingSquareWiredRawTurnCount_source]
      simp
  | succ i ih =>
      have hiStep : i + 1 <
          (fkIsingSquareWiredExplorationOrder n hn omega).length := by
        simpa only [Nat.succ_eq_add_one] using hi
      rw [fkIsingSquareWiredRawTurnCount_succ n hn omega i hiStep]
      have ht := fkIsingSquareWiredTransitionTurn_modEq_directedTangent
        n hn omega (fkIsingSquareWiredExplorationOrder_adj_succ
          n hn omega i hiStep)
      have hsum := (ih (by omega)).add ht
      convert hsum using 1 <;> ring



theorem fkIsingSquareWiredRawTurnCount_modEq_directedTangent
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n)
    (hz : z ∈ fkIsingSquareWiredExplorationOrder n hn omega) :
    fkIsingSquareWiredRawTurnCount n hn omega z ≡
      fkIsingSquareWiredDirectedTangentCode n hn z -
        fkIsingSquareWiredDirectedTangentCode n hn .source [ZMOD 8] := by
  let p := fkIsingSquareWiredExplorationOrder n hn omega
  have hi : p.idxOf z < p.length := List.idxOf_lt_length_iff.mpr hz
  have h := fkIsingSquareWiredRawTurnCount_getElem_modEq n hn omega
    (p.idxOf z) hi
  simpa only [p, List.getElem_idxOf hi] using h




theorem fkIsingSquareWiredPhysicalTurnCount_modEq_directedTangent
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n)
    (hz : z ∈ fkIsingSquareWiredExplorationOrder n hn omega) :
    fkIsingSquareWiredPhysicalTurnCount n hn omega z ≡
      fkIsingSquareWiredDirectedTangentCode n hn z -
        fkIsingSquareWiredDirectedTangentCode n hn .terminal [ZMOD 8] := by
  have hzraw := fkIsingSquareWiredRawTurnCount_modEq_directedTangent
    n hn omega z hz
  have htraw := fkIsingSquareWiredRawTurnCount_modEq_directedTangent
    n hn omega (.terminal : FKIsingSquareWiredCarrier n)
    (fkIsingSquareWiredExplorationOrder_terminal_mem n hn omega)
  have hsub := hzraw.sub htraw
  unfold fkIsingSquareWiredPhysicalTurnCount
  convert hsub using 1 <;> ring

end

end StatMech.Universality
