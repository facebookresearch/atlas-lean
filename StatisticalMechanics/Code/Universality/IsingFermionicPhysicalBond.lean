/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalIncidence

namespace StatMech.Universality

open SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

private theorem fkIsingSquareSignedEighthTurn_shift_pair (a b : Int) :
    let x := fkIsingSquareSignedEighthTurn a (b + 4)
    let y := fkIsingSquareSignedEighthTurn b (a + 4)
    (x = -4 ∧ y = -4) ∨
      (x + y = 0 ∧ x ≠ -4 ∧ y ≠ -4) := by
  dsimp [fkIsingSquareSignedEighthTurn]
  omega

private theorem fkIsingSquareOrientedPrincipalTurn_reverse_ccw
    (a b : Int) :
    (if fkIsingSquareSignedEighthTurn a (b + 4) = -4 then 4
      else fkIsingSquareSignedEighthTurn a (b + 4)) =
      -(fkIsingSquareSignedEighthTurn b (a + 4)) := by
  obtain hpair | ⟨hsum, hxne, _hyne⟩ :=
    fkIsingSquareSignedEighthTurn_shift_pair a b
  · simp [hpair.1, hpair.2]
  · by_cases hx : fkIsingSquareSignedEighthTurn a (b + 4) = -4
    · exact False.elim (hxne hx)
    · simp [hx]
      omega

private theorem fkIsingSquareOrientedPrincipalTurn_reverse_cw
    (a b : Int) :
    fkIsingSquareSignedEighthTurn a (b + 4) =
      -(if fkIsingSquareSignedEighthTurn b (a + 4) = -4 then 4
        else fkIsingSquareSignedEighthTurn b (a + 4)) := by
  obtain hpair | ⟨hsum, _hxne, hyne⟩ :=
    fkIsingSquareSignedEighthTurn_shift_pair a b
  · simp [hpair.1, hpair.2]
  · by_cases hy : fkIsingSquareSignedEighthTurn b (a + 4) = -4
    · exact False.elim (hyne hy)
    · simp [hy]
      omega

theorem fkIsingSquareOrientedPrincipalBondTurn_reverse
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareOrientedPrincipalBondTurn n hn
        (fkIsingSquareWiredBondMate n hn d) d =
      -fkIsingSquareOrientedPrincipalBondTurn n hn d
        (fkIsingSquareWiredBondMate n hn d) := by
  let f := fkIsingSquareWiredBondMate n hn d
  change fkIsingSquareOrientedPrincipalBondTurn n hn f d =
    -fkIsingSquareOrientedPrincipalBondTurn n hn d f
  have hturn := fkIsingSquareWiredBondMate_turn_ne n hn d
  have hturn' : (fkIsingSquareSideCorner f.2).2 ≠
      (fkIsingSquareSideCorner d.2).2 := by simpa only [f] using hturn
  cases hd : (fkIsingSquareSideCorner d.2).2 <;>
    cases hf : (fkIsingSquareSideCorner f.2).2
  · exact False.elim (hturn' (hf.trans hd.symm))
  · unfold fkIsingSquareOrientedPrincipalBondTurn
    dsimp only
    rw [hf, hd]
    simp only [reduceCtorEq, and_true, and_false, if_false, ↓reduceIte]
    have h := fkIsingSquareOrientedPrincipalTurn_reverse_ccw
      (fkIsingSquareWiredCarrierTangentCode n hn (.bond d))
      (fkIsingSquareWiredCarrierTangentCode n hn (.bond f))
    simpa only [neg_neg] using (congrArg Neg.neg h).symm
  · unfold fkIsingSquareOrientedPrincipalBondTurn
    dsimp only
    rw [hf, hd]
    simp only [reduceCtorEq, and_true, and_false, if_false, ↓reduceIte]
    have h := fkIsingSquareOrientedPrincipalTurn_reverse_cw
      (fkIsingSquareWiredCarrierTangentCode n hn (.bond d))
      (fkIsingSquareWiredCarrierTangentCode n hn (.bond f))
    simpa only [neg_neg] using (congrArg Neg.neg h).symm
  · exact False.elim (hturn' (hf.trans hd.symm))

private theorem fkIsingSquareWiredBoundaryForward_codes
    (n : Nat) (hn : 0 < n)
    {d f : FKIsingMedialDart (fkSquareBoxPlanar n)}
    (h : fkIsingSquareWiredBoundaryForward n hn d f) :
    (fkIsingSquareWiredDirectedTangentCode n hn (.bond d) = 9 ∧
        fkIsingSquareWiredDirectedTangentCode n hn (.bond f) = 3) ∨
      (fkIsingSquareWiredDirectedTangentCode n hn (.bond d) = 5 ∧
        fkIsingSquareWiredDirectedTangentCode n hn (.bond f) = 15) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨k, rfl, rfl⟩
  · left
    simp [fkIsingSquareWiredSourceDart, fkIsingSquareWiredTerminalDart]
  · right
    simp

private theorem fkIsingSquareWiredBoundaryForward_asymm
    (n : Nat) (hn : 0 < n)
    {d f : FKIsingMedialDart (fkSquareBoxPlanar n)}
    (h : fkIsingSquareWiredBoundaryForward n hn d f) :
    ¬ fkIsingSquareWiredBoundaryForward n hn f d := by
  intro hrev
  rcases fkIsingSquareWiredBoundaryForward_codes n hn h with h | h <;>
    rcases fkIsingSquareWiredBoundaryForward_codes n hn hrev with h' | h' <;>
    omega

theorem fkIsingSquareWiredBondTurn_reverse
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredBondTurn n hn
        (fkIsingSquareWiredBondMate n hn d) d =
      -fkIsingSquareWiredBondTurn n hn d
        (fkIsingSquareWiredBondMate n hn d) := by
  let f := fkIsingSquareWiredBondMate n hn d
  change fkIsingSquareWiredBondTurn n hn f d =
    -fkIsingSquareWiredBondTurn n hn d f
  by_cases hforward : fkIsingSquareWiredBoundaryForward n hn d f
  · have hnotReverse : ¬ fkIsingSquareWiredBoundaryReverse n hn d f :=
      fkIsingSquareWiredBoundaryForward_asymm n hn hforward
    have hnotForwardSwap : ¬ fkIsingSquareWiredBoundaryForward n hn f d :=
      fkIsingSquareWiredBoundaryForward_asymm n hn hforward
    have hreverseSwap : fkIsingSquareWiredBoundaryReverse n hn f d := hforward
    simp [fkIsingSquareWiredBondTurn, hforward, hnotReverse,
      hnotForwardSwap, hreverseSwap]
  · by_cases hreverse : fkIsingSquareWiredBoundaryReverse n hn d f
    · have hforwardSwap : fkIsingSquareWiredBoundaryForward n hn f d := hreverse
      have hnotReverseSwap : ¬ fkIsingSquareWiredBoundaryReverse n hn f d :=
        fkIsingSquareWiredBoundaryForward_asymm n hn hforwardSwap
      simp [fkIsingSquareWiredBondTurn, hforward, hreverse,
        hforwardSwap, hnotReverseSwap]
    · have hnotForwardSwap : ¬ fkIsingSquareWiredBoundaryForward n hn f d :=
        hreverse
      have hnotReverseSwap : ¬ fkIsingSquareWiredBoundaryReverse n hn f d :=
        hforward
      rw [fkIsingSquareWiredBondTurn, if_neg hnotForwardSwap,
        if_neg hnotReverseSwap, fkIsingSquareWiredBondTurn,
        if_neg hforward, if_neg hreverse]
      exact fkIsingSquareOrientedPrincipalBondTurn_reverse n hn d

theorem fkIsingSquareWired_bondMate_infix_explorationOrder
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
    (h : (.bond d : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationOrder n hn omega) :
    [(.bond d : FKIsingSquareWiredCarrier n),
        .bond (fkIsingSquareWiredBondMate n hn d)] <:+:
        fkIsingSquareWiredExplorationOrder n hn omega ∨
      [(.bond (fkIsingSquareWiredBondMate n hn d) :
          FKIsingSquareWiredCarrier n), .bond d] <:+:
        fkIsingSquareWiredExplorationOrder n hn omega := by
  have hadj : (fkIsingSquareWiredLoopGraph n hn omega).Adj (.bond d)
      (.bond (fkIsingSquareWiredBondMate n hn d)) := by
    right
    simp [fkIsingSquareWiredTransitionMate, hsource, hterminal]
  apply Walk.infix_support_iff_mem_edges.mpr
  exact fkIsingSquareWiredExplorationPath_mem_edges_of_adj n hn omega h hadj

theorem fkIsingSquareWiredRawTurnCount_bondMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
    (h : (.bond d : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationOrder n hn omega) :
    fkIsingSquareWiredRawTurnCount n hn omega
        (.bond (fkIsingSquareWiredBondMate n hn d)) =
      fkIsingSquareWiredRawTurnCount n hn omega (.bond d) +
        fkIsingSquareWiredBondTurn n hn d
          (fkIsingSquareWiredBondMate n hn d) := by
  let p := fkIsingSquareWiredExplorationOrder n hn omega
  let x : FKIsingSquareWiredCarrier n := .bond d
  let y : FKIsingSquareWiredCarrier n :=
    .bond (fkIsingSquareWiredBondMate n hn d)
  have hxy := fkIsingSquareWired_bondMate_infix_explorationOrder
    n hn omega d hsource hterminal h
  have hx : x ∈ p := by simpa [x, p] using h
  have hy : y ∈ p := hxy.elim
    (fun hf ↦ hf.mem (by simp [y]))
    (fun hb ↦ hb.mem (by simp [y]))
  have hix : p.idxOf x < p.length := List.idxOf_lt_length_iff.mpr hx
  have hiy : p.idxOf y < p.length := List.idxOf_lt_length_iff.mpr hy
  rcases hxy with hf | hb
  · have hi := idxOf_succ_of_pair_infix_nodup
        (fkIsingSquareWiredExplorationOrder_nodup n hn omega) hf
    have hs := fkIsingSquareWiredRawTurnCount_succ n hn omega (p.idxOf x)
      (by rw [← hi]; exact hiy)
    simpa only [p, x, y, List.getElem_idxOf hix, ← hi,
      List.getElem_idxOf hiy, fkIsingSquareWiredTransitionTurn] using hs
  · have hi := idxOf_succ_of_pair_infix_nodup
        (fkIsingSquareWiredExplorationOrder_nodup n hn omega) hb
    have hs := fkIsingSquareWiredRawTurnCount_succ n hn omega (p.idxOf y)
      (by rw [← hi]; exact hix)
    have hreverse := fkIsingSquareWiredBondTurn_reverse n hn d
    have hs0 : fkIsingSquareWiredRawTurnCount n hn omega x =
        fkIsingSquareWiredRawTurnCount n hn omega y +
          fkIsingSquareWiredBondTurn n hn
            (fkIsingSquareWiredBondMate n hn d) d := by
      simpa only [p, x, y, List.getElem_idxOf hiy, ← hi,
        List.getElem_idxOf hix, fkIsingSquareWiredTransitionTurn] using hs
    rw [hreverse] at hs0
    have hfinal : fkIsingSquareWiredRawTurnCount n hn omega y =
        fkIsingSquareWiredRawTurnCount n hn omega x +
          fkIsingSquareWiredBondTurn n hn d
            (fkIsingSquareWiredBondMate n hn d) := by omega
    simpa only [x, y] using hfinal

theorem fkIsingSquareWiredLiftedWinding_bondMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
    (h : (.bond d : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationOrder n hn omega) :
    fkIsingSquareWiredLiftedWinding n hn omega
        (.bond (fkIsingSquareWiredBondMate n hn d)) =
      fkIsingSquareWiredLiftedWinding n hn omega (.bond d) +
        (fkIsingSquareWiredBondTurn n hn d
          (fkIsingSquareWiredBondMate n hn d) : Real) * (Real.pi / 4) := by
  simp only [fkIsingSquareWiredLiftedWinding,
    fkIsingSquareWiredPhysicalTurnCount,
    fkIsingSquareWiredRawTurnCount_bondMate n hn omega d
      hsource hterminal h]
  push_cast
  ring

theorem fkIsingSquareWired_bondMate_mem_trace_iff
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    (.bond (fkIsingSquareWiredBondMate n hn d) :
        FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn omega ↔
      (.bond d : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn omega := by
  rw [mem_fkIsingSquareWiredExplorationTrace_iff,
    mem_fkIsingSquareWiredExplorationTrace_iff]
  have hadj : (fkIsingSquareWiredLoopGraph n hn omega).Adj (.bond d)
      (.bond (fkIsingSquareWiredBondMate n hn d)) := by
    right
    simp [fkIsingSquareWiredTransitionMate, hsource, hterminal]
  exact ⟨fun h ↦ h.trans hadj.symm.reachable,
    fun h ↦ h.trans hadj.reachable⟩

def fkIsingSquareWiredBondPhase
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) : Complex :=
  Complex.exp (Complex.I *
    ((((fkIsingSquareWiredBondTurn n hn d
      (fkIsingSquareWiredBondMate n hn d) : Int) : Real) *
        (Real.pi / 8) : Real) : Complex))

theorem fkIsingSquareWiredBondPhase_normSq
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    Complex.normSq (fkIsingSquareWiredBondPhase n hn d) = 1 := by
  rw [Complex.normSq_eq_norm_sq, fkIsingSquareWiredBondPhase,
    Complex.norm_exp]
  simp

theorem fkIsingSquareWired_fermionicSummand_bondMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand omega
        (.bond (fkIsingSquareWiredBondMate n hn d)) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand omega
          (.bond d) * fkIsingSquareWiredBondPhase n hn d := by
  let D := fkIsingSquareWiredDobrushinDomain n hn
  have hmem := fkIsingSquareWired_bondMate_mem_trace_iff
    n hn omega d hsource hterminal
  by_cases hd : (.bond d : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationTrace n hn omega
  · have hf := hmem.mpr hd
    have horder : (.bond d : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationOrder n hn omega := by
      rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      exact hd
    have hwind := fkIsingSquareWiredLiftedWinding_bondMate
      n hn omega d hsource hterminal horder
    simp only [FKIsingDobrushinDomain.fermionicSummand, D,
      fkIsingSquareWiredDobrushinDomain, hf, hd, if_true,
      FKIsingDobrushinDomain.windingPhase]
    rw [hwind]
    unfold fkIsingSquareWiredBondPhase
    rw [show Complex.I *
          (((fkIsingSquareWiredLiftedWinding n hn omega (.bond d) +
              (fkIsingSquareWiredBondTurn n hn d
                (fkIsingSquareWiredBondMate n hn d) : Real) *
                  (Real.pi / 4)) / 2 : Real) : Complex) =
        Complex.I *
            ((fkIsingSquareWiredLiftedWinding n hn omega (.bond d) / 2 : Real) :
              Complex) +
          Complex.I *
            ((((fkIsingSquareWiredBondTurn n hn d
              (fkIsingSquareWiredBondMate n hn d) : Int) : Real) *
                (Real.pi / 8) : Real) : Complex) by push_cast; ring,
      Complex.exp_add]
    ring
  · have hf : (.bond (fkIsingSquareWiredBondMate n hn d) :
        FKIsingSquareWiredCarrier n) ∉
        fkIsingSquareWiredExplorationTrace n hn omega := by
      exact fun h ↦ hd (hmem.mp h)
    simp [FKIsingDobrushinDomain.fermionicSummand, D,
      fkIsingSquareWiredDobrushinDomain, hf, hd]

theorem fkIsingSquareWired_fermionicObservable_bondMate
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.bond (fkIsingSquareWiredBondMate n hn d)) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.bond d) *
        fkIsingSquareWiredBondPhase n hn d := by
  unfold FKIsingDobrushinDomain.fermionicObservable
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro omega _
  exact fkIsingSquareWired_fermionicSummand_bondMate
    n hn omega d hsource hterminal

theorem fkIsingSquareWiredPrimitiveIncrement_bondMate
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    fkIsingSquareWiredPrimitiveIncrement n hn
        (.bond (fkIsingSquareWiredBondMate n hn d)) =
      fkIsingSquareWiredPrimitiveIncrement n hn (.bond d) := by
  unfold fkIsingSquareWiredPrimitiveIncrement isingPrimitiveIncrement
  rw [fkIsingSquareWired_fermionicObservable_bondMate n hn d
    hsource hterminal, Complex.normSq_mul,
    fkIsingSquareWiredBondPhase_normSq, mul_one]



theorem fkIsingSquareWiredPrimitiveIncrement_bondDartMate
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    fkIsingSquareWiredPrimitiveIncrement n hn
        (.dart (fkIsingSquareWiredBondMate n hn d)) =
      fkIsingSquareWiredPrimitiveIncrement n hn (.dart d) := by
  rw [← fkIsingSquareWiredPrimitiveIncrement_incidence n hn
      (fkIsingSquareWiredBondMate n hn d),
    fkIsingSquareWiredPrimitiveIncrement_bondMate n hn d
      hsource hterminal,
    fkIsingSquareWiredPrimitiveIncrement_incidence]



theorem fkIsingSquareWiredPrimitiveIncrement_bond_local_closed
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredPrimitiveIncrement n hn (.bond (e, .west)) +
        fkIsingSquareWiredPrimitiveIncrement n hn (.bond (e, .east)) =
      fkIsingSquareWiredPrimitiveIncrement n hn (.bond (e, .south)) +
        fkIsingSquareWiredPrimitiveIncrement n hn (.bond (e, .north)) := by
  simp only [fkIsingSquareWiredPrimitiveIncrement_incidence]
  exact fkIsingSquareWiredPrimitiveIncrement_local_closed n hn e

end

end StatMech.Universality
