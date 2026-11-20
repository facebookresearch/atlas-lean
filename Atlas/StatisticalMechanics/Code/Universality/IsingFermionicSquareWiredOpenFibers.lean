/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareWiredFullFaces
import Code.Universality.IsingFermionicSquareWiredExhaustive









open Finset SimpleGraph

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section



theorem fkIsingSquareWired_one_visit_separated
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hone :
      (fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega) e .west ∧
        ¬ fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega) e .east) ∨
      (¬ fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega) e .west ∧
        fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega) e .east)) :
    ¬ (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareOrientedEdge n e).tail
      (fkIsingSquareOrientedEdge n e).head :=
  fkIsingSquareWired_one_visit_separated_of_eulerDefect_eq
    n hn omega e hone (fkIsingSquareWiredEulerDefect_toggle_eq n hn omega e)


theorem fkIsingSquareWired_one_visit_gadget_separated
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hone :
      (fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega) e .west ∧
        ¬ fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega) e .east) ∨
      (¬ fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega) e .west ∧
        fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega) e .east)) :
    ¬ (fkIsingSquareLiftPhysicalGraph n
          (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega)) ⊔
        fkIsingSquareWiredExteriorGadget n).Reachable
      (.physical (fkIsingSquareOrientedEdge n e).tail)
      (.physical (fkIsingSquareOrientedEdge n e).head) := by
  have hsep := fkIsingSquareWired_one_visit_separated n hn omega e hone
  rw [FKIsingDobrushinDomain.wiring] at hsep
  intro hgadget
  exact hsep ((fkIsingSquare_openWiredExteriorGadget_reachable_iff n
    (setClosed e.1 omega) (fkIsingSquareOrientedEdge n e).tail
      (fkIsingSquareOrientedEdge n e).head).1 hgadget)


theorem fkIsingSquareWired_one_visit_west_contour_balance
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hopen : ∀ side, fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e side)
    (hphaseW : (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
      (setOpen e.1 omega) (.dart (e, .west)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .west)))
    (hphaseS : (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
      (setOpen e.1 omega) (.dart (e, .south)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .south))) :
    let D := fkIsingSquareWiredDobrushinDomain n hn
    let closed := setClosed e.1 omega
    let opened := setOpen e.1 omega
    let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
    let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
    let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
    let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
    (D.fermionicSummand closed W + D.fermionicSummand opened W) -
        (D.fermionicSummand closed E + D.fermionicSummand opened E) =
      Complex.I *
        ((D.fermionicSummand closed S + D.fermionicSummand opened S) -
          (D.fermionicSummand closed N + D.fermionicSummand opened N)) :=
  fkIsingSquareWired_one_visit_west_pointwise_contour_balance
    n hn omega e hwest heast hopen
      (fkIsingSquareWired_one_visit_gadget_separated n hn omega e
        (Or.inl ⟨hwest, heast⟩)) hphaseW hphaseS


theorem fkIsingSquareWired_one_visit_east_contour_balance
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hopen : ∀ side, fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e side)
    (hphaseE : (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
      (setOpen e.1 omega) (.dart (e, .east)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .east)))
    (hphaseN : (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
      (setOpen e.1 omega) (.dart (e, .north)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .north))) :
    let D := fkIsingSquareWiredDobrushinDomain n hn
    let closed := setClosed e.1 omega
    let opened := setOpen e.1 omega
    let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
    let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
    let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
    let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
    (D.fermionicSummand closed W + D.fermionicSummand opened W) -
        (D.fermionicSummand closed E + D.fermionicSummand opened E) =
      Complex.I *
        ((D.fermionicSummand closed S + D.fermionicSummand opened S) -
          (D.fermionicSummand closed N + D.fermionicSummand opened N)) :=
  fkIsingSquareWired_one_visit_east_pointwise_contour_balance
    n hn omega e hwest heast hopen
      (fkIsingSquareWired_one_visit_gadget_separated n hn omega e
        (Or.inr ⟨hwest, heast⟩)) hphaseE hphaseN

end

end StatMech.Universality
