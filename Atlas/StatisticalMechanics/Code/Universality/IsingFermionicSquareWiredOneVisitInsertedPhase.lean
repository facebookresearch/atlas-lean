/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareWiredOneVisitSplice
import Code.Universality.IsingFermionicSquareWiredExhaustive










open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def carrierAdjacentSum {A : Type*} (f : A → A → Int) (l : List A) : Int :=
  (List.zipWith f l l.tail).sum

@[simp] theorem carrierAdjacentSum_nil {A : Type*} (f : A → A → Int) :
    carrierAdjacentSum f [] = 0 := rfl

@[simp] theorem carrierAdjacentSum_singleton {A : Type*} (f : A → A → Int)
    (a : A) : carrierAdjacentSum f [a] = 0 := rfl

@[simp] theorem carrierAdjacentSum_cons_cons {A : Type*} (f : A → A → Int)
    (a b : A) (l : List A) :
    carrierAdjacentSum f (a :: b :: l) = f a b + carrierAdjacentSum f (b :: l) := by
  simp [carrierAdjacentSum]

theorem carrierAdjacentSum_append_cons {A : Type*} (f : A → A → Int)
    (l : List A) (a b : A) (r : List A) :
    carrierAdjacentSum f (l ++ a :: b :: r) =
      carrierAdjacentSum f (l ++ [a]) + f a b + carrierAdjacentSum f (b :: r) := by
  induction l with
  | nil => simp
  | cons x l ih =>
      cases l with
      | nil => simp [add_assoc]
      | cons y l =>
          simp only [List.cons_append, carrierAdjacentSum_cons_cons]
          change carrierAdjacentSum f (y :: (l ++ a :: b :: r)) =
            carrierAdjacentSum f (y :: (l ++ [a])) + f a b +
              carrierAdjacentSum f (b :: r) at ih
          rw [ih]
          omega

theorem carrierAdjacentSum_append {A : Type*} (f : A → A → Int)
    (l r : List A) (hl : l ≠ []) (hr : r ≠ []) :
    carrierAdjacentSum f (l ++ r) =
      carrierAdjacentSum f l + f (l.getLast hl) (r.head hr) +
        carrierAdjacentSum f r := by
  let a := l.getLast hl
  let b := r.head hr
  have hlEq : l.dropLast ++ [a] = l := by
    simpa only [a] using List.dropLast_append_getLast hl
  have hrEq : b :: r.tail = r := by
    simpa only [b] using List.cons_head_tail hr
  calc
    carrierAdjacentSum f (l ++ r) =
        carrierAdjacentSum f (l.dropLast ++ a :: b :: r.tail) := by
      conv_lhs => rw [← hlEq, ← hrEq]
      simp only [List.append_assoc, List.singleton_append]
    _ = carrierAdjacentSum f (l.dropLast ++ [a]) + f a b +
        carrierAdjacentSum f (b :: r.tail) :=
      carrierAdjacentSum_append_cons f l.dropLast a b r.tail
    _ = carrierAdjacentSum f l + f (l.getLast hl) (r.head hr) +
        carrierAdjacentSum f r := by rw [hlEq, hrEq]

theorem wiredTurnSteps_drop_sum_eq_adjacentSum
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n) :
    ((fkIsingSquareWiredExplorationTurnSteps n hn omega).drop
      ((fkIsingSquareWiredExplorationOrder n hn omega).idxOf z)).sum =
    carrierAdjacentSum
      (fkIsingSquareWiredTransitionTurn n hn omega)
      ((fkIsingSquareWiredExplorationOrder n hn omega).drop
        ((fkIsingSquareWiredExplorationOrder n hn omega).idxOf z)) := by
  simp only [fkIsingSquareWiredExplorationTurnSteps, carrierAdjacentSum,
    List.drop_zipWith]
  rw [List.drop_tail, List.tail_drop]



theorem FKIsingDobrushinDomain.windingPhase_eq_of_winding_eq_add_four_pi_mul_int
    {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]
    (D : FKIsingDobrushinDomain P M)
    (omega omega' : ConfigSpace (Sym2 P.V)) (e e' : M) (k : Int)
    (h : D.winding omega' e' =
      D.winding omega e + (k : Real) * (4 * Real.pi)) :
    D.windingPhase omega' e' = D.windingPhase omega e := by
  unfold FKIsingDobrushinDomain.windingPhase
  rw [h]
  have hexponent :
      Complex.I *
          ((((D.winding omega e + (k : Real) * (4 * Real.pi)) / 2 : Real)) :
            Complex) =
        (k : Complex) * (2 * (Real.pi : Complex) * Complex.I) +
          Complex.I * (((D.winding omega e / 2 : Real)) : Complex) := by
    push_cast
    ring
  rw [hexponent, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, one_mul]




theorem int_eighth_turn_mod_sixteen_of_exp_eq_neg_one (turn : Int)
    (hphase : Complex.exp
      (((((turn : Real) * (Real.pi / 8) : Real) : Complex) * Complex.I)) = -1) :
    turn ≡ 8 [ZMOD 16] := by
  rw [← Complex.exp_pi_mul_I] at hphase
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hphase
  have him := congrArg Complex.im hk
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero,
    Complex.add_im] at him
  norm_num at him
  have hturnR : (turn : Real) = 8 + 16 * (k : Real) := by
    field_simp at him
    nlinarith [Real.pi_pos]
  have hturn : turn = 8 + 16 * k := by
    exact_mod_cast hturnR
  rw [Int.modEq_iff_dvd]
  refine ⟨-k, ?_⟩
  omega

theorem fkIsingSquareWired_one_visit_west_inserted_phase_of_cycle_turn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hcycle : ∀ (r : ((fkIsingSquareWiredLoopGraph n hn
        (setClosed e.1 omega)).deleteEdges
          {s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west)),
            s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east))}).Walk
              (.dart (e, .east)) (.dart (e, .north))),
      r.IsPath →
      List.Disjoint
        (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega))
        r.support →
      carrierAdjacentSum
          (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support +
          fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)
            (.dart (e, .north)) (.dart (e, .east)) ≡ 8 [ZMOD 16]) :
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setOpen e.1 omega) (.dart (e, .south)) =
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setClosed e.1 omega) (.dart (e, .south)) := by
  classical
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let pClosed := fkIsingSquareWiredExplorationOrder n hn
    (setClosed e.1 omega)
  let pOpen := fkIsingSquareWiredExplorationOrder n hn
    (setOpen e.1 omega)
  let turnOpen := fkIsingSquareWiredTransitionTurn n hn
    (setOpen e.1 omega)
  obtain ⟨r, hr, hdisjoint, hsplice⟩ :=
    fkIsingSquareWired_one_visit_west_open_splice_support
      n hn omega e hwest heast
  have hSW := fkIsingSquareWired_closed_south_west_oriented_infix
    n hn omega e hwest
  have hS : S ∈ pClosed := by
    simpa only [S, pClosed] using hSW.mem (by simp)
  have hW : W ∈ pClosed := by
    simpa only [W, pClosed] using hSW.mem (by simp)
  have hiSW := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn
      (setClosed e.1 omega)) hSW
  change pClosed.idxOf W = pClosed.idxOf S + 1 at hiSW
  have hEClosed : E ∉ pClosed := by
    simpa only [E, pClosed, fkIsingSquareWiredPathUsesLocalSide] using heast
  have hWOpen : W ∈ pOpen := by
    rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    apply fkIsingSquareWired_open_local_mem_of_closed_west_mem_not_east
      n hn omega e
    · rw [← mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      simpa only [W, pClosed] using hW
    · intro hE
      apply hEClosed
      rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      simpa only [E] using hE
  have hEOpen : E ∈ pOpen := by
    rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    apply fkIsingSquareWired_open_local_mem_of_closed_west_mem_not_east
      n hn omega e
    · rw [← mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      simpa only [W, pClosed] using hW
    · intro hE
      apply hEClosed
      rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      simpa only [E] using hE
  let pre := pClosed.take (pClosed.idxOf S + 1)
  let suffix := pClosed.drop (pClosed.idxOf W)
  have hsplice' : pOpen = pre ++ r.support ++ suffix := by
    simpa only [pOpen, pClosed, pre, suffix, S, W] using hsplice
  have hrHead : r.support = E :: r.support.tail := by
    simpa only [E] using r.cons_tail_support.symm
  have hsuffix : suffix = W :: pClosed.drop (pClosed.idxOf W + 1) := by
    have hWlt : pClosed.idxOf W < pClosed.length :=
      List.idxOf_lt_length_iff.mpr hW
    simp only [suffix]
    rw [List.drop_eq_getElem_cons hWlt, List.getElem_idxOf hWlt]
  have hEnotPre : E ∉ pre := by
    exact fun h => hEClosed ((List.take_sublist _ _).subset h)
  have hopenDropE : pOpen.drop (pOpen.idxOf E) = r.support ++ suffix := by
    rw [hsplice', hrHead]
    simp only [List.append_assoc, List.cons_append]
    rw [List.idxOf_append, if_neg hEnotPre, List.idxOf_cons_self,
      zero_add, List.drop_left]
  have hWnotPre : W ∉ pre := by
    simp only [pre]
    rw [List.mem_take_iff_idxOf_lt hW]
    omega
  have hWnotR : W ∉ r.support := fun h => hdisjoint hW h
  have hWnotPreR : W ∉ pre ++ r.support := by
    simpa only [List.mem_append, not_or] using And.intro hWnotPre hWnotR
  have hspliceW : pOpen = (pre ++ r.support) ++ suffix := by
    exact hsplice'
  have hopenDropW : pOpen.drop (pOpen.idxOf W) = suffix := by
    rw [hspliceW, hsuffix]
    rw [List.idxOf_append, if_neg hWnotPreR, List.idxOf_cons_self,
      zero_add, List.drop_left]
  have hsumE := wiredTurnSteps_drop_sum_eq_adjacentSum
    n hn (setOpen e.1 omega) E
  have hsumW := wiredTurnSteps_drop_sum_eq_adjacentSum
    n hn (setOpen e.1 omega) W
  rw [show fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega) = pOpen
    from rfl, hopenDropE] at hsumE
  rw [show fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega) = pOpen
    from rfl, hopenDropW] at hsumW
  have hrne : r.support ≠ [] := r.support_ne_nil
  have hsufne : suffix ≠ [] := by rw [hsuffix]; simp
  have happend := carrierAdjacentSum_append turnOpen r.support suffix hrne hsufne
  have hrLast : r.support.getLast hrne = N := r.getLast_support
  have hsufHeadOpt : suffix.head? = some W := by rw [hsuffix]; rfl
  rw [List.head?_eq_some_head hsufne] at hsufHeadOpt
  have hsufHead : suffix.head hsufne = W := Option.some.inj hsufHeadOpt
  rw [hrLast, hsufHead] at happend
  have hturnArc := hcycle r hr hdisjoint
  have hlocal := fkIsingSquareWiredTransitionTurn_local_table n hn omega e
  have hclosedNE : fkIsingSquareWiredTransitionTurn n hn
      (setClosed e.1 omega) N E = 2 := by
    simpa only [N, E] using hlocal.2.2.2.1
  have hopenNW : turnOpen N W = -2 := by
    simpa only [turnOpen, N, W] using hlocal.2.2.2.2.2.1
  have hwindE := fkIsingSquareWiredLiftedWinding_eq_neg_suffix_sum
    n hn (setOpen e.1 omega) E hEOpen
  have hwindW := fkIsingSquareWiredLiftedWinding_eq_neg_suffix_sum
    n hn (setOpen e.1 omega) W hWOpen
  change fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega) E =
    -(((fkIsingSquareWiredExplorationTurnSteps n hn
      (setOpen e.1 omega)).drop (pOpen.idxOf E)).sum : Real) *
      (Real.pi / 4) at hwindE
  rw [hsumW] at hwindW
  change fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega) W =
    -((carrierAdjacentSum turnOpen suffix : Int) : Real) *
      (Real.pi / 4) at hwindW
  rw [hsumE, happend] at hwindE
  have hopenSE := fkIsingSquareWired_open_east_south_winding
    n hn omega e (by
      simpa only [fkIsingSquareWiredPathUsesLocalSide, E, pOpen] using hEOpen)
  have hclosedSW := fkIsingSquareWired_closed_west_south_winding
    n hn omega e hwest
  have hwindWsame := fkIsingSquareWired_one_visit_west_winding
    n hn omega e hwest heast
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hturnArc
  change 8 - (carrierAdjacentSum turnOpen r.support +
    fkIsingSquareWiredTransitionTurn n hn
      (setClosed e.1 omega) N E) = 16 * k at hk
  rw [hclosedNE] at hk
  have harc : carrierAdjacentSum turnOpen r.support = 6 - 16 * k := by
    omega
  have hwindS : fkIsingSquareWiredLiftedWinding n hn
      (setOpen e.1 omega) S =
    fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega) S +
      (k : Real) * (4 * Real.pi) := by
    rw [harc, hopenNW] at hwindE
    dsimp only [S, E, W] at hopenSE hclosedSW hwindWsame hwindE hwindW
    norm_num at hwindE hwindW
    linarith
  exact FKIsingDobrushinDomain.windingPhase_eq_of_winding_eq_add_four_pi_mul_int
    (fkIsingSquareWiredDobrushinDomain n hn)
    (setClosed e.1 omega) (setOpen e.1 omega) S S k (by
      simpa only [S, fkIsingSquareWiredDobrushinDomain] using hwindS)

theorem fkIsingSquareWired_one_visit_east_inserted_phase_of_cycle_turn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hcycle : ∀ (r : ((fkIsingSquareWiredLoopGraph n hn
        (setClosed e.1 omega)).deleteEdges
          {s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east)),
            s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west))}).Walk
              (.dart (e, .west)) (.dart (e, .south))),
      r.IsPath →
      List.Disjoint
        (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega))
        r.support →
      carrierAdjacentSum
          (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support +
          fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)
            (.dart (e, .south)) (.dart (e, .west)) ≡ 8 [ZMOD 16]) :
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setOpen e.1 omega) (.dart (e, .north)) =
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setClosed e.1 omega) (.dart (e, .north)) := by
  classical
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let pClosed := fkIsingSquareWiredExplorationOrder n hn
    (setClosed e.1 omega)
  let pOpen := fkIsingSquareWiredExplorationOrder n hn
    (setOpen e.1 omega)
  let turnOpen := fkIsingSquareWiredTransitionTurn n hn
    (setOpen e.1 omega)
  obtain ⟨r, hr, hdisjoint, hsplice⟩ :=
    fkIsingSquareWired_one_visit_east_open_splice_support
      n hn omega e hwest heast
  have hNE := fkIsingSquareWired_closed_north_east_oriented_infix
    n hn omega e heast
  have hN : N ∈ pClosed := by
    simpa only [N, pClosed] using hNE.mem (by simp)
  have hE : E ∈ pClosed := by
    simpa only [E, pClosed] using hNE.mem (by simp)
  have hiNE := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn
      (setClosed e.1 omega)) hNE
  change pClosed.idxOf E = pClosed.idxOf N + 1 at hiNE
  have hWClosed : W ∉ pClosed := by
    simpa only [W, pClosed, fkIsingSquareWiredPathUsesLocalSide] using hwest
  have hopenAll :=
    fkIsingSquareWired_open_local_mem_of_closed_east_mem_not_west
      n hn omega e (by
        rw [← mem_fkIsingSquareWiredExplorationOrder_iff_trace]
        simpa only [E, pClosed] using hE) (by
          intro hW
          apply hWClosed
          rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
          simpa only [W] using hW)
  have hWOpen : W ∈ pOpen := by
    rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    simpa only [W] using hopenAll .west
  have hEOpen : E ∈ pOpen := by
    rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    simpa only [E] using hopenAll .east
  let pre := pClosed.take (pClosed.idxOf N + 1)
  let suffix := pClosed.drop (pClosed.idxOf E)
  have hsplice' : pOpen = pre ++ r.support ++ suffix := by
    simpa only [pOpen, pClosed, pre, suffix, N, E] using hsplice
  have hrHead : r.support = W :: r.support.tail := by
    simpa only [W] using r.cons_tail_support.symm
  have hsuffix : suffix = E :: pClosed.drop (pClosed.idxOf E + 1) := by
    have hElt : pClosed.idxOf E < pClosed.length :=
      List.idxOf_lt_length_iff.mpr hE
    simp only [suffix]
    rw [List.drop_eq_getElem_cons hElt, List.getElem_idxOf hElt]
  have hWnotPre : W ∉ pre := by
    exact fun h => hWClosed ((List.take_sublist _ _).subset h)
  have hopenDropW : pOpen.drop (pOpen.idxOf W) = r.support ++ suffix := by
    rw [hsplice', hrHead]
    simp only [List.append_assoc, List.cons_append]
    rw [List.idxOf_append, if_neg hWnotPre, List.idxOf_cons_self,
      zero_add, List.drop_left]
  have hEnotPre : E ∉ pre := by
    simp only [pre]
    rw [List.mem_take_iff_idxOf_lt hE]
    omega
  have hEnotR : E ∉ r.support := fun h => hdisjoint hE h
  have hEnotPreR : E ∉ pre ++ r.support := by
    simpa only [List.mem_append, not_or] using And.intro hEnotPre hEnotR
  have hspliceE : pOpen = (pre ++ r.support) ++ suffix := hsplice'
  have hopenDropE : pOpen.drop (pOpen.idxOf E) = suffix := by
    rw [hspliceE, hsuffix]
    rw [List.idxOf_append, if_neg hEnotPreR, List.idxOf_cons_self,
      zero_add, List.drop_left]
  have hsumW := wiredTurnSteps_drop_sum_eq_adjacentSum
    n hn (setOpen e.1 omega) W
  have hsumE := wiredTurnSteps_drop_sum_eq_adjacentSum
    n hn (setOpen e.1 omega) E
  rw [show fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega) = pOpen
    from rfl, hopenDropW] at hsumW
  rw [show fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega) = pOpen
    from rfl, hopenDropE] at hsumE
  have hrne : r.support ≠ [] := r.support_ne_nil
  have hsufne : suffix ≠ [] := by rw [hsuffix]; simp
  have happend := carrierAdjacentSum_append turnOpen r.support suffix hrne hsufne
  have hrLast : r.support.getLast hrne = S := r.getLast_support
  have hsufHeadOpt : suffix.head? = some E := by rw [hsuffix]; rfl
  rw [List.head?_eq_some_head hsufne] at hsufHeadOpt
  have hsufHead : suffix.head hsufne = E := Option.some.inj hsufHeadOpt
  rw [hrLast, hsufHead] at happend
  have hturnArc := hcycle r hr hdisjoint
  have hlocal := fkIsingSquareWiredTransitionTurn_local_table n hn omega e
  have hclosedSW : fkIsingSquareWiredTransitionTurn n hn
      (setClosed e.1 omega) S W = 2 := by
    simpa only [S, W] using hlocal.2.1
  have hopenSE : turnOpen S E = -2 := by
    simpa only [turnOpen, S, E] using hlocal.2.2.2.2.2.2.2
  have hwindW := fkIsingSquareWiredLiftedWinding_eq_neg_suffix_sum
    n hn (setOpen e.1 omega) W hWOpen
  have hwindE := fkIsingSquareWiredLiftedWinding_eq_neg_suffix_sum
    n hn (setOpen e.1 omega) E hEOpen
  change fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega) W =
    -(((fkIsingSquareWiredExplorationTurnSteps n hn
      (setOpen e.1 omega)).drop (pOpen.idxOf W)).sum : Real) *
      (Real.pi / 4) at hwindW
  change fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega) E =
    -(((fkIsingSquareWiredExplorationTurnSteps n hn
      (setOpen e.1 omega)).drop (pOpen.idxOf E)).sum : Real) *
      (Real.pi / 4) at hwindE
  rw [hsumE] at hwindE
  change fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega) E =
    -((carrierAdjacentSum turnOpen suffix : Int) : Real) *
      (Real.pi / 4) at hwindE
  rw [hsumW, happend] at hwindW
  have hopenWN := fkIsingSquareWired_open_west_north_winding
    n hn omega e (by
      simpa only [fkIsingSquareWiredPathUsesLocalSide, W, pOpen] using hWOpen)
  have hclosedEN := fkIsingSquareWired_closed_east_north_winding
    n hn omega e heast
  have hwindEsame := fkIsingSquareWired_one_visit_east_winding
    n hn omega e hwest heast
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hturnArc
  change 8 - (carrierAdjacentSum turnOpen r.support +
    fkIsingSquareWiredTransitionTurn n hn
      (setClosed e.1 omega) S W) = 16 * k at hk
  rw [hclosedSW] at hk
  have harc : carrierAdjacentSum turnOpen r.support = 6 - 16 * k := by
    omega
  have hwindN : fkIsingSquareWiredLiftedWinding n hn
      (setOpen e.1 omega) N =
    fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega) N +
      (k : Real) * (4 * Real.pi) := by
    rw [harc, hopenSE] at hwindW
    dsimp only [N, W, E] at hopenWN hclosedEN hwindEsame hwindW hwindE
    norm_num at hwindW hwindE
    linarith
  exact FKIsingDobrushinDomain.windingPhase_eq_of_winding_eq_add_four_pi_mul_int
    (fkIsingSquareWiredDobrushinDomain n hn)
    (setClosed e.1 omega) (setOpen e.1 omega) N N k (by
      simpa only [N, fkIsingSquareWiredDobrushinDomain] using hwindN)



theorem fkIsingSquareWired_one_visit_west_inserted_phase_of_cycle_turn
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hcycle : ∀ (r : ((fkIsingSquareWiredLoopGraph n hn
        (setClosed e.1 omega)).deleteEdges
          {s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west)),
            s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east))}).Walk
              (.dart (e, .east)) (.dart (e, .north))),
      r.IsPath →
      List.Disjoint
        (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega))
        r.support →
      carrierAdjacentSum
          (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support +
          fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)
            (.dart (e, .north)) (.dart (e, .east)) = 8 ∨
      carrierAdjacentSum
          (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support +
          fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)
            (.dart (e, .north)) (.dart (e, .east)) = -8) :
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setOpen e.1 omega) (.dart (e, .south)) =
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setClosed e.1 omega) (.dart (e, .south)) := by
  apply fkIsingSquareWired_one_visit_west_inserted_phase_of_cycle_turn_mod_sixteen
    n hn omega e hwest heast
  intro r hr hdisjoint
  rcases hcycle r hr hdisjoint with hplus | hminus
  · rw [hplus]
  · rw [hminus]
    decide



theorem fkIsingSquareWired_one_visit_east_inserted_phase_of_cycle_turn
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hcycle : ∀ (r : ((fkIsingSquareWiredLoopGraph n hn
        (setClosed e.1 omega)).deleteEdges
          {s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east)),
            s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west))}).Walk
              (.dart (e, .west)) (.dart (e, .south))),
      r.IsPath →
      List.Disjoint
        (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega))
        r.support →
      carrierAdjacentSum
          (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support +
          fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)
            (.dart (e, .south)) (.dart (e, .west)) = 8 ∨
      carrierAdjacentSum
          (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support +
          fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)
            (.dart (e, .south)) (.dart (e, .west)) = -8) :
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setOpen e.1 omega) (.dart (e, .north)) =
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setClosed e.1 omega) (.dart (e, .north)) := by
  apply fkIsingSquareWired_one_visit_east_inserted_phase_of_cycle_turn_mod_sixteen
    n hn omega e hwest heast
  intro r hr hdisjoint
  rcases hcycle r hr hdisjoint with hplus | hminus
  · rw [hplus]
  · rw [hminus]
    decide

end
end StatMech.Universality
