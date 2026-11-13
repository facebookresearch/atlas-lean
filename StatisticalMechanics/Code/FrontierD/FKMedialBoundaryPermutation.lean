/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKMedialCheckerboard
import Code.FrontierA.PermCycleQuotientCount

open SimpleGraph Equiv

namespace StatMech.FrontierD

variable {T : EvenTorus}


def fkMedialLocalMateEquiv (pairing : FKMedialLoopPairing T) :
    FKMedialDart T ≃ FKMedialDart T where
  toFun := fkMedialLocalMate pairing
  invFun := fkMedialLocalMate pairing
  left_inv := fkMedialLocalMate_involutive pairing
  right_inv := fkMedialLocalMate_involutive pairing


def fkMedialBondMateEquiv (T : EvenTorus) :
    FKMedialDart T ≃ FKMedialDart T where
  toFun := fkMedialBondMate T
  invFun := fkMedialBondMate T
  left_inv := fkMedialBondMate_involutive T
  right_inv := fkMedialBondMate_involutive T



def fkMedialBoundaryStep (pairing : FKMedialLoopPairing T) :
    Perm (FKMedialDart T) :=
  (fkMedialLocalMateEquiv pairing).trans (fkMedialBondMateEquiv T)

@[simp] theorem fkMedialBoundaryStep_apply
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T) :
    fkMedialBoundaryStep pairing d =
      fkMedialBondMate T (fkMedialLocalMate pairing d) := rfl


theorem fkMedialCheckerColor_boundaryStep
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T) :
    fkMedialCheckerColor (fkMedialBoundaryStep pairing d) =
      fkMedialCheckerColor d := by
  have hlocal := fkMedialCheckerColor_localMate_ne pairing d
  have hbond := fkMedialCheckerColor_bondMate_ne T
    (fkMedialLocalMate pairing d)
  simp only [fkMedialBoundaryStep_apply] at hbond ⊢
  generalize hd : fkMedialCheckerColor d = bd at hlocal ⊢
  generalize hl : fkMedialCheckerColor
    (fkMedialLocalMate pairing d) = bl at hlocal hbond
  generalize hb : fkMedialCheckerColor
    (fkMedialBondMate T (fkMedialLocalMate pairing d)) = bb at hbond ⊢
  cases bd <;> cases bl <;> cases bb <;> simp_all



abbrev FKMedialBlackDart (T : EvenTorus) :=
  {d : FKMedialDart T // fkMedialCheckerColor d = false}


def fkMedialBlackBoundaryPerm (pairing : FKMedialLoopPairing T) :
    Perm (FKMedialBlackDart T) :=
  (fkMedialBoundaryStep pairing).subtypePerm fun d => by
    rw [fkMedialCheckerColor_boundaryStep]

@[simp] theorem fkMedialBlackBoundaryPerm_val
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    (fkMedialBlackBoundaryPerm pairing d).1 =
      fkMedialBondMate T (fkMedialLocalMate pairing d.1) := rfl



theorem fkMedialBlackBoundaryPerm_val_step
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    (fkMedialBlackBoundaryPerm pairing d).1 =
      fkMedialBoundaryStep pairing d.1 := rfl



theorem fkMedialBoundaryStep_reachable
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T) :
    (fkMedialLoopGraph T pairing).Reachable d
      (fkMedialBoundaryStep pairing d) := by
  apply (show (fkMedialLoopGraph T pairing).Adj d
      (fkMedialLocalMate pairing d) by
    rw [fkMedialLoopGraph_adj_iff]
    exact Or.inl rfl).reachable.trans
  apply (show (fkMedialLoopGraph T pairing).Adj
      (fkMedialLocalMate pairing d)
      (fkMedialBondMate T (fkMedialLocalMate pairing d)) by
    rw [fkMedialLoopGraph_adj_iff]
    exact Or.inr rfl).reachable



theorem fkMedialBoundaryStep_iterate_reachable
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T) (n : Nat) :
    (fkMedialLoopGraph T pairing).Reachable d
      ((fkMedialBoundaryStep pairing)^[n] d) := by
  induction n generalizing d with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact (fkMedialBoundaryStep_reachable pairing d).trans
        (ih (d := fkMedialBoundaryStep pairing d))

theorem fkMedialBoundaryStep_iterate_ne_of_not_reachable
    (pairing : FKMedialLoopPairing T) {d e : FKMedialDart T}
    (hde : ¬ (fkMedialLoopGraph T pairing).Reachable d e)
    (n : Nat) :
    (fkMedialBoundaryStep pairing)^[n] d ≠ e := by
  intro h
  apply hde
  simpa [h] using fkMedialBoundaryStep_iterate_reachable pairing d n



theorem fkMedial_reachable_of_blackBoundary_sameCycle
    (pairing : FKMedialLoopPairing T) (d e : FKMedialBlackDart T)
    (hde : (fkMedialBlackBoundaryPerm pairing).SameCycle d e) :
    (fkMedialLoopGraph T pairing).Reachable d.1 e.1 := by
  obtain ⟨n, hn⟩ := hde.exists_nat_pow_eq
  have hpow : ∀ n : Nat,
      (fkMedialLoopGraph T pairing).Reachable d.1
        (((fkMedialBlackBoundaryPerm pairing) ^ n) d).1 := by
    intro n
    induction n with
    | zero => exact Reachable.refl _
    | succ n ih =>
        rw [pow_succ']
        change (fkMedialLoopGraph T pairing).Reachable d.1
          (fkMedialBlackBoundaryPerm pairing
            (((fkMedialBlackBoundaryPerm pairing) ^ n) d)).1
        exact ih.trans (fkMedialBoundaryStep_reachable pairing _)
  simpa only [hn] using hpow n

set_option maxHeartbeats 800000 in



theorem fkMedial_blackBoundary_sameCycle_of_walk
    (pairing : FKMedialLoopPairing T) {d e : FKMedialDart T}
    (p : (fkMedialLoopGraph T pairing).Walk d e)
    (hd : fkMedialCheckerColor d = false)
    (he : fkMedialCheckerColor e = false) :
    (fkMedialBlackBoundaryPerm pairing).SameCycle
      ⟨d, hd⟩ ⟨e, he⟩ := by
  induction n : p.length using Nat.strong_induction_on generalizing d e with
  | _ n IH =>
    subst n
    cases p with
    | nil => exact ⟨0, rfl⟩
    | @cons _ v _ hdv p' =>
      cases p' with
      | nil =>
          have hc := fkMedialLoopGraph_adj_checkerColor_ne T pairing hdv
          exact False.elim (hc (hd.trans he.symm))
      | @cons _ w _ hvw rest =>
          have hcdv := fkMedialLoopGraph_adj_checkerColor_ne T pairing hdv
          have hcvw := fkMedialLoopGraph_adj_checkerColor_ne T pairing hvw
          have hw : fkMedialCheckerColor w = false := by
            generalize hv : fkMedialCheckerColor v = bv at hcdv hcvw
            generalize hwc : fkMedialCheckerColor w = bw at hcvw ⊢
            cases bv <;> cases bw <;> simp_all
          have htail :
              (fkMedialBlackBoundaryPerm pairing).SameCycle
                ⟨w, hw⟩ ⟨e, he⟩ :=
            IH rest.length (by simp only [Walk.length_cons]; omega)
              rest hw he rfl
          have htwo :
              (fkMedialBlackBoundaryPerm pairing).SameCycle
                ⟨d, hd⟩ ⟨w, hw⟩ := by
            rw [fkMedialLoopGraph_adj_iff] at hdv hvw
            rcases hdv with hdv | hdv <;> rcases hvw with hvw | hvw
            · have hdw : d = w := by
                rw [hvw, hdv, fkMedialLocalMate_involutive]
              exact (Subtype.ext hdw).sameCycle _
            · have hdw :
                (fkMedialBlackBoundaryPerm pairing ⟨d, hd⟩).1 = w := by
                simp only [fkMedialBlackBoundaryPerm_val]
                rw [hvw, hdv]
              refine ⟨1, ?_⟩
              apply Subtype.ext
              simpa only [zpow_one] using hdw
            · have hdw :
                (fkMedialBlackBoundaryPerm pairing ⟨w, hw⟩).1 = d := by
                simp only [fkMedialBlackBoundaryPerm_val]
                rw [hvw, fkMedialLocalMate_involutive, hdv,
                  fkMedialBondMate_involutive]
              apply Equiv.Perm.SameCycle.symm
              refine ⟨1, ?_⟩
              apply Subtype.ext
              simpa only [zpow_one] using hdw
            · have hdw : d = w := by
                rw [hvw, hdv, fkMedialBondMate_involutive]
              exact (Subtype.ext hdw).sameCycle _
          exact htwo.trans htail

theorem fkMedial_blackBoundary_sameCycle_iff_reachable
    (pairing : FKMedialLoopPairing T) (d e : FKMedialBlackDart T) :
    (fkMedialBlackBoundaryPerm pairing).SameCycle d e ↔
      (fkMedialLoopGraph T pairing).Reachable d.1 e.1 := by
  constructor
  · exact fkMedial_reachable_of_blackBoundary_sameCycle pairing d e
  · rintro ⟨p⟩
    exact fkMedial_blackBoundary_sameCycle_of_walk pairing p d.2 e.2



noncomputable def fkMedialBlackBoundaryCycleToLoop
    (pairing : FKMedialLoopPairing T) :
    StatMech.FrontierA.PermCycleClass
        (fkMedialBlackBoundaryPerm pairing) →
      (fkMedialLoopGraph T pairing).ConnectedComponent := by
  classical
  exact Quot.lift
    (fun d : FKMedialBlackDart T =>
      (fkMedialLoopGraph T pairing).connectedComponentMk d.1)
    (fun d e hde => SimpleGraph.ConnectedComponent.sound
      ((fkMedial_blackBoundary_sameCycle_iff_reachable pairing d e).1 hde))

theorem fkMedialBlackBoundaryCycleToLoop_bijective
    (pairing : FKMedialLoopPairing T) :
    Function.Bijective (fkMedialBlackBoundaryCycleToLoop pairing) := by
  classical
  constructor
  · intro A B hAB
    induction A using Quot.ind with
    | _ d =>
      induction B using Quot.ind with
      | _ e =>
        apply Quot.sound
        apply (fkMedial_blackBoundary_sameCycle_iff_reachable pairing d e).2
        apply SimpleGraph.ConnectedComponent.exact
        exact hAB
  · intro C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | _ d =>
      by_cases hd : fkMedialCheckerColor d = false
      · refine ⟨Quot.mk _ (⟨d, hd⟩ : FKMedialBlackDart T), rfl⟩
      · have hlocal : fkMedialCheckerColor
            (fkMedialLocalMate pairing d) = false := by
          have hne := fkMedialCheckerColor_localMate_ne pairing d
          generalize hc : fkMedialCheckerColor d = c at hd hne
          generalize hl : fkMedialCheckerColor
            (fkMedialLocalMate pairing d) = l at hne ⊢
          cases c <;> cases l <;> simp_all
        let b : FKMedialBlackDart T :=
          ⟨fkMedialLocalMate pairing d, hlocal⟩
        refine ⟨Quot.mk _ b, ?_⟩
        apply SimpleGraph.ConnectedComponent.sound
        exact (show (fkMedialLoopGraph T pairing).Adj
            (fkMedialLocalMate pairing d) d by
          rw [fkMedialLoopGraph_adj_iff]
          left
          rw [fkMedialLocalMate_involutive]).reachable



theorem permCycleCount_fkMedialBlackBoundaryPerm
    (pairing : FKMedialLoopPairing T) :
    StatMech.FrontierA.permCycleCount
        (fkMedialBlackBoundaryPerm pairing) =
      fkMedialLoopCount T pairing := by
  classical
  rw [← StatMech.FrontierA.natCard_permCycleClass]
  unfold fkMedialLoopCount
  exact Nat.card_congr (Equiv.ofBijective
    (fkMedialBlackBoundaryCycleToLoop pairing)
    (fkMedialBlackBoundaryCycleToLoop_bijective pairing))

end StatMech.FrontierD
