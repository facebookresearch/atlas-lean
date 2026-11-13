/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKMedialBoundaryPermutation











open SimpleGraph Equiv

namespace StatMech.FrontierD

variable {T : EvenTorus}

set_option maxHeartbeats 800000 in



theorem fkMedial_boundary_sameCycle_of_walk
    (pairing : FKMedialLoopPairing T) {d e : FKMedialDart T}
    (p : (fkMedialLoopGraph T pairing).Walk d e)
    (hcolor : fkMedialCheckerColor d = fkMedialCheckerColor e) :
    (fkMedialBoundaryStep pairing).SameCycle d e := by
  induction n : p.length using Nat.strong_induction_on generalizing d e with
  | _ n ih =>
    subst n
    cases p with
    | nil => exact ⟨0, rfl⟩
    | @cons _ v _ hdv p' =>
      cases p' with
      | nil =>
          have hc := fkMedialLoopGraph_adj_checkerColor_ne T pairing hdv
          exact False.elim (hc hcolor)
      | @cons _ w _ hvw rest =>
          have hcdv := fkMedialLoopGraph_adj_checkerColor_ne T pairing hdv
          have hcvw := fkMedialLoopGraph_adj_checkerColor_ne T pairing hvw
          have hw : fkMedialCheckerColor w = fkMedialCheckerColor d := by
            generalize hd : fkMedialCheckerColor d = bd at hcdv hcolor ⊢
            generalize hv : fkMedialCheckerColor v = bv at hcdv hcvw
            generalize hwc : fkMedialCheckerColor w = bw at hcvw ⊢
            cases bd <;> cases bv <;> cases bw <;> simp_all
          have htail : (fkMedialBoundaryStep pairing).SameCycle w e :=
            ih rest.length (by simp only [Walk.length_cons]; omega)
              rest (hw.trans hcolor) rfl
          have htwo : (fkMedialBoundaryStep pairing).SameCycle d w := by
            rw [fkMedialLoopGraph_adj_iff] at hdv hvw
            rcases hdv with hdv | hdv <;> rcases hvw with hvw | hvw
            · have hdw : d = w := by
                rw [hvw, hdv, fkMedialLocalMate_involutive]
              exact hdw ▸ ⟨0, rfl⟩
            · have hdw : fkMedialBoundaryStep pairing d = w := by
                simp only [fkMedialBoundaryStep_apply]
                rw [hvw, hdv]
              refine ⟨1, ?_⟩
              simpa only [zpow_one] using hdw
            · have hdw : fkMedialBoundaryStep pairing w = d := by
                simp only [fkMedialBoundaryStep_apply]
                rw [hvw, fkMedialLocalMate_involutive, hdv,
                  fkMedialBondMate_involutive]
              apply Equiv.Perm.SameCycle.symm
              refine ⟨1, ?_⟩
              simpa only [zpow_one] using hdw
            · have hdw : d = w := by
                rw [hvw, hdv, fkMedialBondMate_involutive]
              exact hdw ▸ ⟨0, rfl⟩
          exact htwo.trans htail



theorem fkMedial_boundary_sameCycle_iff_reachable_of_color_eq
    (pairing : FKMedialLoopPairing T) (d e : FKMedialDart T)
    (hcolor : fkMedialCheckerColor d = fkMedialCheckerColor e) :
    (fkMedialBoundaryStep pairing).SameCycle d e ↔
      (fkMedialLoopGraph T pairing).Reachable d e := by
  constructor
  · intro hcycle
    obtain ⟨n, hn⟩ := hcycle.exists_nat_pow_eq
    have hreach := fkMedialBoundaryStep_iterate_reachable pairing d n
    rw [← Equiv.Perm.coe_pow] at hreach
    simpa only [hn] using hreach
  · rintro ⟨p⟩
    exact fkMedial_boundary_sameCycle_of_walk pairing p hcolor



@[simp] theorem fkMedialCheckerColor_west_eq_east (v : T.Vertex) :
    fkMedialCheckerColor (fkMedialWestDart v) =
      fkMedialCheckerColor (fkMedialEastDart v) := by
  rfl



theorem fkMedial_west_east_sameCycle_iff_reachable
    (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    (fkMedialBoundaryStep pairing).SameCycle
        (fkMedialWestDart v) (fkMedialEastDart v) ↔
      (fkMedialLoopGraph T pairing).Reachable
        (fkMedialWestDart v) (fkMedialEastDart v) :=
  fkMedial_boundary_sameCycle_iff_reachable_of_color_eq pairing _ _
    (fkMedialCheckerColor_west_eq_east v)


theorem fkMedial_west_east_reachable_iff_exists_boundary_iterate
    (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    (fkMedialLoopGraph T pairing).Reachable
        (fkMedialWestDart v) (fkMedialEastDart v) ↔
      ∃ n : Nat, (fkMedialBoundaryStep pairing)^[n]
        (fkMedialWestDart v) = fkMedialEastDart v := by
  rw [← fkMedial_west_east_sameCycle_iff_reachable pairing v]
  constructor
  · intro hcycle
    obtain ⟨n, hn⟩ := hcycle.exists_nat_pow_eq
    refine ⟨n, ?_⟩
    rwa [← Equiv.Perm.coe_pow]
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rwa [← Equiv.Perm.coe_pow] at hn

end StatMech.FrontierD
