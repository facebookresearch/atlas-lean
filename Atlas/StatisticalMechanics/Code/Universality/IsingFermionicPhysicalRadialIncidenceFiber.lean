/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalRadialIncidence









namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

private theorem fkIsingSquareDirectionDart_congr_endpoint
    (n : Nat) (u v : (fkSquareBoxPlanar n).V)
    {d e : FKIsingSquareDirection} (huv : u = v) (hde : d = e)
    (hd : fkIsingSquareDirectionAvailable n u d)
    (he : fkIsingSquareDirectionAvailable n v e)
    (turn : FKIsingSquareCornerTurn) :
    fkIsingSquareDirectionDart n u d hd turn =
      fkIsingSquareDirectionDart n v e he turn := by
  subst v
  exact fkIsingSquareDirectionDart_congr n u hde hd he turn

theorem fkIsingSquareInteriorRadialDart_eq_or_bondMate_of_endpoint_faceKey
    (n : Nat) (hn : 0 < n)
    (d f : FKIsingSquareInteriorRadialDart n)
    (hend : fkIsingSquareDartEndpoint n d.1 =
      fkIsingSquareDartEndpoint n f.1)
    (hface : fkIsingSquareWedgeFaceKey n d.1 =
      fkIsingSquareWedgeFaceKey n f.1) :
    d.1 = f.1 ∨ fkIsingSquareBondMate n hn d.1 = f.1 := by
  have hdrec := fkIsingSquareDirectionDart_reconstruct n d.1
  have hfrec := fkIsingSquareDirectionDart_reconstruct n f.1
  by_cases hsame :
      fkIsingSquareDartDirection n d.1 = fkIsingSquareDartDirection n f.1 ∧
        (fkIsingSquareSideCorner d.1.2).2 =
          (fkIsingSquareSideCorner f.1.2).2
  · left
    rw [← hdrec, ← hfrec, hsame.2]
    exact fkIsingSquareDirectionDart_congr_endpoint
      n _ _ hend hsame.1 _ _ _
  generalize hdd : fkIsingSquareDartDirection n d.1 = dd at hface
  generalize hdt : (fkIsingSquareSideCorner d.1.2).2 = dt at hface
  generalize hfd : fkIsingSquareDartDirection n f.1 = fd at hface
  generalize hft : (fkIsingSquareSideCorner f.1.2).2 = ft at hface
  cases dd <;> cases dt <;> cases fd <;> cases ft <;>
    simp only [fkIsingSquareWedgeFaceKey, hdd, hdt, hfd, hft, hend] at hface <;>
    try { exfalso; apply hsame; constructor <;> simp_all } <;>
    try { exfalso; have := congrArg Prod.fst hface; have := congrArg Prod.snd hface; omega } <;>
    try { left; rw [← hdrec, ← hfrec, hdd, hdt, hfd, hft, hend] }
  all_goals
    have hfavailableD : fkIsingSquareDirectionAvailable n
        (fkIsingSquareDartEndpoint n d.1)
        (fkIsingSquareDartDirection n f.1) := by
      rw [hend]
      exact fkIsingSquareDartDirection_available n f.1
    simp only [hfd] at hfavailableD
    right
    rw [← hfrec]
    simp only [fkIsingSquareBondMate, hdt, hft]
    apply fkIsingSquareDirectionDart_congr_endpoint n _ _ hend
    simp [hdd, hfd, fkIsingSquareNextDirection,
      fkIsingSquarePreviousDirection, hfavailableD]

theorem fkIsingSquareInteriorRadialIncidence_ext
    (n : Nat) (hn : 0 < n)
    (e f : FKIsingSquareInteriorRadialIncidence n hn)
    (hend : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareInteriorRadialEndpoint n hn f)
    (hface : fkIsingSquareInteriorRadialFaceKey n hn e =
      fkIsingSquareInteriorRadialFaceKey n hn f) : e = f := by
  induction e using Quot.ind with
  | _ d =>
      induction f using Quot.ind with
      | _ f =>
          rw [fkIsingSquareInteriorRadialEndpoint_mk,
            fkIsingSquareInteriorRadialEndpoint_mk] at hend
          rw [fkIsingSquareInteriorRadialFaceKey_mk,
            fkIsingSquareInteriorRadialFaceKey_mk] at hface
          rcases
              fkIsingSquareInteriorRadialDart_eq_or_bondMate_of_endpoint_faceKey
                n hn d f hend hface with h | h
          · congr 2
            exact Subtype.ext h
          · apply Quot.sound
            have hcycle :=
              (Equiv.Perm.SameCycle.rfl :
                (fkIsingSquareInteriorRadialBondPerm n hn).SameCycle d d).apply_right
            have hstep : fkIsingSquareInteriorRadialBondPerm n hn d = f := by
              apply Subtype.ext
              change fkIsingSquareWiredBondMate n hn d.1 = f.1
              rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior
                n hn d.1 d.2]
              exact h
            simpa only [hstep] using hcycle

theorem fkIsingSquareInteriorRadial_endpoint_faceKey_injective
    (n : Nat) (hn : 0 < n) :
    Function.Injective (fun e : FKIsingSquareInteriorRadialIncidence n hn ↦
      (fkIsingSquareInteriorRadialEndpoint n hn e,
        fkIsingSquareInteriorRadialFaceKey n hn e)) := by
  intro e f h
  exact fkIsingSquareInteriorRadialIncidence_ext
    n hn e f (congrArg Prod.fst h) (congrArg Prod.snd h)

end

end StatMech.Universality
