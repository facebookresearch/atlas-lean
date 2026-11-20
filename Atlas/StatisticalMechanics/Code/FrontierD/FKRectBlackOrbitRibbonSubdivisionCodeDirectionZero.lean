/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCode



namespace StatMech.FrontierD

open StatMech.Onsager
open StatMech.Onsager.BaseCase

noncomputable section

set_option maxHeartbeats 500000 in
theorem fkRectBlackOrbitRibbonSubdivisionCode_eq_of_directions_zero_zero
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (z w : FKRectBlackOrbitRibbonSubdivisionIndex R omega d)
    (hz : fkRectBlackOrbitMedialRibbonFlatDirection R omega d z.1 = 0)
    (hw : fkRectBlackOrbitMedialRibbonFlatDirection R omega d w.1 = 0)
    (h : fkRectBlackOrbitRibbonSubdivisionCode R omega d z =
      fkRectBlackOrbitRibbonSubdivisionCode R omega d w) :
    z = w := by
  rcases z with ⟨i, r⟩
  rcases w with ⟨j, s⟩
  change fkRectBlackOrbitMedialRibbonFlatDirection R omega d i = 0 at hz
  change fkRectBlackOrbitMedialRibbonFlatDirection R omega d j = 0 at hw
  let W := 8 * R.medialTorus.width
  let H := 8 * R.medialTorus.height
  have hW : 0 < W := mul_pos (by decide) R.medialTorus.width_pos
  have hH : 0 < H := mul_pos (by decide) R.medialTorus.height_pos
  letI : NeZero W := ⟨hW.ne'⟩
  letI : NeZero H := ⟨hH.ne'⟩
  let pi := fkRectBlackOrbitMedialRibbonFlatSite R omega d i
  let pj := fkRectBlackOrbitMedialRibbonFlatSite R omega d j
  let ri := fkRectRibbonSubdivisionResidueCongr W H hz r
  let sj := fkRectRibbonSubdivisionResidueCongr W H hw s
  have hir := fkRectRibbonSubdivisionCode_congr_direction
    W H hW hH pi hz r
  have hjs := fkRectRibbonSubdivisionCode_congr_direction
    W H hW hH pj hw s
  have hzero : fkRectRibbonSubdivisionCode W H hW hH pi 0 ri =
      fkRectRibbonSubdivisionCode W H hW hH pj 0 sj := by
    exact hir.symm.trans (h.trans hjs)
  have hx := congrArg
    (fun c : (Fin W × Fin H) × (Fin H × Fin W) => c.1.1.val) hzero
  have hy := congrArg
    (fun c : (Fin W × Fin H) × (Fin H × Fin W) => c.2.1.val) hzero
  simp only [fkRectRibbonSubdivisionCode] at hx hy
  letI : NeZero W := ⟨hW.ne'⟩
  letI : NeZero H := ⟨hH.ne'⟩
  have hp : pi = pj := by
    apply Prod.ext
    · exact ZMod.val_injective W hx
    · exact ZMod.val_injective H hy
  have hij : i = j :=
    fkRectBlackOrbitMedialRibbonFlatSite_injective R omega d hp
  subst j
  have hrs : r = s := by
    apply fkRectRibbonSubdivisionCode_fixed_injective W H hW hH pi
      (fkRectBlackOrbitMedialRibbonFlatDirection R omega d i)
    exact h
  cases hrs
  rfl

set_option maxHeartbeats 500000 in

theorem fkRectBlackOrbitRibbonSubdivisionCode_eq_of_direction_zero
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (z w : FKRectBlackOrbitRibbonSubdivisionIndex R omega d)
    (hz : fkRectBlackOrbitMedialRibbonFlatDirection R omega d z.1 = 0)
    (h : fkRectBlackOrbitRibbonSubdivisionCode R omega d z =
      fkRectBlackOrbitRibbonSubdivisionCode R omega d w) :
    z = w := by
  rcases z with ⟨i, r⟩
  rcases w with ⟨j, s⟩
  change fkRectBlackOrbitMedialRibbonFlatDirection R omega d i = 0 at hz
  let W := 8 * R.medialTorus.width
  let H := 8 * R.medialTorus.height
  have hW : 0 < W := mul_pos (by decide) R.medialTorus.width_pos
  have hH : 0 < H := mul_pos (by decide) R.medialTorus.height_pos
  letI : NeZero W := ⟨hW.ne'⟩
  letI : NeZero H := ⟨hH.ne'⟩
  let pi := fkRectBlackOrbitMedialRibbonFlatSite R omega d i
  let pj := fkRectBlackOrbitMedialRibbonFlatSite R omega d j
  let pxi := fkRectZModFin hW pi.1
  let pxj := fkRectZModFin hW pj.1
  let pyi := fkRectZModFin hH pi.2
  let pyj := fkRectZModFin hH pj.2
  rcases fkRectFinFour_cases
      (fkRectBlackOrbitMedialRibbonFlatDirection R omega d j) with
    hw | hw | hw | hw
  · exact fkRectBlackOrbitRibbonSubdivisionCode_eq_of_directions_zero_zero
      R omega d ⟨i, r⟩ ⟨j, s⟩ hz hw h
  · let ri := fkRectRibbonSubdivisionResidueCongr W H hz r
    let sj := fkRectRibbonSubdivisionResidueCongr W H hw s
    have hir := fkRectRibbonSubdivisionCode_congr_direction
      W H hW hH pi hz r
    have hjs := fkRectRibbonSubdivisionCode_congr_direction
      W H hW hH pj hw s
    have h01 : fkRectRibbonSubdivisionCode W H hW hH pi 0 ri =
        fkRectRibbonSubdivisionCode W H hW hH pj 1 sj :=
      hir.symm.trans (h.trans hjs)
    have hpx : pxi = pxj := by
      simpa [fkRectRibbonSubdivisionCode, pxi, pxj, fkRectZModFin] using
        congrArg
          (fun c : (Fin W × Fin H) × (Fin H × Fin W) => c.1.1) h01
    have hpy : pyi = pyj := by
      simpa [fkRectRibbonSubdivisionCode, pyi, pyj, fkRectZModFin] using
        congrArg
          (fun c : (Fin W × Fin H) × (Fin H × Fin W) => c.2.1) h01
    have hp : pi = pj := by
      apply Prod.ext
      · exact fkRectZModFin_injective hW hpx
      · exact fkRectZModFin_injective hH hpy
    have hij := fkRectBlackOrbitMedialRibbonFlatSite_injective R omega d hp
    subst j
    have hbad : (0 : Fin 4) = 1 := hz.symm.trans hw
    exact (by simpa using congrArg Fin.val hbad : False).elim
  · let ri := fkRectRibbonSubdivisionResidueCongr W H hz r
    let sj := fkRectRibbonSubdivisionResidueCongr W H hw s
    have hir := fkRectRibbonSubdivisionCode_congr_direction
      W H hW hH pi hz r
    have hjs := fkRectRibbonSubdivisionCode_congr_direction
      W H hW hH pj hw s
    have h02 : fkRectRibbonSubdivisionCode W H hW hH pi 0 ri =
        fkRectRibbonSubdivisionCode W H hW hH pj 2 sj :=
      hir.symm.trans (h.trans hjs)
    have hxpair : (pxi, ri) = fkRectRibbonBackwardCode hW hH pxj sj := by
      simpa [fkRectRibbonSubdivisionCode, pxi, pxj, fkRectZModFin] using
        congrArg
          (fun c : (Fin W × Fin H) × (Fin H × Fin W) => c.1) h02
    have hpy : pyi = pyj := by
      simpa [fkRectRibbonSubdivisionCode, pyi, pyj, fkRectZModFin] using
        congrArg
          (fun c : (Fin W × Fin H) × (Fin H × Fin W) => c.2.1) h02
    rcases fkRectRibbon_forward_eq_backward hW hH pxi pxj ri sj hxpair with
      hsame | hopp
    · have hp : pi = pj := by
        apply Prod.ext
        · exact fkRectZModFin_injective hW hsame.2.2
        · exact fkRectZModFin_injective hH hpy
      have hij := fkRectBlackOrbitMedialRibbonFlatSite_injective R omega d hp
      subst j
      have hbad : (0 : Fin 4) = 2 := hz.symm.trans hw
      exact (by simpa using congrArg Fin.val hbad : False).elim
    · have hadd : pi.1 + 1 = pj.1 := by
        apply fkRectZModFin_injective hW
        rw [fkRectZModFin_add_one]
        change finitePeriodicSucc hW pxi = pxj
        rw [hopp.2.2.1, finitePeriodicSucc_cyclicPred]
      have hycoord : pi.2 = pj.2 := fkRectZModFin_injective hH hpy
      have hpstep : pj = fkRectRibbonRectStep W H 0 pi := by
        apply Prod.ext
        · exact hadd.symm
        · exact hycoord.symm
      have hsucc := fkRectBlackOrbitMedialRibbonFlatSite_succ R omega d i
      rw [hz] at hsucc
      have hji : j = i + 1 :=
        fkRectBlackOrbitMedialRibbonFlatSite_injective R omega d
          (hpstep.trans hsucc.symm)
      rw [hji] at hw
      exact False.elim
        ((fkRectBlackOrbitMedialRibbonFlatDirection_nonUturn R omega d i)
          (by simpa [hz] using hw))
  · let ri := fkRectRibbonSubdivisionResidueCongr W H hz r
    let sj := fkRectRibbonSubdivisionResidueCongr W H hw s
    have hir := fkRectRibbonSubdivisionCode_congr_direction
      W H hW hH pi hz r
    have hjs := fkRectRibbonSubdivisionCode_congr_direction
      W H hW hH pj hw s
    have h03 : fkRectRibbonSubdivisionCode W H hW hH pi 0 ri =
        fkRectRibbonSubdivisionCode W H hW hH pj 3 sj :=
      hir.symm.trans (h.trans hjs)
    have hpx : pxi = pxj := by
      simpa [fkRectRibbonSubdivisionCode, pxi, pxj, fkRectZModFin] using
        congrArg
          (fun c : (Fin W × Fin H) × (Fin H × Fin W) => c.1.1) h03
    have hypair : (pyi, (0 : Fin W)) =
        fkRectRibbonBackwardCode hH hW pyj sj := by
      simpa [fkRectRibbonSubdivisionCode, pyi, pyj, fkRectZModFin] using
        congrArg
          (fun c : (Fin W × Fin H) × (Fin H × Fin W) => c.2) h03
    rcases fkRectRibbon_forward_eq_backward hH hW pyi pyj 0 sj hypair with
      hsame | himpossible
    · have hp : pi = pj := by
        apply Prod.ext
        · exact fkRectZModFin_injective hW hpx
        · exact fkRectZModFin_injective hH hsame.2.2
      have hij := fkRectBlackOrbitMedialRibbonFlatSite_injective R omega d hp
      subst j
      have hbad : (0 : Fin 4) = 3 := hz.symm.trans hw
      exact (by simpa using congrArg Fin.val hbad : False).elim
    · exact (himpossible.1 rfl).elim

end

end StatMech.FrontierD
