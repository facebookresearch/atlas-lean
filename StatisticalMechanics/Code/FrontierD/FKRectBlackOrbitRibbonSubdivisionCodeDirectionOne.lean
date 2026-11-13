/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCodeDirectionZero



namespace StatMech.FrontierD

open StatMech.Onsager
open StatMech.Onsager.BaseCase

noncomputable section

set_option maxHeartbeats 500000 in

theorem fkRectBlackOrbitRibbonSubdivisionCode_eq_of_direction_one
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (z w : FKRectBlackOrbitRibbonSubdivisionIndex R omega d)
    (hz : fkRectBlackOrbitMedialRibbonFlatDirection R omega d z.1 = 1)
    (h : fkRectBlackOrbitRibbonSubdivisionCode R omega d z =
      fkRectBlackOrbitRibbonSubdivisionCode R omega d w) :
    z = w := by
  rcases z with ⟨i, r⟩
  rcases w with ⟨j, s⟩
  change fkRectBlackOrbitMedialRibbonFlatDirection R omega d i = 1 at hz
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
  · exact (fkRectBlackOrbitRibbonSubdivisionCode_eq_of_direction_zero
      R omega d ⟨j, s⟩ ⟨i, r⟩ hw h.symm).symm
  · let ri := fkRectRibbonSubdivisionResidueCongr W H hz r
    let sj := fkRectRibbonSubdivisionResidueCongr W H hw s
    have hir := fkRectRibbonSubdivisionCode_congr_direction
      W H hW hH pi hz r
    have hjs := fkRectRibbonSubdivisionCode_congr_direction
      W H hW hH pj hw s
    have h11 : fkRectRibbonSubdivisionCode W H hW hH pi 1 ri =
        fkRectRibbonSubdivisionCode W H hW hH pj 1 sj :=
      hir.symm.trans (h.trans hjs)
    have hpx : pxi = pxj := by
      simpa [fkRectRibbonSubdivisionCode, pxi, pxj, fkRectZModFin] using
        congrArg
          (fun c : (Fin W × Fin H) × (Fin H × Fin W) => c.1.1) h11
    have hpy : pyi = pyj := by
      simpa [fkRectRibbonSubdivisionCode, pyi, pyj, fkRectZModFin] using
        congrArg
          (fun c : (Fin W × Fin H) × (Fin H × Fin W) => c.2.1) h11
    have hp : pi = pj := by
      apply Prod.ext
      · exact fkRectZModFin_injective hW hpx
      · exact fkRectZModFin_injective hH hpy
    have hij := fkRectBlackOrbitMedialRibbonFlatSite_injective R omega d hp
    subst j
    have hrs : r = s := by
      apply fkRectRibbonSubdivisionCode_fixed_injective W H hW hH pi
        (fkRectBlackOrbitMedialRibbonFlatDirection R omega d i)
      exact h
    cases hrs
    rfl
  · let ri := fkRectRibbonSubdivisionResidueCongr W H hz r
    let sj := fkRectRibbonSubdivisionResidueCongr W H hw s
    have hir := fkRectRibbonSubdivisionCode_congr_direction
      W H hW hH pi hz r
    have hjs := fkRectRibbonSubdivisionCode_congr_direction
      W H hW hH pj hw s
    have h12 : fkRectRibbonSubdivisionCode W H hW hH pi 1 ri =
        fkRectRibbonSubdivisionCode W H hW hH pj 2 sj :=
      hir.symm.trans (h.trans hjs)
    have hxpair : (pxi, (0 : Fin H)) =
        fkRectRibbonBackwardCode hW hH pxj sj := by
      simpa [fkRectRibbonSubdivisionCode, pxi, pxj, fkRectZModFin] using
        congrArg
          (fun c : (Fin W × Fin H) × (Fin H × Fin W) => c.1) h12
    have hpy : pyi = pyj := by
      simpa [fkRectRibbonSubdivisionCode, pyi, pyj, fkRectZModFin] using
        congrArg
          (fun c : (Fin W × Fin H) × (Fin H × Fin W) => c.2.1) h12
    rcases fkRectRibbon_forward_eq_backward hW hH pxi pxj 0 sj hxpair with
      hsame | himpossible
    · have hp : pi = pj := by
        apply Prod.ext
        · exact fkRectZModFin_injective hW hsame.2.2
        · exact fkRectZModFin_injective hH hpy
      have hij := fkRectBlackOrbitMedialRibbonFlatSite_injective R omega d hp
      subst j
      have hbad : (1 : Fin 4) = 2 := hz.symm.trans hw
      exact (by simpa using congrArg Fin.val hbad : False).elim
    · exact (himpossible.1 rfl).elim
  · let ri := fkRectRibbonSubdivisionResidueCongr W H hz r
    let sj := fkRectRibbonSubdivisionResidueCongr W H hw s
    have hir := fkRectRibbonSubdivisionCode_congr_direction
      W H hW hH pi hz r
    have hjs := fkRectRibbonSubdivisionCode_congr_direction
      W H hW hH pj hw s
    have h13 : fkRectRibbonSubdivisionCode W H hW hH pi 1 ri =
        fkRectRibbonSubdivisionCode W H hW hH pj 3 sj :=
      hir.symm.trans (h.trans hjs)
    have hpx : pxi = pxj := by
      simpa [fkRectRibbonSubdivisionCode, pxi, pxj, fkRectZModFin] using
        congrArg
          (fun c : (Fin W × Fin H) × (Fin H × Fin W) => c.1.1) h13
    have hypair : (pyi, ri) = fkRectRibbonBackwardCode hH hW pyj sj := by
      simpa [fkRectRibbonSubdivisionCode, pyi, pyj, fkRectZModFin] using
        congrArg
          (fun c : (Fin W × Fin H) × (Fin H × Fin W) => c.2) h13
    rcases fkRectRibbon_forward_eq_backward hH hW pyi pyj ri sj hypair with
      hsame | hopp
    · have hp : pi = pj := by
        apply Prod.ext
        · exact fkRectZModFin_injective hW hpx
        · exact fkRectZModFin_injective hH hsame.2.2
      have hij := fkRectBlackOrbitMedialRibbonFlatSite_injective R omega d hp
      subst j
      have hbad : (1 : Fin 4) = 3 := hz.symm.trans hw
      exact (by simpa using congrArg Fin.val hbad : False).elim
    · have hadd : pi.2 + 1 = pj.2 := by
        apply fkRectZModFin_injective hH
        rw [fkRectZModFin_add_one]
        change finitePeriodicSucc hH pyi = pyj
        rw [hopp.2.2.1, finitePeriodicSucc_cyclicPred]
      have hxcoord : pi.1 = pj.1 := fkRectZModFin_injective hW hpx
      have hpstep : pj = fkRectRibbonRectStep W H 1 pi := by
        apply Prod.ext
        · exact hxcoord.symm
        · exact hadd.symm
      have hsucc := fkRectBlackOrbitMedialRibbonFlatSite_succ R omega d i
      rw [hz] at hsucc
      have hji : j = i + 1 :=
        fkRectBlackOrbitMedialRibbonFlatSite_injective R omega d
          (hpstep.trans hsucc.symm)
      rw [hji] at hw
      exact False.elim
        ((fkRectBlackOrbitMedialRibbonFlatDirection_nonUturn R omega d i)
          (by simpa [hz] using hw))

end

end StatMech.FrontierD
