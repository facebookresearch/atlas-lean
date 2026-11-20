/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCodeDirectionOne



namespace StatMech.FrontierD

open StatMech.Onsager
open StatMech.Onsager.BaseCase

noncomputable section

set_option maxHeartbeats 500000 in

theorem fkRectBlackOrbitRibbonSubdivisionCode_eq_of_direction_two
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (z w : FKRectBlackOrbitRibbonSubdivisionIndex R omega d)
    (hz : fkRectBlackOrbitMedialRibbonFlatDirection R omega d z.1 = 2)
    (h : fkRectBlackOrbitRibbonSubdivisionCode R omega d z =
      fkRectBlackOrbitRibbonSubdivisionCode R omega d w) :
    z = w := by
  rcases z with ⟨i, r⟩
  rcases w with ⟨j, s⟩
  change fkRectBlackOrbitMedialRibbonFlatDirection R omega d i = 2 at hz
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
  · exact (fkRectBlackOrbitRibbonSubdivisionCode_eq_of_direction_one
      R omega d ⟨j, s⟩ ⟨i, r⟩ hw h.symm).symm
  · let ri := fkRectRibbonSubdivisionResidueCongr W H hz r
    let sj := fkRectRibbonSubdivisionResidueCongr W H hw s
    have hir := fkRectRibbonSubdivisionCode_congr_direction
      W H hW hH pi hz r
    have hjs := fkRectRibbonSubdivisionCode_congr_direction
      W H hW hH pj hw s
    have h22 : fkRectRibbonSubdivisionCode W H hW hH pi 2 ri =
        fkRectRibbonSubdivisionCode W H hW hH pj 2 sj :=
      hir.symm.trans (h.trans hjs)
    have hback : fkRectRibbonBackwardCode hW hH pxi ri =
        fkRectRibbonBackwardCode hW hH pxj sj := by
      simpa [fkRectRibbonSubdivisionCode, pxi, pxj, fkRectZModFin] using
        congrArg
          (fun c : (Fin W × Fin H) × (Fin H × Fin W) => c.1) h22
    have hpairs : (pxi, ri) = (pxj, sj) :=
      fkRectRibbonBackwardCode_injective hW hH hback
    have hpy : pyi = pyj := by
      simpa [fkRectRibbonSubdivisionCode, pyi, pyj, fkRectZModFin] using
        congrArg
          (fun c : (Fin W × Fin H) × (Fin H × Fin W) => c.2.1) h22
    have hp : pi = pj := by
      apply Prod.ext
      · exact fkRectZModFin_injective hW (congrArg Prod.fst hpairs)
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
    have h23 : fkRectRibbonSubdivisionCode W H hW hH pi 2 ri =
        fkRectRibbonSubdivisionCode W H hW hH pj 3 sj :=
      hir.symm.trans (h.trans hjs)
    have hxpair : fkRectRibbonBackwardCode hW hH pxi ri =
        (pxj, (0 : Fin H)) := by
      simpa [fkRectRibbonSubdivisionCode, pxi, pxj, fkRectZModFin] using
        congrArg
          (fun c : (Fin W × Fin H) × (Fin H × Fin W) => c.1) h23
    have hypair : (pyi, (0 : Fin W)) =
        fkRectRibbonBackwardCode hH hW pyj sj := by
      simpa [fkRectRibbonSubdivisionCode, pyi, pyj, fkRectZModFin] using
        congrArg
          (fun c : (Fin W × Fin H) × (Fin H × Fin W) => c.2) h23
    have hxforward : (pxj, (0 : Fin H)) =
        fkRectRibbonBackwardCode hW hH pxi ri := hxpair.symm
    rcases fkRectRibbon_forward_eq_backward hW hH pxj pxi 0 ri hxforward with
      hxsame | hximpossible
    · rcases fkRectRibbon_forward_eq_backward hH hW pyi pyj 0 sj hypair with
        hysame | hyimpossible
      · have hp : pi = pj := by
          apply Prod.ext
          · exact fkRectZModFin_injective hW hxsame.2.2.symm
          · exact fkRectZModFin_injective hH hysame.2.2
        have hij := fkRectBlackOrbitMedialRibbonFlatSite_injective R omega d hp
        subst j
        have hbad : (2 : Fin 4) = 3 := hz.symm.trans hw
        exact (by simpa using congrArg Fin.val hbad : False).elim
      · exact (hyimpossible.1 rfl).elim
    · exact (hximpossible.1 rfl).elim

end

end StatMech.FrontierD
