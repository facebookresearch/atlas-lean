/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCodeDirectionTwo



namespace StatMech.FrontierD

open StatMech.Onsager
open StatMech.Onsager.BaseCase

noncomputable section

set_option maxHeartbeats 500000 in

theorem fkRectBlackOrbitRibbonSubdivisionCode_eq_of_direction_three
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (z w : FKRectBlackOrbitRibbonSubdivisionIndex R omega d)
    (hz : fkRectBlackOrbitMedialRibbonFlatDirection R omega d z.1 = 3)
    (h : fkRectBlackOrbitRibbonSubdivisionCode R omega d z =
      fkRectBlackOrbitRibbonSubdivisionCode R omega d w) :
    z = w := by
  rcases z with ⟨i, r⟩
  rcases w with ⟨j, s⟩
  change fkRectBlackOrbitMedialRibbonFlatDirection R omega d i = 3 at hz
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
  · exact (fkRectBlackOrbitRibbonSubdivisionCode_eq_of_direction_two
      R omega d ⟨j, s⟩ ⟨i, r⟩ hw h.symm).symm
  · let ri := fkRectRibbonSubdivisionResidueCongr W H hz r
    let sj := fkRectRibbonSubdivisionResidueCongr W H hw s
    have hir := fkRectRibbonSubdivisionCode_congr_direction
      W H hW hH pi hz r
    have hjs := fkRectRibbonSubdivisionCode_congr_direction
      W H hW hH pj hw s
    have h33 : fkRectRibbonSubdivisionCode W H hW hH pi 3 ri =
        fkRectRibbonSubdivisionCode W H hW hH pj 3 sj :=
      hir.symm.trans (h.trans hjs)
    have hpx : pxi = pxj := by
      simpa [fkRectRibbonSubdivisionCode, pxi, pxj, fkRectZModFin] using
        congrArg
          (fun c : (Fin W × Fin H) × (Fin H × Fin W) => c.1.1) h33
    have hback : fkRectRibbonBackwardCode hH hW pyi ri =
        fkRectRibbonBackwardCode hH hW pyj sj := by
      simpa [fkRectRibbonSubdivisionCode, pyi, pyj, fkRectZModFin] using
        congrArg
          (fun c : (Fin W × Fin H) × (Fin H × Fin W) => c.2) h33
    have hpairs : (pyi, ri) = (pyj, sj) :=
      fkRectRibbonBackwardCode_injective hH hW hback
    have hp : pi = pj := by
      apply Prod.ext
      · exact fkRectZModFin_injective hW hpx
      · exact fkRectZModFin_injective hH (congrArg Prod.fst hpairs)
    have hij := fkRectBlackOrbitMedialRibbonFlatSite_injective R omega d hp
    subst j
    have hrs : r = s := by
      apply fkRectRibbonSubdivisionCode_fixed_injective W H hW hH pi
        (fkRectBlackOrbitMedialRibbonFlatDirection R omega d i)
      exact h
    cases hrs
    rfl

end

end StatMech.FrontierD
