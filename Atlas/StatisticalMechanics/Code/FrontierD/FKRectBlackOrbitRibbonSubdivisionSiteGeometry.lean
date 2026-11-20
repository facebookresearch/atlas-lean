/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionOffsetGeometry



namespace StatMech.FrontierD

open StatMech.Onsager
open StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectOnsDirStep_cast {M N : ℕ} (h : M = N)
    (mu : Fin 4) (s : ZMod M × ZMod M) :
    Equiv.cast (congrArg (fun n => ZMod n × ZMod n) h)
        (ons_dirStep M mu s) =
      ons_dirStep N mu
        (Equiv.cast (congrArg (fun n => ZMod n × ZMod n) h) s) := by
  subst N
  rfl

theorem fkRectBlackOrbitRibbonSubdivisionSite_succ
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (z : FKRectBlackOrbitRibbonSubdivisionIndex R omega d) :
    fkRectBlackOrbitRibbonSubdivisionSite R omega d
        (fkRectFinSigmaSucc
          (fun i => onsAnisotropicStepScale (8 * R.medialTorus.width)
            (8 * R.medialTorus.height)
            (fkRectBlackOrbitMedialRibbonFlatDirection R omega d i))
          (fkRectBlackOrbitRibbonSubdivisionStepScale_pos R omega d) z) =
      ons_dirStep (fkRectBlackOrbitRibbonSubdivisionSide R)
        (fkRectBlackOrbitMedialRibbonFlatDirection R omega d z.1)
        (fkRectBlackOrbitRibbonSubdivisionSite R omega d z) := by
  rcases z with ⟨i, r⟩
  simp only [fkRectFinSigmaSucc]
  split_ifs with hr
  · unfold fkRectBlackOrbitRibbonSubdivisionSite
    rw [← fkRectOnsDirStep_cast
      (fkRectBlackOrbitRibbonSubdivisionSide_eq_refinedProduct R)]
    apply congrArg (Equiv.cast (congrArg (fun n => ZMod n × ZMod n)
      (fkRectBlackOrbitRibbonSubdivisionSide_eq_refinedProduct R)))
    exact fkRectRibbonSubdivisionCodeEmbed_offset_succ
      (8 * R.medialTorus.width) (8 * R.medialTorus.height)
      (mul_pos (by decide) R.medialTorus.width_pos)
      (mul_pos (by decide) R.medialTorus.height_pos)
      (fkRectBlackOrbitMedialRibbonFlatSite R omega d i)
      (fkRectBlackOrbitMedialRibbonFlatDirection R omega d i) r hr
  · unfold fkRectBlackOrbitRibbonSubdivisionSite
    rw [← fkRectOnsDirStep_cast
      (fkRectBlackOrbitRibbonSubdivisionSide_eq_refinedProduct R)]
    apply congrArg (Equiv.cast (congrArg (fun n => ZMod n × ZMod n)
      (fkRectBlackOrbitRibbonSubdivisionSide_eq_refinedProduct R)))
    unfold fkRectBlackOrbitRibbonSubdivisionCode
    rw [fkRectBlackOrbitMedialRibbonFlatSite_succ]
    exact fkRectRibbonSubdivisionCodeEmbed_offset_wrap
      (8 * R.medialTorus.width) (8 * R.medialTorus.height)
      (mul_pos (by decide) R.medialTorus.width_pos)
      (mul_pos (by decide) R.medialTorus.height_pos)
      (fkRectBlackOrbitMedialRibbonFlatSite R omega d i)
      (fkRectBlackOrbitMedialRibbonFlatDirection R omega d i)
      (fkRectBlackOrbitMedialRibbonFlatDirection R omega d (i + 1))
      r hr ⟨0, fkRectBlackOrbitRibbonSubdivisionStepScale_pos R omega d (i + 1)⟩ rfl

end

end StatMech.FrontierD
