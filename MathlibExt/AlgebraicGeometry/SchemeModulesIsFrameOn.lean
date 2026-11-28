/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_
iso_unit_monoidalV2.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_
iso_unit_monoidalV2.lean`
and
`Definitions/Def_AlgebraicGeometry_ModulesSectionsTensor.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.Modules.IsFrameOn
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict

@[expose] public section

open CategoryTheory Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

namespace FramePullback

private lemma isIso_smulSectionHom {M : X.Modules} {U V : X.Opens} {s : Γ(M, U)}
    (h : IsFrameOn s V) (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V) :
    IsIso (smulSectionHom W (M.presheaf.map (homOfLE hWU).op s)) := by
  refine Hom.isIso_iff_isIso_app.mpr fun W' => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  have e : ⇑(ConcreteCategory.hom
        ((smulSectionHom W (M.presheaf.map (homOfLE hWU).op s)).app W')) =
      (M.restrictAppIso W.ι W').inv ∘
        (fun g : Γ(X, W.ι ''ᵁ W') => g •
          M.presheaf.map (homOfLE (W.ι_image_le W')).op (M.presheaf.map (homOfLE hWU).op s)) ∘
        (W.ι.appIso W').inv :=
    funext (smulSectionHom_app_apply W _ W')
  rw [e]
  exact (ConcreteCategory.bijective_of_isIso _).comp
    (((h.map (homOfLE hWU)) (W.ι_image_le W') ((W.ι_image_le W').trans hWV)).comp
      (ConcreteCategory.bijective_of_isIso _))

end FramePullback

/-- **Trivialization by a local frame.** A local frame trivializes the pullback of a sheaf of
modules to any smaller open contained in both the domain of the section and the open on
which it is a frame. -/
public theorem IsFrameOn.nonempty_pullback_iso_unit
    {M : X.Modules} {U V : X.Opens} {s : Γ(M, U)}
    (h : IsFrameOn s V) (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V) :
    Nonempty ((Modules.pullback W.ι).obj M ≅
      SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf) :=
  haveI := FramePullback.isIso_smulSectionHom h W hWU hWV
  ⟨(restrictFunctorIsoPullback W.ι).symm.app M ≪≫
    (asIso (smulSectionHom W (M.presheaf.map (homOfLE hWU).op s))).symm⟩

end AlgebraicGeometry.Scheme.Modules

end
