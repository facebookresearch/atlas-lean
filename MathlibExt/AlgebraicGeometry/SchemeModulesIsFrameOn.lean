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

variable {M : X.Modules} {U : X.Opens} (s : Γ(M, U)) (W : X.Opens) (hWU : W ≤ U)

-- The restrictions of `s` to the opens of `W`, as a global section of `M.restrict W.ι`.
private def restrictSection : (M.restrict W.ι).sections :=
  PresheafOfModules.sectionsMk
    (fun W' => (M.restrictAppIso W.ι W'.unop).inv
      (M.presheaf.map (homOfLE ((W.ι_image_le W'.unop).trans hWU)).op s))
    (fun W₁ W₂ i => by
      change (M.restrict W.ι).presheaf.map i ((M.restrictAppIso W.ι W₁.unop).inv _) = _
      rw [restrictAppIso_inv_map_apply]
      congr 1
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)

-- The structure sheaf of `W`, as an object of `W.Modules`.
private abbrev unitW : (W : Scheme.{u}).Modules :=
  SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf

-- Multiplication by the restrictions of `s`, as a morphism out of the structure sheaf of `W`.
private def smulHom : unitW W ⟶ M.restrict W.ι :=
  (SheafOfModules.unitHomEquiv (M.restrict W.ι)).symm (restrictSection s W hWU)

private lemma smulHom_app_apply (W' : (W : Scheme.{u}).Opens) (a : Γ(W, W')) :
    (smulHom s W hWU).app W' a =
      (M.restrictAppIso W.ι W').inv ((W.ι.appIso W').inv a •
        M.presheaf.map (homOfLE ((W.ι_image_le W').trans hWU)).op s) := by
  rw [smul_restrictAppIso_inv_apply, Iso.inv_hom_id_apply]
  rfl

private lemma isIso_smulHom {V : X.Opens} (h : IsFrameOn s V) (hWV : W ≤ V) :
    IsIso (smulHom s W hWU) := by
  refine Hom.isIso_iff_isIso_app.mpr fun W' => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  have e : ⇑(ConcreteCategory.hom ((smulHom s W hWU).app W')) =
      (M.restrictAppIso W.ι W').inv ∘
        (fun g : Γ(X, W.ι ''ᵁ W') =>
          g • M.presheaf.map (homOfLE ((W.ι_image_le W').trans hWU)).op s) ∘
        (W.ι.appIso W').inv :=
    funext (smulHom_app_apply s W hWU W')
  rw [e]
  exact (ConcreteCategory.bijective_of_isIso _).comp
    ((h ((W.ι_image_le W').trans hWU) ((W.ι_image_le W').trans hWV)).comp
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
  haveI := FramePullback.isIso_smulHom s W hWU h hWV
  ⟨(restrictFunctorIsoPullback W.ι).symm.app M ≪≫
    (asIso (FramePullback.smulHom s W hWU)).symm⟩

end AlgebraicGeometry.Scheme.Modules

end
