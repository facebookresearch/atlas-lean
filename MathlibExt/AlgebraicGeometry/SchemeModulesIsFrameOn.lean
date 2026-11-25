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

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict

@[expose] public section

open CategoryTheory Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A section `s` of a sheaf of modules `M` over `U` is a frame on `V` when
multiplication by the restriction of `s` identifies the sections of the
structure sheaf with the sections of `M` over every open `W ⊆ U ∩ V`. -/
def IsFrameOn {M : X.Modules} {U : X.Opens} (s : Γ(M, U)) (V : X.Opens) :
    Prop :=
  ∀ ⦃W : X.Opens⦄ (hWU : W ≤ U), W ≤ V →
    Function.Bijective fun g : Γ(X, W) =>
      g • (M.presheaf.map (homOfLE hWU).op s : Γ(M, W))

namespace IsFrameOn

variable {M : X.Modules} {U V : X.Opens} {s : Γ(M, U)}

lemma bijective (h : IsFrameOn s V) {W : X.Opens} (hWU : W ≤ U)
    (hWV : W ≤ V) :
    Function.Bijective fun g : Γ(X, W) =>
      g • (M.presheaf.map (homOfLE hWU).op s : Γ(M, W)) :=
  h hWU hWV

end IsFrameOn

namespace FramePullback

private def restrictRingCatSheafHom (W : X.Opens) :
    (W : Scheme.{u}).ringCatSheaf ⟶
      (W.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology (W : Scheme.{u}))
        (Opens.grothendieckTopology X)).obj X.ringCatSheaf :=
  ⟨𝟙 _⟩

private def restrictFunctor' (W : X.Opens) :
    X.Modules ⥤ (W : Scheme.{u}).Modules :=
  SheafOfModules.pushforward (restrictRingCatSheafHom W)

private lemma restrictFunctor'_eq (W : X.Opens) :
    restrictFunctor' W = Modules.restrictFunctor W.ι := by
  dsimp only [restrictFunctor', Modules.restrictFunctor, restrictRingCatSheafHom]
  congr 2
  ext V : 2
  change 𝟙 _ = (forget₂ CommRingCat RingCat).map (W.ι.appIso V.unop).inv
  rw [Scheme.Opens.ι_appIso]
  rfl

private def restrictFunctor'IsoPullback (W : X.Opens) :
    restrictFunctor' W ≅ Modules.pullback W.ι :=
  eqToIso (restrictFunctor'_eq W) ≪≫ Modules.restrictFunctorIsoPullback W.ι

private lemma image_le (W : X.Opens) (W' : (W : Scheme.{u}).Opens) :
    W.ι ''ᵁ W' ≤ W :=
  (W.ι.image_le_opensRange W').trans_eq W.opensRange_ι

private abbrev secX (W : X.Opens) (W' : (W : Scheme.{u}).Opens)
    (a : Γ(W, W')) : Γ(X, W.ι ''ᵁ W') :=
  a

private def smulSectionHom (W : X.Opens) (N : X.Modules) (τ : Γ(N, W)) :
    SheafOfModules.unit ((W : X.Opens) : Scheme.{u}).ringCatSheaf ⟶
      (restrictFunctor' W).obj N :=
  ⟨{
    app := fun W' =>
      letI : Module ↑(((W : Scheme.{u}).ringCatSheaf).obj.obj W')
          ↑(((PresheafOfModules.pushforward₀ (Scheme.Hom.opensFunctor W.ι)
            ((CategoryTheory.sheafToPresheaf (Opens.grothendieckTopology X) RingCat).obj
              X.ringCatSheaf)).obj N.val).obj W') :=
        inferInstanceAs (Module (Γ(X, W.ι ''ᵁ W'.unop)) (Γ(N, W.ι ''ᵁ W'.unop)))
      ModuleCat.ofHom
      { toFun := fun a =>
          (secX W W'.unop a •
            N.presheaf.map (homOfLE (image_le W W'.unop)).op τ :
              Γ(N, W.ι ''ᵁ W'.unop))
        map_add' := fun a b => by
          change secX W W'.unop (a + b) •
              (N.presheaf.map (homOfLE (image_le W W'.unop)).op τ :
                Γ(N, W.ι ''ᵁ W'.unop)) =
            secX W W'.unop a •
              (N.presheaf.map (homOfLE (image_le W W'.unop)).op τ :
                Γ(N, W.ι ''ᵁ W'.unop)) +
            secX W W'.unop b •
              (N.presheaf.map (homOfLE (image_le W W'.unop)).op τ :
                Γ(N, W.ι ''ᵁ W'.unop))
          exact add_smul (secX W W'.unop a) (secX W W'.unop b) _
        map_smul' := fun r a => by
          change secX W W'.unop (r * a) •
              (N.presheaf.map (homOfLE (image_le W W'.unop)).op τ :
                Γ(N, W.ι ''ᵁ W'.unop)) =
            secX W W'.unop r • (secX W W'.unop a •
              (N.presheaf.map (homOfLE (image_le W W'.unop)).op τ :
                Γ(N, W.ι ''ᵁ W'.unop)))
          exact mul_smul (secX W W'.unop r) (secX W W'.unop a) _ }
    naturality := fun {W' W''} i => by
         apply ModuleCat.hom_ext
         apply LinearMap.ext
         intro a
         change secX W W''.unop
               (X.presheaf.map (W.ι.opensFunctor.map i.unop).op
                 (secX W W'.unop a)) •
             N.presheaf.map (homOfLE (image_le W W''.unop)).op τ =
           N.presheaf.map (W.ι.opensFunctor.map i.unop).op
             (secX W W'.unop a •
               N.presheaf.map (homOfLE (image_le W W'.unop)).op τ)
         rw [Scheme.Modules.map_smul]
         congr 1
         change _ = (N.presheaf.map _ ≫ N.presheaf.map _) τ
         rw [← N.presheaf.map_comp]
         rfl }⟩

private lemma isIso_smulSectionHom_of_bijective (W : X.Opens)
    (N : X.Modules) (τ : Γ(N, W))
    (hb : ∀ W' : (((W : X.Opens) : Scheme.{u}).Opens)ᵒᵖ,
      Function.Bijective ((smulSectionHom W N τ).val.app W')) :
    IsIso (smulSectionHom W N τ) := by
  set ψ := smulSectionHom W N τ
  have h₂ : IsIso ((PresheafOfModules.toPresheaf _).map
      ((SheafOfModules.forget _).map ψ)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro W'
    have : IsIso ((CategoryTheory.forget Ab).map
        (((PresheafOfModules.toPresheaf _).map
          ((SheafOfModules.forget _).map ψ)).app W')) :=
      (isIso_iff_bijective _).2 (hb W')
    exact isIso_of_reflects_iso _ (CategoryTheory.forget Ab)
  have := (SheafOfModules.fullyFaithfulForget
    (((W : X.Opens) : Scheme.{u}).ringCatSheaf)).reflectsIsomorphisms
  have h₃ := isIso_of_reflects_iso ((SheafOfModules.forget _).map ψ)
    (PresheafOfModules.toPresheaf _)
  exact isIso_of_reflects_iso ψ (SheafOfModules.forget _)

private lemma isIso_smulSectionHom {M : X.Modules} {U V : X.Opens}
    {s : Γ(M, U)} (h : IsFrameOn s V) (W : X.Opens)
    (hWU : W ≤ U) (hWV : W ≤ V) :
    IsIso (smulSectionHom W M
      (M.presheaf.map (homOfLE hWU).op s)) := by
  apply isIso_smulSectionHom_of_bijective
  intro W'
  have e : M.presheaf.map (homOfLE (image_le W W'.unop)).op
        (M.presheaf.map (homOfLE hWU).op s) =
      M.presheaf.map
        (homOfLE ((image_le W W'.unop).trans hWU)).op s := by
    change (M.presheaf.map _ ≫ M.presheaf.map _) s = _
    rw [← M.presheaf.map_comp]
    rfl
  have hb := h ((image_le W W'.unop).trans hWU)
    ((image_le W W'.unop).trans hWV)
  rw [← e] at hb
  exact hb

end FramePullback

/-- A local frame trivializes the pullback of a sheaf of modules to any
smaller open contained in both the domain of the section and the open on
which it is a frame. -/
public theorem IsFrameOn.nonempty_pullback_iso_unit
    {M : X.Modules} {U V : X.Opens} {s : Γ(M, U)}
    (h : IsFrameOn s V) (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V) :
    Nonempty ((Modules.pullback W.ι).obj M ≅
      SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf) :=
  haveI := FramePullback.isIso_smulSectionHom h W hWU hWV
  ⟨((FramePullback.restrictFunctor'IsoPullback W).symm.app M) ≪≫
    (asIso (FramePullback.smulSectionHom W M
      (M.presheaf.map (homOfLE hWU).op s))).symm⟩

end AlgebraicGeometry.Scheme.Modules

end
