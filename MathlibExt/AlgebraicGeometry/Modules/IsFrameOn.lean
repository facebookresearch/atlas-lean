/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from:

`Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_
tensorSectionsBilin_monoidalV2.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_
tensorSectionsBilin_monoidalV2.lean`,
`Definitions/Def_AlgebraicGeometry_RelativePicardFunctor.lean`,
`Definitions/Def_AlgebraicGeometry_ModulesSectionsTensor.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Frames of sheaves of modules on a scheme

A section `s` of a sheaf of modules `M` over an open `U` is a frame on an open `V`
(`Scheme.Modules.IsFrameOn`) when multiplication by its restrictions identifies the sections of
the structure sheaf with those of `M` over every open `W ≤ U ⊓ V`. A frame gives a unique
coordinate to every section over such `W`; frames restrict to smaller opens and along restriction
maps. For a section `τ` over `W`, `Scheme.Modules.smulSectionHom W τ` is the morphism from the
structure sheaf of `W` to the restriction of `M` to `W` that multiplies by the restrictions of `τ`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section Frame

variable {M : X.Modules} {U : X.Opens}

/-- **Frame of a sheaf of modules.** A section `s` of `M` over `U` is a frame on `V` when
multiplication by its restrictions identifies the sections of the structure sheaf with those of
`M` over every open `W ≤ U ⊓ V`. -/
def IsFrameOn (s : Γ(M, U)) (V : X.Opens) : Prop :=
  ∀ ⦃W : X.Opens⦄ (hWU : W ≤ U), W ≤ V →
    Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE hWU).op s : Γ(M, W))

namespace IsFrameOn

variable {s : Γ(M, U)} {V : X.Opens}

lemma bijective (h : IsFrameOn s V) {W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V) :
    Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE hWU).op s : Γ(M, W)) :=
  h hWU hWV

lemma mono (h : IsFrameOn s V) {V' : X.Opens} (hV' : V' ≤ V) : IsFrameOn s V' :=
  fun _ hWU hWV' => h hWU (hWV'.trans hV')

lemma of_inf (h : IsFrameOn s (V ⊓ U)) : IsFrameOn s V :=
  fun _ hWU hWV => h hWU (le_inf hWV hWU)

lemma inf_iff : IsFrameOn s (V ⊓ U) ↔ IsFrameOn s V :=
  ⟨of_inf, fun h => h.mono inf_le_left⟩

lemma map (h : IsFrameOn s V) {U' : X.Opens} (i : U' ⟶ U) :
    IsFrameOn (M.presheaf.map i.op s) V := by
  intro W hWU' hWV
  have e : M.presheaf.map (homOfLE hWU').op (M.presheaf.map i.op s) =
      M.presheaf.map (homOfLE (hWU'.trans i.le)).op s := by
    rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
    rfl
  simp only [e]
  exact h (hWU'.trans i.le) hWV

lemma existsUnique (h : IsFrameOn s V) {W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V) (x : Γ(M, W)) :
    ∃! g : Γ(X, W), g • M.presheaf.map (homOfLE hWU).op s = x :=
  (Function.bijective_iff_existsUnique _).1 (h hWU hWV) x

lemma smul_eq_zero_iff (h : IsFrameOn s V) {W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V) (g : Γ(X, W)) :
    g • M.presheaf.map (homOfLE hWU).op s = 0 ↔ g = 0 := by
  constructor
  · intro hg
    apply (h hWU hWV).1
    change g • M.presheaf.map (homOfLE hWU).op s = (0 : Γ(X, W)) • M.presheaf.map (homOfLE hWU).op s
    rw [hg, zero_smul]
  · rintro rfl
    exact zero_smul _ _

end IsFrameOn

end Frame

section SMulSectionHom

variable {M : X.Modules} (W : X.Opens) (τ : Γ(M, W))

/-- **Multiplication by a section.** For a section `τ` of `M` over an open `W`, the morphism from
the structure sheaf of `W` to the restriction of `M` to `W` that multiplies by the restrictions of
`τ`. It is the morphism that `SheafOfModules.unitHomEquiv` assigns to the global section of the
restriction formed by these restrictions. A section over a larger open is restricted to `W`
first. -/
noncomputable def smulSectionHom :
    Quiver.Hom (V := (W : Scheme.{u}).Modules)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf) (M.restrict W.ι) :=
  (SheafOfModules.unitHomEquiv (M.restrict W.ι)).symm
    (PresheafOfModules.sectionsMk
      (fun W' => (M.restrictAppIso W.ι W'.unop).inv
        (M.presheaf.map (homOfLE (W.ι_image_le W'.unop)).op τ))
      (fun W₁ W₂ i => by
        change (M.restrict W.ι).presheaf.map i ((M.restrictAppIso W.ι W₁.unop).inv _) = _
        rw [restrictAppIso_inv_map_apply]
        congr 1
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl))

theorem smulSectionHom_app_apply (W' : (W : Scheme.{u}).Opens) (a : Γ(W, W')) :
    (smulSectionHom W τ).app W' a =
      (M.restrictAppIso W.ι W').inv ((W.ι.appIso W').inv a •
        M.presheaf.map (homOfLE (W.ι_image_le W')).op τ) := by
  rw [smul_restrictAppIso_inv_apply, Iso.inv_hom_id_apply]
  rfl

end SMulSectionHom

end AlgebraicGeometry.Scheme.Modules
