/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Modules.IsFrameOn
public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
public import Mathlib.AlgebraicGeometry.Properties

@[expose] public section

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries (structureModule)

universe u

/-- The unit section `1` of the structure sheaf is a frame on `U`: multiplication by its
restrictions is the identity of `Γ(X, W)`. -/
private theorem isFrameOn_one (X : Scheme.{u}) (U : X.Opens) :
    Scheme.Modules.IsFrameOn (M := structureModule X) (1 : Γ(X, U)) U := by
  intro W hWU _
  have h : ∀ g : Γ(X, W), g * X.presheaf.map (homOfLE hWU).op 1 = g := fun g => by
    rw [map_one, mul_one]
  refine ⟨fun a b hab => ?_, fun b => ⟨b, h b⟩⟩
  rw [← h a, ← h b]
  exact hab

/-- The zero section of the structure sheaf of a nonempty scheme is not a frame. -/
example (X : Scheme.{u}) [Nonempty X] :
    ¬ Scheme.Modules.IsFrameOn (0 : Γ(structureModule X, ⊤)) ⊤ := fun h =>
  one_ne_zero ((h le_rfl le_rfl).1 (a₁ := 1) (a₂ := 0) (by simp only [map_zero, smul_zero]))

/-- Frames restrict along restriction maps and to smaller opens: the restriction of the unit
section to `U' ≤ U` is a frame on `U'`. -/
example (X : Scheme.{u}) {U U' : X.Opens} (h : U' ≤ U) :
    Scheme.Modules.IsFrameOn ((structureModule X).presheaf.map (homOfLE h).op (1 : Γ(X, U))) U' :=
  ((isFrameOn_one X U).map (homOfLE h)).mono h

/-- Against the unit frame, only `0` has coordinate `0`. -/
example (X : Scheme.{u}) (U : X.Opens) (g : Γ(X, U)) :
    g • (structureModule X).presheaf.map (homOfLE le_rfl).op (1 : Γ(X, U)) = 0 ↔ g = 0 :=
  (isFrameOn_one X U).smul_eq_zero_iff le_rfl le_rfl g

/-- `smulSectionHom W τ` is the morphism that `SheafOfModules.unitHomEquiv` assigns to the
restrictions of `τ` to the opens of `W`. -/
example (X : Scheme.{u}) {M : X.Modules} (W : X.Opens) (τ : Γ(M, W))
    (W' : (W : Scheme.{u}).Opens) :
    (SheafOfModules.unitHomEquiv (M.restrict W.ι) (Scheme.Modules.smulSectionHom W τ)).val
        (Opposite.op W') =
      (M.restrictAppIso W.ι W').inv (M.presheaf.map (homOfLE (W.ι_image_le W')).op τ) :=
  congrArg (fun σ : (M.restrict W.ι).sections => σ.val (Opposite.op W'))
    (Equiv.apply_symm_apply _ _)

/-- On each open of `W`, the component of `smulSectionHom W τ` sends `1` to the restriction
of `τ`. -/
example (X : Scheme.{u}) {M : X.Modules} (W : X.Opens) (τ : Γ(M, W))
    (W' : (W : Scheme.{u}).Opens) :
    (Scheme.Modules.smulSectionHom W τ).app W' (1 : Γ(W, W')) =
      (M.restrictAppIso W.ι W').inv (M.presheaf.map (homOfLE (W.ι_image_le W')).op τ) := by
  rw [Scheme.Modules.smulSectionHom_app_apply, map_one, one_smul]
