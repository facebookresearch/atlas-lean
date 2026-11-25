/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Modules.IsFrameOn
public import Mathlib.AlgebraicGeometry.Properties

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/-- The structure sheaf of `X` as a sheaf of modules. -/
private noncomputable abbrev unitMod (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The unit section `1` of the structure sheaf is a frame on `U`: multiplication by its
restrictions is the identity of `Γ(X, W)`. -/
private theorem isFrameOn_one (X : Scheme.{u}) (U : X.Opens) :
    Scheme.Modules.IsFrameOn (M := unitMod X) (1 : Γ(X, U)) U := by
  intro W hWU _
  have h : ∀ g : Γ(X, W), g * X.presheaf.map (homOfLE hWU).op 1 = g := fun g => by
    rw [map_one, mul_one]
  refine ⟨fun a b hab => ?_, fun b => ⟨b, h b⟩⟩
  rw [← h a, ← h b]
  exact hab

/-- The zero section of the structure sheaf of a nonempty scheme is not a frame. -/
example (X : Scheme.{u}) [Nonempty X] :
    ¬ Scheme.Modules.IsFrameOn (0 : Γ(unitMod X, ⊤)) ⊤ := fun h =>
  one_ne_zero ((h le_rfl le_rfl).1 (a₁ := 1) (a₂ := 0) (by simp only [map_zero, smul_zero]))

/-- Frames restrict along restriction maps and to smaller opens: the restriction of the unit
section to `U' ≤ U` is a frame on `U'`. -/
example (X : Scheme.{u}) {U U' : X.Opens} (h : U' ≤ U) :
    Scheme.Modules.IsFrameOn ((unitMod X).presheaf.map (homOfLE h).op (1 : Γ(X, U))) U' :=
  ((isFrameOn_one X U).map (homOfLE h)).mono h

/-- Against the unit frame, only `0` has coordinate `0`. -/
example (X : Scheme.{u}) (U : X.Opens) (g : Γ(X, U)) :
    g • (unitMod X).presheaf.map (homOfLE le_rfl).op (1 : Γ(X, U)) = 0 ↔ g = 0 :=
  (isFrameOn_one X U).smul_eq_zero_iff le_rfl le_rfl g
