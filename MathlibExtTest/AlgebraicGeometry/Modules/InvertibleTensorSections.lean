/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Modules.InvertibleTensorSections
public import MathlibExt.AlgebraicGeometry.SheafTensorSections

@[expose] public section

open CategoryTheory MonoidalCategory AlgebraicGeometry TensorProduct
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

universe u

/-- Consumer with the original binders. -/
example {X : Scheme.{u}} {L M : X.Modules} (hL : IsLineBundle L)
    (hM : IsLineBundle M) (U : X.affineOpens) :
    Function.Bijective (TensorProduct.lift (Scheme.Modules.tensorSectionsBilin L M U) :
      Γ(L, U) ⊗[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(L ⊗ M, U)) :=
  hL.bijective_lift_tensorSectionsBilin hM U

/-- Non-vacuity: the structure sheaf is invertible, so the statement applies to `𝒪_X ⊗ 𝒪_X`. -/
example (X : Scheme.{u}) (U : X.affineOpens) :
    Function.Bijective (TensorProduct.lift
      (Scheme.Modules.tensorSectionsBilin (𝟙_ X.Modules) (𝟙_ X.Modules) U)) :=
  IsLineBundle.bijective_lift_tensorSectionsBilin
    (isLineBundle_structureModule X) (isLineBundle_structureModule X) U

/-- Through `tensorIsoSheafify`, `tensorSections` is `SheafTensorSections.tensorSection`. -/
example (X : Scheme.{0}) (L M : X.Modules) (U : X.Opens) (s : Γ(L, U)) (t : Γ(M, U)) :
    Scheme.Modules.tensorSections s t =
      ((Scheme.Modules.tensorIsoSheafify L M).hom.val.app (Opposite.op U)).hom
        (MathlibExt.AlgebraicGeometry.SheafTensorSections.tensorSection X L M U s t) :=
  rfl

/-- The tensor product of two frames on `V` is a frame on `V`. -/
example {X : Scheme.{u}} {L M : X.Modules} {U V : X.Opens} {s : Γ(L, U)} {t : Γ(M, U)}
    (hs : Scheme.Modules.IsFrameOn s V) (ht : Scheme.Modules.IsFrameOn t V) :
    Scheme.Modules.IsFrameOn (Scheme.Modules.tensorSections s t) V :=
  hs.tensorSections ht

/-- The unit section `1` of the structure sheaf is a frame on `U`: multiplication by its
restrictions is the identity of `Γ(X, W)`. -/
example (X : Scheme.{u}) (U : X.Opens) :
    Scheme.Modules.IsFrameOn (M := 𝟙_ X.Modules) (1 : Γ(X, U)) U := by
  intro W hWU _
  have h : ∀ g : Γ(X, W), g * X.presheaf.map (homOfLE hWU).op 1 = g := fun g => by
    rw [map_one, mul_one]
  refine ⟨fun a b hab => ?_, fun b => ⟨b, h b⟩⟩
  rw [← h a, ← h b]
  exact hab

/-- The zero section of the structure sheaf of a nonempty scheme is not a frame. -/
example (X : Scheme.{u}) [Nonempty X] :
    ¬ Scheme.Modules.IsFrameOn (0 : Γ(𝟙_ X.Modules, ⊤)) ⊤ := fun h =>
  one_ne_zero ((h le_rfl le_rfl).1 (a₁ := 1) (a₂ := 0) (by simp only [map_zero, smul_zero]))
