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
