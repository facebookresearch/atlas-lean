/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantTensorPowers
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSphereOne
public import MathlibExt.CategoryTheory.Monoidal.TensorPowers

/-!
# Tensor powers of sphere one in the pointed CGWH model category

Every tensor power of the native pointed one-sphere is cofibrant in the
selected pointed CGWH model. Consequently, tensoring on the left by any such
power preserves cofibrations and trivial cofibrations.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory MonoidalCategory
open HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.modelCategory

/-- Every tensor power of the native pointed one-sphere is cofibrant. -/
theorem tensorPowObj_sphereOne_isCofibrant (r : ℕ) :
    IsCofibrant
      (TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} r) := by
  let _ : IsCofibrant PointedCGWH.sphereOne.{u, v} :=
    PointedCGWH.modelCategory.sphereOne_isCofibrant
  let _ : IsCofibrant (𝟙_ PointedCGWH.{u, v}) :=
    PointedCGWH.modelCategory.smashUnit_isCofibrant
  exact IsClosedSymmetricMonoidalModelCategory.isCofibrant_tensorPowObj
    PointedCGWH.sphereOne.{u, v} r

/-- Tensoring on the left by a tensor power of the native pointed one-sphere
preserves cofibrations. -/
theorem tensorPowObj_whiskerLeft_mem_cofibrations
    (r : ℕ) {X Y : PointedCGWH.{u, v}} {f : X ⟶ Y}
    (hf : cofibrations PointedCGWH.{u, v} f) :
    cofibrations PointedCGWH.{u, v}
      (𝟙 (TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} r) ⊗ₘ f) := by
  let _ : IsCofibrant
      (TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} r) :=
    tensorPowObj_sphereOne_isCofibrant r
  rw [MonoidalCategory.id_tensorHom]
  exact IsClosedSymmetricMonoidalModelCategory.whiskerLeft_mem_cofibrations
    (TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} r) f hf

/-- Tensoring on the left by a tensor power of the native pointed one-sphere
preserves trivial cofibrations. -/
theorem tensorPowObj_whiskerLeft_mem_trivialCofibrations
    (r : ℕ) {X Y : PointedCGWH.{u, v}} {f : X ⟶ Y}
    (hf : trivialCofibrations PointedCGWH.{u, v} f) :
    trivialCofibrations PointedCGWH.{u, v}
      (𝟙 (TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} r) ⊗ₘ f) := by
  let _ : IsCofibrant
      (TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} r) :=
    tensorPowObj_sphereOne_isCofibrant r
  rw [MonoidalCategory.id_tensorHom]
  exact IsClosedSymmetricMonoidalModelCategory.whiskerLeft_mem_trivialCofibrations
    (TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} r) f hf

end PointedCGWH.modelCategory
