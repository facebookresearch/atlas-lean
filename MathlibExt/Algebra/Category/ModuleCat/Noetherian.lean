/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.CategoryTheory.Subobject.NoetherianObject
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

open CategoryTheory

universe v u

namespace ModuleCat

variable {R : Type u} [Ring R] (M : ModuleCat.{v} R)

/-- A module object in `ModuleCat R` is categorically noetherian iff it is algebraically
noetherian as an `R`-module. The bridge uses `ModuleCat.subobjectModule`, the order
isomorphism `Subobject M ≃o Submodule R M`, and the characterisations
`IsNoetherian R M ↔ WellFoundedGT (Submodule R M)` and
`IsNoetherianObject M ↔ WellFoundedGT (Subobject M)` via strict order well-foundedness. -/
theorem isNoetherianObject_iff_isNoetherian :
    IsNoetherianObject M ↔ IsNoetherian R M := by
  rw [isNoetherian_iff]
  have h_obj : IsNoetherianObject M ↔ WellFoundedGT (Subobject M) := by
    rw [IsNoetherianObject, ObjectProperty.is_iff, isNoetherianObject]
  rw [h_obj]
  constructor
  · intro hGT_sub
    have hLT_dual_sub : WellFoundedLT (OrderDual (Subobject M)) :=
      (wellFoundedGT_dual_iff (α := OrderDual (Subobject M))).mp hGT_sub
    have : WellFoundedLT (OrderDual (Subobject M)) := hLT_dual_sub
    have hLT_dual_mod : WellFoundedLT (OrderDual (Submodule R M)) :=
      (subobjectModule M).symm.toOrderEmbedding.dual.wellFoundedLT
    exact (wellFoundedGT_dual_iff (α := OrderDual (Submodule R M))).mpr hLT_dual_mod
  · intro hGT_mod
    have hLT_dual_mod : WellFoundedLT (OrderDual (Submodule R M)) :=
      (wellFoundedGT_dual_iff (α := OrderDual (Submodule R M))).mp hGT_mod
    have : WellFoundedLT (OrderDual (Submodule R M)) := hLT_dual_mod
    have hLT_dual_sub : WellFoundedLT (OrderDual (Subobject M)) :=
      (subobjectModule M).toOrderEmbedding.dual.wellFoundedLT
    exact (wellFoundedGT_dual_iff (α := OrderDual (Subobject M))).mpr hLT_dual_sub

/-- Over a noetherian ring, finite generation is exactly the categorical noetherian-object
property in `ModuleCat R`. The proof combines `isNoetherianObject_iff_isNoetherian` with the
algebraic facts `IsNoetherian R M → Module.Finite R M` and
`[IsNoetherianRing R] [Module.Finite R M] → IsNoetherian R M`. -/
theorem isNoetherianObject_iff_finite [IsNoetherianRing R] :
    Module.Finite R M ↔ IsNoetherianObject M := by
  constructor
  · intro hFin
    have : Module.Finite R M := hFin
    have hNoeth : IsNoetherian R M := inferInstance
    exact (isNoetherianObject_iff_isNoetherian M).mpr hNoeth
  · intro hObj
    have hNoeth : IsNoetherian R M := (isNoetherianObject_iff_isNoetherian M).mp hObj
    have : IsNoetherian R M := hNoeth
    exact inferInstance

theorem finite_iff_isNoetherianObject [IsNoetherianRing R] :
    Module.Finite R M ↔ IsNoetherianObject M :=
  isNoetherianObject_iff_finite M

theorem isFG_iff_isNoetherianObject [IsNoetherianRing R] :
    isFG (R := R) M ↔ IsNoetherianObject M := by
  rw [isFG_iff]
  exact isNoetherianObject_iff_finite M

end ModuleCat
