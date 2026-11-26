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

/-!
# Noetherian module objects and finite generation

For a ring R and a module object M, the order isomorphism between subobjects of M and
R-submodules identifies categorical noetherianity with algebraic noetherianity. Thus M is a
noetherian object exactly when its R-submodules satisfy the ascending-chain condition.

If R is noetherian, this condition is equivalent to finite generation of M. The ring and
module carrier universe levels are independent.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace ModuleCat

variable {R : Type u} [Ring R] (M : ModuleCat.{v} R)

/-- Categorical and algebraic noetherianity of a module agree.

For any ring R and R-module M, IsNoetherianObject M holds exactly when IsNoetherian R M holds,
through the subobject–submodule order isomorphism. -/
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

/-- Finite generation characterizes noetherian objects over a noetherian ring.

If R is noetherian, an R-module M is finitely generated if and only if it is a noetherian
object of ModuleCat R. -/
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

/-- The finite-module criterion for categorical noetherianity.

Over a noetherian ring R, Module.Finite R M is equivalent to IsNoetherianObject M. -/
theorem finite_iff_isNoetherianObject [IsNoetherianRing R] :
    Module.Finite R M ↔ IsNoetherianObject M :=
  isNoetherianObject_iff_finite M

/-- The finitely generated object predicate and noetherianity.

Over a noetherian ring, the predicate isFG on a module object is equivalent to categorical
noetherianity. -/
theorem isFG_iff_isNoetherianObject [IsNoetherianRing R] :
    isFG (R := R) M ↔ IsNoetherianObject M := by
  rw [isFG_iff]
  exact isNoetherianObject_iff_finite M

end ModuleCat
