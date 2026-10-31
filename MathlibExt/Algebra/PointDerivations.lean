/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_Algebra_PointDerivations.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source file at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Module.Submodule.Defs

/-!
# Point derivations

A point derivation at a `k`-point `ev : A →ₐ[k] k` of a `k`-algebra `A` is
a `k`-linear map `D : A →ₗ[k] M` satisfying the Leibniz rule
`D (a * b) = ev a • D b + ev b • D a`. They form a submodule of
`A →ₗ[k] M`, functorial in `M`, and vanish on constants and on the image
of `algebraMap k A`.
-/

@[expose] public section

universe u v w w'

namespace Algebra

/-- Point derivations at a `k`-point `ev` of a `k`-algebra `A` with values
in a `k`-module `M`. -/
def PointDerivations (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    (ev : A →ₐ[k] k) (M : Type w) [AddCommGroup M] [Module k M] : Submodule k (A →ₗ[k] M) where
  carrier := {D | ∀ a b : A, D (a * b) = ev a • D b + ev b • D a}
  add_mem' := by
    intro D D' hD hD' a b
    simp only [LinearMap.add_apply, hD a b, hD' a b, smul_add]
    ac_rfl
  zero_mem' := by
    intro a b
    simp
  smul_mem' := by
    intro c D hD a b
    simp only [LinearMap.smul_apply, hD a b, smul_add, smul_comm c]

namespace PointDerivations

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] {ev : A →ₐ[k] k}
  {M : Type w} [AddCommGroup M] [Module k M] {M' : Type w'} [AddCommGroup M'] [Module k M']

theorem mem_iff (D : A →ₗ[k] M) :
    D ∈ PointDerivations k A ev M ↔ ∀ a b : A, D (a * b) = ev a • D b + ev b • D a :=
  Iff.rfl

theorem apply_mul {D : A →ₗ[k] M} (hD : D ∈ PointDerivations k A ev M) (a b : A) :
    D (a * b) = ev a • D b + ev b • D a := hD a b

theorem apply_one {D : A →ₗ[k] M} (hD : D ∈ PointDerivations k A ev M) : D 1 = 0 := by
  have h := hD 1 1
  rw [mul_one, show ev 1 = 1 from map_one ev, one_smul] at h
  have h2 : D 1 + D 1 = D 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

theorem apply_algebraMap {D : A →ₗ[k] M} (hD : D ∈ PointDerivations k A ev M) (c : k) :
    D (algebraMap k A c) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, LinearMap.map_smul, apply_one hD, smul_zero]

/-- Functoriality of point derivations in the coefficient module. -/
def map (ev : A →ₐ[k] k) (φ : M →ₗ[k] M') :
    ↥(PointDerivations k A ev M) →ₗ[k] ↥(PointDerivations k A ev M') where
  toFun D := ⟨φ.comp D.1, fun a b => by
    simp only [LinearMap.comp_apply, D.2 a b, map_add, map_smul]⟩
  map_add' D D' := by ext a; simp
  map_smul' c D := by ext a; simp

@[simp] theorem map_apply_coe (ev : A →ₐ[k] k) (φ : M →ₗ[k] M')
    (D : ↥(PointDerivations k A ev M)) (a : A) :
    (map ev φ D : A →ₗ[k] M') a = φ (D.1 a) := rfl

theorem map_id (ev : A →ₐ[k] k) (D : ↥(PointDerivations k A ev M)) :
    map ev (LinearMap.id : M →ₗ[k] M) D = D := by
  ext a; rfl

theorem map_comp {M'' : Type w} [AddCommGroup M''] [Module k M''] (ev : A →ₐ[k] k)
    (φ : M →ₗ[k] M') (ψ : M' →ₗ[k] M'') (D : ↥(PointDerivations k A ev M)) :
    map ev (ψ.comp φ) D = map ev ψ (map ev φ D) := by
  ext a; rfl

end PointDerivations

end Algebra
