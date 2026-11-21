/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul.lean`
and
`P2M/Sol/S_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
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

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

set_option autoImplicit false

open TensorProduct

namespace Module.FaithfullyFlat

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]

/-- The degree-zero Amitsur difference map `b ↦ b ⊗ 1 - 1 ⊗ b`. -/
private noncomputable def amitsurDelta : B →ₗ[A] B ⊗[A] B :=
  (TensorProduct.mk A B B).flip 1 - TensorProduct.mk A B B 1

private theorem amitsurDelta_apply (b : B) :
    amitsurDelta (A := A) (B := B) b = b ⊗ₜ[A] (1 : B) - (1 : B) ⊗ₜ[A] b :=
  rfl

private theorem tmul_algebraMap (a : A) :
    algebraMap A B a ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] algebraMap A B a := by
  rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]

private theorem amitsurDelta_comp_linearMap :
    amitsurDelta (A := A) (B := B) ∘ₗ Algebra.linearMap A B = 0 := by
  ext a
  simp only [LinearMap.comp_apply, Algebra.linearMap_apply,
    LinearMap.zero_apply, amitsurDelta_apply, tmul_algebraMap, sub_self]

private noncomputable def amitsurContraction :
    B ⊗[A] (B ⊗[A] B) →ₗ[A] B ⊗[A] B :=
  (LinearMap.mul' A B).rTensor B ∘ₗ
    (TensorProduct.assoc A B B B).symm.toLinearMap

private theorem amitsurContraction_lTensor_amitsurDelta (x : B ⊗[A] B) :
    amitsurContraction (A := A) (B := B)
        ((amitsurDelta (A := A) (B := B)).lTensor B x) =
      (LinearMap.mul' A B x) ⊗ₜ[A] (1 : B) - x := by
  induction x using TensorProduct.induction_on with
  | zero => simp [amitsurContraction]
  | tmul b c =>
      simp [amitsurContraction, amitsurDelta_apply, LinearMap.lTensor_tmul,
        TensorProduct.tmul_sub, TensorProduct.sub_tmul,
        TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul,
        LinearMap.mul'_apply]
  | add x y hx hy =>
      simp only [map_add, hx, hy, TensorProduct.add_tmul]
      abel

private theorem exact_lTensor_linearMap_lTensor_amitsurDelta :
    Function.Exact ((Algebra.linearMap A B).lTensor B)
      ((amitsurDelta (A := A) (B := B)).lTensor B) := by
  intro x
  constructor
  · intro hx
    refine ⟨(LinearMap.mul' A B x) ⊗ₜ[A] (1 : A), ?_⟩
    have h := amitsurContraction_lTensor_amitsurDelta (A := A) (B := B) x
    rw [hx, map_zero, eq_comm, sub_eq_zero] at h
    rw [LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one, h]
  · rintro ⟨y, rfl⟩
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      amitsurDelta_comp_linearMap, LinearMap.lTensor_zero,
      LinearMap.zero_apply]

private theorem exact_linearMap_amitsurDelta [Module.FaithfullyFlat A B] :
    Function.Exact (Algebra.linearMap A B)
      (amitsurDelta (A := A) (B := B)) :=
  (Module.FaithfullyFlat.lTensor_exact_iff_exact A B _ _).mp
    exact_lTensor_linearMap_lTensor_amitsurDelta

/-- Amitsur exactness in degree zero: if `B` is faithfully flat over `A`
and `b ⊗ 1 = 1 ⊗ b` in `B ⊗[A] B`, then `b` comes from `A`. -/
public theorem exists_algebraMap_eq_of_tmul_one_eq_one_tmul
    [Module.FaithfullyFlat A B] {b : B}
    (hb : b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b) :
    ∃ a : A, algebraMap A B a = b := by
  obtain ⟨a, ha⟩ :=
    ((exact_linearMap_amitsurDelta (A := A) (B := B)) b).mp
      (by rw [amitsurDelta_apply, hb, sub_self])
  exact ⟨a, ha⟩

end Module.FaithfullyFlat
