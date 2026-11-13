/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The statement is adapted from
`Theorems/Thm_Algebra_exists_algHom_forall_apply_ne_zero_of_finiteType_of_isAlgClosed.lean`
and its paired
`P2M/Sol/S_Algebra_exists_algHom_forall_apply_ne_zero_of_finiteType_of_isAlgClosed.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE credits Mathlib, copyright the respective Mathlib authors,
released under Apache 2.0. The proof below uses Mathlib's Jacobson-ring API
rather than the source's explicit localization construction.
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Rational points avoiding finitely many functions

A finite family of nonzero elements of a finite-type domain over an
algebraically closed field is simultaneously nonzero at some rational point.
-/

public section

set_option autoImplicit false

namespace Algebra

/-- A finite family of nonzero functions on an integral affine variety over an
algebraically closed field is simultaneously nonzero at some rational point.
The family may be empty, and the field may have any characteristic. -/
theorem exists_algHom_forall_ne_zero
    {k : Type*} [Field k] [IsAlgClosed k]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra k B] [FiniteType k B]
    {ι : Type*} [Finite ι] (g : ι → B) (hg : ∀ i, g i ≠ 0) :
    ∃ χ : B →ₐ[k] k, ∀ i, χ (g i) ≠ 0 := by
  classical
  let _ := Fintype.ofFinite ι
  let _ : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := k)
  have hbot : (⊥ : Ideal B).jacobson = ⊥ := by
    rw [← Ideal.radical_eq_jacobson, Ideal.radical_bot_of_isReduced]
  obtain ⟨m, ⟨_, hm⟩, hprod⟩ := Ideal.eq_jacobson_iff_notMem.mp hbot
    (∏ i, g i) (by simpa using Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hg i))
  let _ := hm
  let _ := Ideal.Quotient.field m
  have := finite_of_finite_type_of_isJacobsonRing k (B ⧸ m)
  let φ : (B ⧸ m) →ₐ[k] k := IsAlgClosed.lift
  let χ : B →ₐ[k] k := φ.comp (Ideal.Quotient.mkₐ k m)
  have hχ : χ (∏ i, g i) ≠ 0 := by
    intro h
    exact hprod (Ideal.Quotient.eq_zero_iff_mem.mp
      (φ.injective (h.trans (map_zero φ).symm)))
  refine ⟨χ, fun i ↦ ?_⟩
  rw [map_prod] at hχ
  exact Finset.prod_ne_zero_iff.mp hχ i (Finset.mem_univ i)

end Algebra
