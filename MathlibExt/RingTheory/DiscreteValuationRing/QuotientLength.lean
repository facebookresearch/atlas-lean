/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsDiscreteValuationRing_length_quotient_map_span_eq_length_mul_length.lean` and
`P2M/Sol/S_IsDiscreteValuationRing_length_quotient_map_span_eq_length_mul_length.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.Length

import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Lengths of principal quotients over a discrete valuation ring

For an injective ring hom `φ : D →+* L` from a discrete valuation ring `D`
to a local domain `L`, the length of `L / (φ f)` factors as the length of
`D / (f)` times the length of `L / 𝔪_D L`.
-/

@[expose] public section

open IsLocalRing

namespace IsDiscreteValuationRing.PrincipalQuotLength

variable {R : Type*} [CommRing R]

private noncomputable def mulQuot (x y : R) :
    (R ⧸ Ideal.span {y}) →ₗ[R] (R ⧸ Ideal.span {x * y}) :=
  Submodule.mapQ (Ideal.span {y}) (Ideal.span {x * y}) (LinearMap.mulLeft R x) (by
    intro z hz
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩)

private theorem mulQuot_mk (x y r : R) :
    mulQuot x y (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (x * r) :=
  rfl

private noncomputable def projQuot (x y : R) :
    (R ⧸ Ideal.span {x * y}) →ₗ[R] (R ⧸ Ideal.span {x}) :=
  Submodule.mapQ (Ideal.span {x * y}) (Ideal.span {x}) LinearMap.id (by
    intro z hz
    rw [Submodule.mem_comap, LinearMap.id_apply]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact Ideal.mem_span_singleton'.mpr ⟨c * y, by ring⟩)

private theorem projQuot_mk (x y r : R) :
    projQuot x y (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ r :=
  rfl

private theorem projQuot_surjective (x y : R) : Function.Surjective (projQuot x y) := by
  intro m
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  exact ⟨Ideal.Quotient.mk _ r, rfl⟩

private theorem mulQuot_injective [IsDomain R] (x y : R) (hx : x ≠ 0) :
    Function.Injective (mulQuot x y) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro m hm
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [LinearMap.mem_ker, mulQuot_mk, Ideal.Quotient.eq_zero_iff_mem] at hm
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hm
  rw [Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.mem_span_singleton'.mpr ⟨s, mul_left_cancel₀ hx ?_⟩
  rw [← hs]; ring

private theorem exact_mulQuot_projQuot (x y : R) :
    Function.Exact (mulQuot x y) (projQuot x y) := by
  intro m
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [projQuot_mk, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hr
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    exact ⟨Ideal.Quotient.mk _ c, by rw [mulQuot_mk, mul_comm x c]⟩
  · rintro ⟨m', hm'⟩
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective m'
    rw [mulQuot_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hm'
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hm'
    refine Ideal.mem_span_singleton'.mpr ⟨r' - s * y, ?_⟩
    have hrr : r = x * r' - s * (x * y) := by rw [hs]; ring
    rw [hrr]; ring

private theorem length_quotient_mul [IsDomain R] (x y : R) (hx : x ≠ 0) :
    Module.length R (R ⧸ Ideal.span {x * y}) =
      Module.length R (R ⧸ Ideal.span {y}) + Module.length R (R ⧸ Ideal.span {x}) :=
  Module.length_eq_add_of_exact (mulQuot x y) (projQuot x y)
    (mulQuot_injective x y hx) (projQuot_surjective x y) (exact_mulQuot_projQuot x y)

private theorem length_quotient_pow [IsDomain R] (x : R) (hx : x ≠ 0) (m : ℕ) :
    Module.length R (R ⧸ Ideal.span {x ^ m}) =
      m * Module.length R (R ⧸ Ideal.span {x}) := by
  induction m with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, Module.length_eq_zero_iff,
      Ideal.span_singleton_one]
    infer_instance
  | succ m ih =>
    rw [pow_succ', length_quotient_mul x _ hx, ih, Nat.cast_succ]
    ring

private theorem length_quotient_unit_mul {a : R} (ha : IsUnit a) (x : R) :
    Module.length R (R ⧸ Ideal.span {a * x}) = Module.length R (R ⧸ Ideal.span {x}) := by
  rw [Ideal.span_singleton_mul_left_unit ha]

end IsDiscreteValuationRing.PrincipalQuotLength

open IsDiscreteValuationRing.PrincipalQuotLength in
/-- For `φ : D →+* L` injective, `D` a DVR and `L` a local domain,
`length_L (L / (φ f)) = length_D (D / (f)) * length_L (L / 𝔪_D L)`. -/
public theorem IsDiscreteValuationRing.length_quotient_map_span_eq_length_mul_length
    {D L : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [CommRing L] [IsDomain L] [IsLocalRing L]
    (φ : D →+* L) (hφ0 : Function.Injective φ) (f : D) (hf : f ≠ 0) :
    Module.length L (L ⧸ Ideal.span {φ f}) =
      Module.length D (D ⧸ Ideal.span {f}) *
        Module.length L (L ⧸ Ideal.map φ (IsLocalRing.maximalIdeal D)) := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible D
  have hmax : IsLocalRing.maximalIdeal D = Ideal.span {t} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hf ht
  have ht0 : t ≠ 0 := ht.ne_zero
  have hφt0 : φ t ≠ 0 := fun h => ht0 (hφ0 (by rw [h, map_zero]))
  have hD : Module.length D (D ⧸ Ideal.span {(u : D) * t ^ m}) = m := by
    rw [length_quotient_unit_mul u.isUnit, length_quotient_pow t ht0, ← hmax]
    have h1 : Module.length D (D ⧸ IsLocalRing.maximalIdeal D) = 1 :=
      Module.length_eq_one_iff.mpr (isSimpleModule_iff_quot_maximal.mpr
        ⟨IsLocalRing.maximalIdeal D, inferInstance,
          ⟨LinearEquiv.refl D (D ⧸ IsLocalRing.maximalIdeal D)⟩⟩)
    rw [h1, mul_one]
  have hL : Module.length L (L ⧸ Ideal.span {φ ((u : D) * t ^ m)}) =
      m * Module.length L (L ⧸ Ideal.span {φ t}) := by
    rw [map_mul, map_pow, length_quotient_unit_mul (u.isUnit.map φ),
      length_quotient_pow (φ t) hφt0]
  rw [hL, hD, hmax, Ideal.map_span, Set.image_singleton]
