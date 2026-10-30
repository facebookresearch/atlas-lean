/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsPrimitiveRoot_exists_ringHom_zeta_eq_of_isCyclotomicExtension.lean` and
`P2M/Sol/S_IsPrimitiveRoot_exists_ringHom_zeta_eq_of_isCyclotomicExtension.lean`
(fermats-last-theorem):
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.
-/

module

public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# Embeddings of cyclotomic extensions

A cyclotomic extension embeds into any characteristic-zero field containing
a primitive `n`-th root of unity, sending the distinguished root to it.
-/

@[expose] public section

/-- A cyclotomic extension `K` of `ℚ` embeds into any characteristic-zero
field `L` containing a primitive `n`-th root of unity, sending the
distinguished root `ζ` to it. -/
theorem IsPrimitiveRoot.exists_ringHom_zeta_eq_of_isCyclotomicExtension
    (n : ℕ) [NeZero n] (K : Type*) [Field K] [Algebra ℚ K]
    [IsCyclotomicExtension {n} ℚ K]
    (L : Type*) [Field L] [CharZero L] (ξ : L) (hξ : IsPrimitiveRoot ξ n) :
    ∃ φ : K →+* L, φ (IsCyclotomicExtension.zeta n ℚ K) = ξ := by
  classical
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ K
  have hirr : Irreducible (Polynomial.cyclotomic n ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)
  let E := hζ.embeddingsEquivPrimitiveRoots L hirr
  have hξmem : ξ ∈ primitiveRoots n L := (mem_primitiveRoots (NeZero.pos n)).mpr hξ
  let φ : K →ₐ[ℚ] L := E.symm ⟨ξ, hξmem⟩
  refine ⟨φ.toRingHom, ?_⟩
  have happly : (E φ : L) = φ (IsCyclotomicExtension.zeta n ℚ K) :=
    hζ.embeddingsEquivPrimitiveRoots_apply_coe L hirr φ
  rw [show E φ = ⟨ξ, hξmem⟩ from E.apply_symm_apply _] at happly
  exact happly.symm
