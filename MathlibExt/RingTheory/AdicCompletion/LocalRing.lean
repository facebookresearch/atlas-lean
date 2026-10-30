/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal.lean`,
`P2M/Sol/S_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal.lean`,
`Theorems/Thm_IsLocalRing_comap_map_adicCompletion_eq.lean` and
`P2M/Sol/S_IsLocalRing_comap_map_adicCompletion_eq.lean`
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

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Adic completions of Noetherian local rings

The adic completion of a Noetherian local ring at its maximal ideal is
faithfully flat, so ideals contract back to themselves along the completion
map.
-/

@[expose] public section

open IsLocalRing

/-- The adic completion of a Noetherian local ring at its maximal ideal is
faithfully flat. -/
theorem IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) := by
  rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
  refine ⟨inferInstance, fun I hI htop => ?_⟩
  have hle : (I • ⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) ≤
      (maximalIdeal R) ^ 1 • ⊤ := by
    rw [pow_one]; exact Submodule.smul_mono_left (IsLocalRing.le_maximalIdeal hI)
  rw [htop, top_le_iff, AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian _)] at hle
  have hsurj := AdicCompletion.eval_surjective (maximalIdeal R) R 1
  have hne : ((maximalIdeal R) ^ 1 • ⊤ : Submodule R R) ≠ ⊤ := by
    rw [pow_one, smul_eq_mul, Ideal.mul_top]; exact (maximalIdeal.isMaximal R).ne_top
  have : Nontrivial (R ⧸ ((maximalIdeal R) ^ 1 • ⊤ : Submodule R R)) :=
    Submodule.Quotient.nontrivial_iff.mpr hne
  obtain ⟨q, hq⟩ := exists_ne (0 : R ⧸ ((maximalIdeal R) ^ 1 • ⊤ : Submodule R R))
  obtain ⟨x, rfl⟩ := hsurj q
  have hx : x ∈ LinearMap.ker (AdicCompletion.eval (maximalIdeal R) R 1) :=
    hle ▸ Submodule.mem_top
  exact hq (LinearMap.mem_ker.mp hx)

/-- Ideals contract back to themselves along the adic completion map of a
Noetherian local ring. -/
theorem IsLocalRing.comap_map_adicCompletion_eq
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R) :
    (I.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).comap
      (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) = I := by
  have : Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal R
  exact Ideal.comap_map_eq_self_of_faithfullyFlat I
