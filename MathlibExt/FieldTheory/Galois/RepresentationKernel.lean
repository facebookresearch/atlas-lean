/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_GaloisRep_exists_intermediateField_isGalois_fixingSubgroup_eq_ker.lean`
and
`P2M/Sol/S_GaloisRep_exists_intermediateField_isGalois_fixingSubgroup_eq_ker.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Kernels of representations of the absolute Galois group of `ℚ`

If the kernel of a homomorphism from `Gal(ℚ̄/ℚ)` to a finite group contains
the fixing subgroup of a finite-dimensional intermediate field, then that
kernel is the fixing subgroup of a finite Galois intermediate field, whose
degree over `ℚ` divides the order of the group.
-/

@[expose] public section

/-- **Kernel of a Galois representation as a fixing subgroup.** Let
`ρ : Gal(ℚ̄/ℚ) →* G` be a homomorphism to a finite group `G`, and let `M` be a
finite-dimensional intermediate field of `ℚ̄/ℚ` whose fixing subgroup is
contained in the kernel of `ρ`; this containment, not the finiteness of `G`, is
what makes the kernel open. Then there is a finite Galois intermediate field
whose fixing subgroup is exactly the kernel of `ρ`. Its degree over `ℚ` is the
order of the image of `ρ`, a subgroup of `G`, so it divides the order of `G`. -/
theorem GaloisRep.exists_intermediateField_isGalois_fixingSubgroup_eq_ker
    {G : Type*} [Group G] [Finite G]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* G)
    (M : IntermediateField ℚ (AlgebraicClosure ℚ)) (hM : FiniteDimensional ℚ M)
    (hker : M.fixingSubgroup ≤ ρ.ker) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧
      F.fixingSubgroup = ρ.ker ∧ Module.finrank ℚ F ∣ Nat.card G := by
  have hopen : IsOpen ((ρ.ker :
      Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
    Subgroup.isOpen_mono hker M.fixingSubgroup_isOpen
  have hclosed : IsClosed ((ρ.ker :
      Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
    Subgroup.isClosed_of_isOpen _ hopen
  let H : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := ⟨ρ.ker, hclosed⟩
  set F : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField ρ.ker with hFdef
  have hfix : F.fixingSubgroup = ρ.ker := InfiniteGalois.fixingSubgroup_fixedField H
  have hfg : FiniteDimensional ℚ F ∧ IsGalois ℚ F :=
    (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois F).mp
      ⟨by change IsOpen (F.fixingSubgroup :
          Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)); rw [hfix]; exact hopen,
       by rw [hfix]; exact MonoidHom.normal_ker ρ⟩
  refine ⟨F, hfg.1, hfg.2, hfix, ?_⟩
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, hfix, Subgroup.index_ker]
  exact Subgroup.card_subgroup_dvd_card ρ.range
