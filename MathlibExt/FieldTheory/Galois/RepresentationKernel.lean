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

A homomorphism from `Gal(ℚ̄/ℚ)` to a finite group whose kernel contains the
fixing subgroup of a finite intermediate field is the kernel of the fixing
subgroup of a finite Galois intermediate field.
-/

@[expose] public section

/-- There is a finite Galois intermediate field whose fixing subgroup is
exactly the kernel of `ρ`, and whose degree divides the order of `G`. -/
theorem GaloisRep.exists_intermediateField_isGalois_fixingSubgroup_eq_ker
    {G : Type*} [Group G] [Finite G]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* G)
    (M : IntermediateField ℚ (AlgebraicClosure ℚ)) (hM : FiniteDimensional ℚ M)
    (hker : M.fixingSubgroup ≤ ρ.ker) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧
      F.fixingSubgroup = ρ.ker ∧ Module.finrank ℚ F ∣ Nat.card G := by
  classical
  haveI hnorm : Normal ℚ (AlgebraicClosure ℚ) := inferInstance
  haveI hsep : Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) :=
    ⟨fun x => (minpoly.irreducible (Algebra.IsIntegral.isIntegral x)).separable⟩
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := IsGalois.mk
  haveI := hM
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
      ⟨by show IsOpen (F.fixingSubgroup :
          Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)); rw [hfix]; exact hopen,
       by rw [hfix]; exact MonoidHom.normal_ker ρ⟩
  haveI : FiniteDimensional ℚ F := hfg.1
  haveI : IsGalois ℚ F := hfg.2
  refine ⟨F, hfg.1, hfg.2, hfix, ?_⟩
  have hk : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker = ρ.ker :=
    (IntermediateField.restrictNormalHom_ker F).trans hfix
  have h1 : Nat.card (F ≃ₐ[ℚ] F) =
      Nat.card ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ ρ.ker) := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (AlgEquiv.restrictNormalHom_surjective (F := ℚ) (E := AlgebraicClosure ℚ)
        (K₁ := F))).toEquiv]
    exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hk).toEquiv
  have h2 : Nat.card ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ ρ.ker) =
      Nat.card ρ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv
  rw [← IsGalois.card_aut_eq_finrank, h1, h2]
  exact Subgroup.card_subgroup_dvd_card ρ.range
