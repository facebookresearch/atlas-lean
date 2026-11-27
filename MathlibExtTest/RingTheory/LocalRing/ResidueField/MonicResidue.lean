/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.ResidueField.MonicResidue

@[expose] public section

open Polynomial IsLocalRing

universe u v w

private theorem exactSource
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]
    [Module.Free 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    {F : Type} [CommRing F] [Algebra 𝒪 F]
    (j : A →ₐ[𝒪] F) (hj : Function.Injective j) (x : A)
    (c : IsLocalRing.ResidueField 𝒪) :
    (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (j x) R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C c) ^ R.natDegree) ↔
      IsLocalRing.residue A x = IsLocalRing.ResidueField.map (algebraMap 𝒪 A) c :=
  IsLocalRing.exists_monic_aeval_eq_zero_map_residue_eq_pow_iff_residue_eq_of_injective
    j hj x c

example
    {𝒪 : Type u} [CommRing 𝒪] [IsLocalRing 𝒪]
    {A : Type v} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]
    [Module.Free 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    {F : Type w} [CommRing F] [Algebra 𝒪 F]
    (j : A →ₐ[𝒪] F) (hj : Function.Injective j) (x : A)
    (c : IsLocalRing.ResidueField 𝒪) :
    (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (j x) R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C c) ^ R.natDegree) ↔
      IsLocalRing.residue A x = IsLocalRing.ResidueField.map (algebraMap 𝒪 A) c :=
  IsLocalRing.exists_monic_aeval_eq_zero_map_residue_eq_pow_iff_residue_eq_of_injective
    j hj x c

/-- Boundary: with mismatched residue values, no such monic polynomial exists. -/
example : ¬ ∃ R : Polynomial ℚ, R.Monic ∧ Polynomial.aeval (0 : ℚ) R = 0 ∧
    R.map (IsLocalRing.residue ℚ) =
      (Polynomial.X - Polynomial.C (1 : IsLocalRing.ResidueField ℚ)) ^ R.natDegree := by
  intro h
  have hiff :=
    (IsLocalRing.exists_monic_aeval_eq_zero_map_residue_eq_pow_iff_residue_eq_of_injective
      (AlgHom.id ℚ ℚ) (Function.injective_id) (0 : ℚ)
      (1 : IsLocalRing.ResidueField ℚ)).mp h
  simp at hiff
