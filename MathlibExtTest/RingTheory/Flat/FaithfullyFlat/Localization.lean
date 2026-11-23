/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The original-type theorem below is adapted from the file
`Thm_IsDiscreteValuationRing_bijective_algebraMap_of_flat_of_isLocalHom_of_isFractionRing.lean`
in `Theorems/` and its paired solution in `P2M/Sol/`, in
https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright 2026 Anthropic, PBC.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The source NOTICE credits Mathlib and its respective authors under Apache 2.0;
ATTRIBUTION.md records no additional per-file notice for these two files.
The statement is preserved; the proof-extraction framework is not used.
-/

module

import MathlibExt.RingTheory.Flat.FaithfullyFlat.Localization
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LaurentSeries

/-!
# Applications and boundaries of faithfully flat birational descent

Named private tests keep their proofs available for transitive axiom audits
and fresh kernel replay, without adding public APIs.
-/

set_option autoImplicit false

-- The complete original type, including its redundant hypotheses.
set_option linter.unusedVariables false in
private theorem local_dvr_bijective
    {O' O F : Type*} [CommRing O'] [IsNoetherianRing O'] [IsLocalRing O']
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field F] [Algebra O' O] [Algebra O F] [Algebra O' F] [IsScalarTower O' O F]
    [IsFractionRing O F] [IsFractionRing O' F]
    [IsLocalHom (algebraMap O' O)] [Module.Flat O' O]
    (hinj : Function.Injective (algebraMap O' O))
    (π : O') (hπ0 : π ≠ 0) (hπ : (Ideal.span {π}).IsPrime) :
    Function.Bijective (algebraMap O' O) := by
  have : Module.FaithfullyFlat O' O :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact IsLocalization.bijective_algebraMap_of_faithfullyFlat O' O F (nonZeroDivisors O')

-- All original hypotheses are jointly realized by a power-series DVR.
private theorem powerSeries_source_witness :
    ∃ π : PowerSeries ℚ, π ≠ 0 ∧ (Ideal.span {π}).IsPrime ∧
      Function.Bijective (algebraMap (PowerSeries ℚ) (PowerSeries ℚ)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_prime (PowerSeries ℚ)
  have hp := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  exact ⟨π, hπ.ne_zero, hp,
    local_dvr_bijective (F := LaurentSeries ℚ) Function.injective_id π hπ.ne_zero hp⟩

-- Any faithfully flat intermediate algebra of a fraction ring is just the base.
private theorem subalgebra_eq_bot {R K : Type*}
    [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K]
    (S : Subalgebra R K) [Module.FaithfullyFlat R S] : S = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨r, hr⟩ :=
    (IsLocalization.bijective_algebraMap_of_faithfullyFlat
      R S K (nonZeroDivisors R)).surjective ⟨x, hx⟩
  exact Algebra.mem_bot.mpr ⟨r, congrArg Subtype.val hr⟩

-- A flat integral birational extension is already the base ring.
private theorem integral_bijective {R S K : Type*}
    [CommRing R] [CommRing S] [Field K]
    [Algebra R S] [Algebra S K] [Algebra R K] [IsScalarTower R S K]
    [IsFractionRing R K] [IsFractionRing S K]
    [Module.Flat R S] [Algebra.IsIntegral R S] :
    Function.Bijective (algebraMap R S) := by
  have : IsDomain S := IsDomain.of_faithfulSMul S K
  have : FaithfulSMul R S :=
    (faithfulSMul_iff_algebraMap_injective R S).mpr (by
      intro a b h
      apply IsFractionRing.injective R K
      simp only [IsScalarTower.algebraMap_apply R S K, h])
  exact IsLocalization.bijective_algebraMap_of_faithfullyFlat R S K (nonZeroDivisors R)

-- A nonvacuous identity case, without any DVR or prime-generator assumptions.
private theorem rat_bijective : Function.Bijective (algebraMap ℚ ℚ) :=
  IsLocalization.bijective_algebraMap_of_faithfullyFlat ℚ ℚ ℚ (nonZeroDivisors ℚ)

-- Total quotient rings allow zero divisors, not just domains.
private theorem zmod_bijective :
    Function.Bijective (algebraMap (ZMod 6) (ZMod 6)) := by
  have : IsFractionRing (ZMod 6) (ZMod 6) :=
    IsLocalization.of_le_isUnit fun _ h ↦
      isUnit_iff_mem_nonZeroDivisors_of_finite.mpr h
  exact IsLocalization.bijective_algebraMap_of_faithfullyFlat
    (ZMod 6) (ZMod 6) (ZMod 6) (nonZeroDivisors (ZMod 6))

-- Q[X, 1/X] is a localization, but not the fraction field Q(X) of Q[X].
private theorem away_X_bijective :
    Function.Bijective (algebraMap (Polynomial ℚ) (Polynomial ℚ)) := by
  have : FaithfulSMul (Polynomial ℚ)
      (Localization.Away (Polynomial.X : Polynomial ℚ)) :=
    (faithfulSMul_iff_algebraMap_injective (Polynomial ℚ)
      (Localization.Away (Polynomial.X : Polynomial ℚ))).mpr
        (IsLocalization.injective (M := Submonoid.powers Polynomial.X) _
          (Submonoid.powers_le.mpr (by simp)))
  exact IsLocalization.bijective_algebraMap_of_faithfullyFlat
    (Polynomial ℚ) (Polynomial ℚ)
    (Localization.Away (Polynomial.X : Polynomial ℚ)) (Submonoid.powers Polynomial.X)

-- Merely flat and birational is insufficient: Z -> Q is not faithfully flat.
private theorem int_rat_flat : Module.Flat ℤ ℚ :=
  IsLocalization.flat ℚ (nonZeroDivisors ℤ)

private theorem int_rat_not_faithfullyFlat : ¬ Module.FaithfullyFlat ℤ ℚ := by
  intro h
  have := h
  have htwo : IsUnit (2 : ℤ) :=
    (isUnit_map_iff (algebraMap ℤ ℚ) 2).mp (by norm_num)
  norm_num [Int.isUnit_iff] at htwo

private theorem int_rat_not_surjective :
    ¬ Function.Surjective (algebraMap ℤ ℚ) := by
  intro h
  exact Int.not_isField (IsFractionRing.surjective_iff_isField.mp h)

-- Faithfully flat is insufficient without birationality.
private theorem polynomial_faithfullyFlat :
    Module.FaithfullyFlat ℚ (Polynomial ℚ) := inferInstance

private theorem polynomial_not_surjective :
    ¬ Function.Surjective (algebraMap ℚ (Polynomial ℚ)) := by
  intro h
  obtain ⟨r, hr⟩ := h Polynomial.X
  have := congrArg (fun p : Polynomial ℚ ↦ p.coeff 1) hr
  simp at this
