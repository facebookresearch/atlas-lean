/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Homology.KoszulComplexAnnihilation
public import MathlibExt.Algebra.Homology.KoszulComplexFamilyReindex

/-!
# Finite-family Koszul Euler characteristics

For a finite coefficient family over a Noetherian ring, finite length of the
quotient by the generated ideal supplies finite length of every Koszul
homology module.  Since the complex vanishes above the cardinality of the
family, this gives canonical finite-length homology data and an Euler
characteristic in arbitrary family size.

No regular-sequence or positive-degree exactness hypothesis is used.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace KoszulComplex

universe u v

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {I : Type v} [Fintype I]

/-- Canonical finite-length homology data for a finite-family Koszul complex
whose coefficient quotient has finite length. -/
noncomputable def familyFiniteLengthHomologyDataOfQuotient
    (a : I → R)
    (hquot : Module.length R (R ⧸ Ideal.span (Set.range a)) ≠ ⊤) :
    HomologicalComplex.FiniteLengthHomologyData R
      (familyComplex R a) where
  cutoff := Fintype.card I + 1
  length_ne_top j _ :=
    familyHomology_length_ne_top_of_quotient R a j hquot
  vanishes j hj := by
    have hX : IsZero ((familyComplex R a).X j) :=
      familyComplex_isZero_above R a j (by omega)
    exact (HomologicalComplex.ExactAt.of_isZero hX).isZero_homology

/-- The finite-family Koszul Euler characteristic, requiring only finite
length of the generated-ideal quotient. -/
noncomputable def familyEulerCharacteristicOfQuotient
    (a : I → R)
    (hquot : Module.length R (R ⧸ Ideal.span (Set.range a)) ≠ ⊤) : ℤ :=
  HomologicalComplex.finiteLengthEulerCharacteristic R
    (familyFiniteLengthHomologyDataOfQuotient R a hquot)

/-- Explicit bounded alternating-sum formula for the finite-family Koszul
Euler characteristic. -/
theorem familyEulerCharacteristicOfQuotient_eq
    (a : I → R)
    (hquot : Module.length R (R ⧸ Ideal.span (Set.range a)) ≠ ⊤) :
    familyEulerCharacteristicOfQuotient R a hquot =
      ∑ j ∈ Finset.range (Fintype.card I + 1),
        (-1 : ℤ) ^ j *
          (Module.length R ((familyComplex R a).homology j)).toNat :=
  rfl

/-- The canonical finite-family Koszul Euler characteristic is invariant
under reindexing the coefficient family by an equivalence. -/
theorem familyEulerCharacteristicOfQuotient_reindex
    {J : Type v} [Fintype J] (a : I → R) (e : I ≃ J)
    (hquot : Module.length R (R ⧸ Ideal.span (Set.range a)) ≠ ⊤) :
    let hquot' : Module.length R
        (R ⧸ Ideal.span (Set.range (fun j => a (e.symm j)))) ≠ ⊤ := by
      rwa [familyReindex_range R a e]
    familyEulerCharacteristicOfQuotient R a hquot =
      familyEulerCharacteristicOfQuotient R
        (fun j => a (e.symm j)) hquot' := by
  let hquot' : Module.length R
      (R ⧸ Ideal.span (Set.range (fun j => a (e.symm j)))) ≠ ⊤ := by
    rwa [familyReindex_range R a e]
  let hdata := familyFiniteLengthHomologyDataOfQuotient R a hquot
  change familyEulerCharacteristicOfQuotient R a hquot =
    familyEulerCharacteristicOfQuotient R (fun j => a (e.symm j)) hquot'
  calc
    familyEulerCharacteristicOfQuotient R a hquot =
        HomologicalComplex.finiteLengthEulerCharacteristic R hdata := rfl
    _ = HomologicalComplex.finiteLengthEulerCharacteristic R
          (familyComplexReindexFiniteLengthData R a e hdata) :=
      familyComplexReindex_eulerCharacteristic R a e hdata
    _ = familyEulerCharacteristicOfQuotient R
          (fun j => a (e.symm j)) hquot' :=
      HomologicalComplex.finiteLengthEulerCharacteristic_eq_of_data R _ _

end KoszulComplex
