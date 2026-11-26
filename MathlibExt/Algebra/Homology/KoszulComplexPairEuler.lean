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

public import MathlibExt.Algebra.Homology.KoszulComplexFamilyReindex
public import MathlibExt.Algebra.Homology.KoszulComplexHomologyZero
public import MathlibExt.Algebra.Homology.KoszulComplexFamilyEuler
import Mathlib.Tactic.IntervalCases

/-!
# Length Euler data for a two-generator Koszul complex

Only degrees 0,1,2 can occur in the Koszul complex on (f,g). Finite lengths of these homology
modules give finite-length homology data with cutoff 3 and Euler value ℓ(H₀)−ℓ(H₁)+ℓ(H₂),
where H₀ ≅ R/(f,g).

Over a noetherian ring, finite length of R/(f,g) implies finite length of all Koszul homology,
giving the Euler value from this single quotient hypothesis. The Euler value is invariant
under swapping f and g.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace KoszulComplex

universe u

variable (R : Type u) [CommRing R]

/-- Finite lengths of the three pair homology degrees.

Record finite R-length for H₀,H₁,H₂ of K(f,g). -/
structure PairHomologyFiniteLength (f g : R) : Prop where
/-- Finite length of degree-zero pair homology.

The module H₀(K(f,g)) has finite length. -/
  degree_zero : Module.length R
    ((familyComplex R (pairFamily R f g)).homology 0) ≠ ⊤
/-- Finite length of degree-one pair homology.

The module H₁(K(f,g)) has finite length. -/
  degree_one : Module.length R
    ((familyComplex R (pairFamily R f g)).homology 1) ≠ ⊤
/-- Finite length of degree-two pair homology.

The module H₂(K(f,g)) has finite length. -/
  degree_two : Module.length R
    ((familyComplex R (pairFamily R f g)).homology 2) ≠ ⊤

/-- The pair degree-zero homology is the pair-ideal quotient.

Identify H₀(K(f,g)) with R/(f,g) as R-modules. -/
noncomputable def pairHomologyZeroLinearEquivQuotient (f g : R) :
    (familyComplex R (pairFamily R f g)).homology 0 ≃ₗ[R]
      R ⧸ Ideal.span ({f, g} : Set R) := by
  rw [← pairFamily_range R f g]
  exact familyHomologyZeroLinearEquivQuotient R (pairFamily R f g)

/-- The length of pair degree-zero homology.

Its R-length equals ℓ_R(R/(f,g)). -/
theorem pairHomologyZero_length_eq_quotient (f g : R) :
    Module.length R
        ((familyComplex R (pairFamily R f g)).homology 0) =
      Module.length R (R ⧸ Ideal.span ({f, g} : Set R)) :=
  (pairHomologyZeroLinearEquivQuotient R f g).length_eq

/-- A finite pair quotient gives finite Koszul homology over a noetherian ring.

If R is noetherian and R/(f,g) has finite length, every homology degree of K(f,g) has finite
length. -/
theorem pairHomology_length_ne_top_of_quotient
    [IsNoetherianRing R] (f g : R) (n : ℕ)
    (hquot : Module.length R
      (R ⧸ Ideal.span ({f, g} : Set R)) ≠ ⊤) :
    Module.length R
      ((familyComplex R (pairFamily R f g)).homology n) ≠ ⊤ := by
  rw [← pairFamily_range R f g] at hquot
  exact familyHomology_length_ne_top_of_quotient R
    (pairFamily R f g) n hquot

/-- Pair homology length data from the quotient and higher degrees.

Finite length of R/(f,g), H₁ and H₂ supplies the three-degree finiteness record. -/
theorem PairHomologyFiniteLength.of_quotient
    {f g : R}
    (degree_zero_quotient :
      Module.length R (R ⧸ Ideal.span ({f, g} : Set R)) ≠ ⊤)
    (degree_one : Module.length R
      ((familyComplex R (pairFamily R f g)).homology 1) ≠ ⊤)
    (degree_two : Module.length R
      ((familyComplex R (pairFamily R f g)).homology 2) ≠ ⊤) :
    PairHomologyFiniteLength R f g where
  degree_zero := by
    rw [pairHomologyZero_length_eq_quotient]
    exact degree_zero_quotient
  degree_one := degree_one
  degree_two := degree_two

/-- Pair homology length data from a finite noetherian quotient.

For noetherian R, finite length of R/(f,g) supplies all three homology finiteness conditions. -/
theorem PairHomologyFiniteLength.of_quotient_noetherian
    [IsNoetherianRing R] {f g : R}
    (hquot : Module.length R
      (R ⧸ Ideal.span ({f, g} : Set R)) ≠ ⊤) :
    PairHomologyFiniteLength R f g :=
  PairHomologyFiniteLength.of_quotient R hquot
    (pairHomology_length_ne_top_of_quotient R f g 1 hquot)
    (pairHomology_length_ne_top_of_quotient R f g 2 hquot)

/-- Pair homology finiteness is invariant under swapping generators.

Finite homology lengths for (f,g) give them for (g,f). -/
theorem PairHomologyFiniteLength.swap
    {f g : R} (h : PairHomologyFiniteLength R f g) :
    PairHomologyFiniteLength R g f where
  degree_zero := by
    rw [← pairComplexSwap_homology_length_eq R f g 0]
    exact h.degree_zero
  degree_one := by
    rw [← pairComplexSwap_homology_length_eq R f g 1]
    exact h.degree_one
  degree_two := by
    rw [← pairComplexSwap_homology_length_eq R f g 2]
    exact h.degree_two

/-- The pair complex finite-length homology data.

Use cutoff 3, the three finite-length hypotheses and vanishing above degree two. -/
noncomputable def pairFiniteLengthHomologyData
    (f g : R) (h : PairHomologyFiniteLength R f g) :
    HomologicalComplex.FiniteLengthHomologyData R
      (familyComplex R (pairFamily R f g)) where
  cutoff := 3
  length_ne_top j hj := by
    interval_cases j
    · exact h.degree_zero
    · exact h.degree_one
    · exact h.degree_two
  vanishes j hj := by
    have hX : IsZero
        ((familyComplex R (pairFamily R f g)).X j) :=
      familyComplex_isZero_above R (pairFamily R f g) j (by
        simp
        omega)
    exact (HomologicalComplex.ExactAt.of_isZero hX).isZero_homology

/-- The Euler characteristic of a pair Koszul complex.

Take the finite-length Euler invariant of K(f,g) using its three-degree homology data. -/
noncomputable def pairEulerCharacteristic
    (f g : R) (h : PairHomologyFiniteLength R f g) : ℤ :=
  HomologicalComplex.finiteLengthEulerCharacteristic R
    (pairFiniteLengthHomologyData R f g h)

/-- The three-term pair Euler formula.

The value is ℓ(H₀)−ℓ(H₁)+ℓ(H₂), with finite lengths interpreted as integers. -/
theorem pairEulerCharacteristic_eq
    (f g : R) (h : PairHomologyFiniteLength R f g) :
    pairEulerCharacteristic R f g h =
      (Module.length R
          ((familyComplex R (pairFamily R f g)).homology 0)).toNat -
        (Module.length R
          ((familyComplex R (pairFamily R f g)).homology 1)).toNat +
        (Module.length R
          ((familyComplex R (pairFamily R f g)).homology 2)).toNat := by
  simp only [pairEulerCharacteristic,
    HomologicalComplex.finiteLengthEulerCharacteristic,
    pairFiniteLengthHomologyData, Finset.sum_range_succ,
    Finset.sum_range_zero, pow_zero, pow_succ, one_mul, neg_mul,
    mul_neg, neg_neg, zero_add]
  rw [sub_eq_add_neg]

/-- The pair Euler formula with the quotient in degree zero.

The value is ℓ(R/(f,g))−ℓ(H₁)+ℓ(H₂). -/
theorem pairEulerCharacteristic_eq_quotient
    (f g : R) (h : PairHomologyFiniteLength R f g) :
    pairEulerCharacteristic R f g h =
      (Module.length R (R ⧸ Ideal.span ({f, g} : Set R))).toNat -
        (Module.length R
          ((familyComplex R (pairFamily R f g)).homology 1)).toNat +
        (Module.length R
          ((familyComplex R (pairFamily R f g)).homology 2)).toNat := by
  rw [pairEulerCharacteristic_eq,
    pairHomologyZero_length_eq_quotient]

/-- The pair Euler value obtained from a finite noetherian quotient.

For noetherian R and finite-length R/(f,g), use the induced family homology data to define the
pair Euler invariant. -/
noncomputable def pairEulerCharacteristicOfQuotient
    [IsNoetherianRing R] (f g : R)
    (hquot : Module.length R
      (R ⧸ Ideal.span ({f, g} : Set R)) ≠ ⊤) : ℤ :=
  familyEulerCharacteristicOfQuotient R (pairFamily R f g) (by
    rw [pairFamily_range R f g]
    exact hquot)

/-- The quotient-defined pair Euler formula.

The quotient-defined value is ℓ(R/(f,g))−ℓ(H₁)+ℓ(H₂). -/
theorem pairEulerCharacteristicOfQuotient_eq
    [IsNoetherianRing R] (f g : R)
    (hquot : Module.length R
      (R ⧸ Ideal.span ({f, g} : Set R)) ≠ ⊤) :
    pairEulerCharacteristicOfQuotient R f g hquot =
      (Module.length R (R ⧸ Ideal.span ({f, g} : Set R))).toNat -
        (Module.length R
          ((familyComplex R (pairFamily R f g)).homology 1)).toNat +
        (Module.length R
          ((familyComplex R (pairFamily R f g)).homology 2)).toNat := by
  let hpair := PairHomologyFiniteLength.of_quotient_noetherian R hquot
  calc
    pairEulerCharacteristicOfQuotient R f g hquot =
        HomologicalComplex.finiteLengthEulerCharacteristic R
          (pairFiniteLengthHomologyData R f g hpair) :=
      HomologicalComplex.finiteLengthEulerCharacteristic_eq_of_data R _ _
    _ = pairEulerCharacteristic R f g hpair := rfl
    _ = _ := pairEulerCharacteristic_eq_quotient R f g hpair

/-- Finite-length homology data transported to the swapped pair.

Transport the pair data through the canonical complex swap isomorphism. -/
noncomputable def pairHomologyFiniteLengthSwap
    (f g : R) (h : PairHomologyFiniteLength R f g) :
    HomologicalComplex.FiniteLengthHomologyData R
      (familyComplex R (pairFamily R g f)) :=
  (pairFiniteLengthHomologyData R f g h).mapIso R
    (pairComplexSwapIso R f g)

/-- The pair Euler value under transported swap data.

The Euler invariant equals that of the swapped complex with the transported finite-length
data. -/
theorem pairEulerCharacteristic_swap
    (f g : R) (h : PairHomologyFiniteLength R f g) :
    pairEulerCharacteristic R f g h =
      HomologicalComplex.finiteLengthEulerCharacteristic R
        (pairHomologyFiniteLengthSwap R f g h) :=
  pairComplexSwap_eulerCharacteristic R f g
    (pairFiniteLengthHomologyData R f g h)

/-- Symmetry of the pair Euler characteristic.

The Euler value for (f,g) equals that for (g,f) with swapped finiteness data. -/
theorem pairEulerCharacteristic_comm
    (f g : R) (h : PairHomologyFiniteLength R f g) :
    pairEulerCharacteristic R f g h =
      pairEulerCharacteristic R g f h.swap := by
  calc
    pairEulerCharacteristic R f g h =
        HomologicalComplex.finiteLengthEulerCharacteristic R
          (pairHomologyFiniteLengthSwap R f g h) :=
      pairEulerCharacteristic_swap R f g h
    _ = HomologicalComplex.finiteLengthEulerCharacteristic R
          (pairFiniteLengthHomologyData R g f h.swap) :=
      HomologicalComplex.finiteLengthEulerCharacteristic_eq_of_data R _ _
    _ = pairEulerCharacteristic R g f h.swap := rfl

/-- Symmetry of the quotient-defined pair Euler characteristic.

For a finite noetherian pair quotient, swapping f and g leaves the quotient-defined Euler
invariant unchanged. -/
theorem pairEulerCharacteristicOfQuotient_comm
    [IsNoetherianRing R] (f g : R)
    (hquot : Module.length R
      (R ⧸ Ideal.span ({f, g} : Set R)) ≠ ⊤) :
    let hquot' : Module.length R
        (R ⧸ Ideal.span ({g, f} : Set R)) ≠ ⊤ := by
      rwa [Ideal.span_pair_comm]
    pairEulerCharacteristicOfQuotient R f g hquot =
      pairEulerCharacteristicOfQuotient R g f hquot' := by
  let hquot' : Module.length R
      (R ⧸ Ideal.span ({g, f} : Set R)) ≠ ⊤ := by
    rwa [Ideal.span_pair_comm]
  let hfg := PairHomologyFiniteLength.of_quotient_noetherian R hquot
  let hgf := PairHomologyFiniteLength.of_quotient_noetherian R hquot'
  change pairEulerCharacteristicOfQuotient R f g hquot =
    pairEulerCharacteristicOfQuotient R g f hquot'
  calc
    pairEulerCharacteristicOfQuotient R f g hquot =
        pairEulerCharacteristic R f g hfg :=
      HomologicalComplex.finiteLengthEulerCharacteristic_eq_of_data R _ _
    _ = pairEulerCharacteristic R g f hfg.swap :=
      pairEulerCharacteristic_comm R f g hfg
    _ = pairEulerCharacteristicOfQuotient R g f hquot' :=
      (HomologicalComplex.finiteLengthEulerCharacteristic_eq_of_data
        R _ _).symm

end KoszulComplex
