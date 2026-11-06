/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialPlanData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPlanProducts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTensorOperators

/-! Exact complete actual tensor formulas from bounded original signed spin plans. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every checked finite plan binds the full original spin word, including every Parker sign. -/
theorem generatedAxisGlobalComparisonMonomialPlan_sound (k : Fin 8)
    (hc : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedAxisGlobalComparisonMonomialPlan k)) :
    representativeSpinCertificate
      ((generatedAxisGlobalComparisonMonomialWord k).map generatedFourthMonomialSpinLetter).prod
      (generatedAxisGlobalComparisonMonomialModel k).coordinate
      (generatedAxisGlobalComparisonMonomialModel k).phase := by
  have hs : ∀ step ∈ generatedAxisGlobalComparisonMonomialPlan k,
      representativeSpinCertificate (generatedFourthMonomialSpinLetter step.1)
        (generatedFourthMonomialLetterModel step.1).coordinate
        (generatedFourthMonomialLetterModel step.1).phase := by
    intro step _
    exact generatedFourth_monomial_letter_model step.1
  have h := representativeSpinPlan_certificate generatedFourthMonomialSpinLetter
    generatedFourthMonomialLetterModel (generatedAxisGlobalComparisonMonomialPlan k) 1
    representativeSpinIdentityModel representativeSpinCertificate_one hs hc
  rw [representativeSpinPlanEvaluate_eq_product, one_mul] at h
  exact h

/-- Complete compact rational tensor action of an original comparison permutation stretch. -/
def generatedAxisGlobalComparisonMonomialTensor (k : Fin 8)
    (T : GeneratedAxisGlobalRationalTensor) (a : Fin 4096) (i : Fin 24) : ℚ :=
  (generatedAxisGlobalIntSign
    (monsterMonomialQuadratic (fun i j => (generatedAxisGlobalComparisonMonomialModel k).phase i j)
      (golayLabelCoefficients a)) : ℚ) *
    T (generatedAxisGlobalSpinLabel
      ((generatedAxisGlobalComparisonMonomialModel k).coordinate *ᵥ golayLabelCoefficients a))
      ((((generatedAxisGlobalComparisonMonomialWord k).map
        generatedFourthMonomialPermutationLetter).prod).val.symm i)

/-- Every physical output coordinate is the original genuine tensor action. -/
theorem generatedAxisGlobalComparisonMonomialTensor_coordinate (k : Fin 8)
    (hc : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedAxisGlobalComparisonMonomialPlan k))
    (T : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation (((generatedAxisGlobalComparisonMonomialWord k).map
      generatedFourthMonomialFiberLetter).prod) T t i =
    qSign (monsterMonomialQuadratic (fun i j => (generatedAxisGlobalComparisonMonomialModel k).phase i j) t) *
      T ((generatedAxisGlobalComparisonMonomialModel k).coordinate *ᵥ t)
        ((((generatedAxisGlobalComparisonMonomialWord k).map
          generatedFourthMonomialPermutationLetter).prod).val.symm i) := by
  have hspin := generatedAxisGlobalComparisonMonomialPlan_sound k hc
  rw [generatedAxisGlobalTensor_local_coordinate]
  simp_rw [generatedAxisGlobalMonomial_word_spin]
  have he :
      (∑ j : Fin 24,
        (((generatedAxisGlobalComparisonMonomialWord k).map
          generatedFourthMonomialSpinLetter).prod).val (fun u => T u j) t *
        (((generatedAxisGlobalComparisonMonomialWord k).map
          generatedFourthMonomialFiberLetter).prod).val.2.val (Pi.single j 1) i) =
      ∑ j : Fin 24,
        (qSign (monsterMonomialQuadratic
          (fun i j => (generatedAxisGlobalComparisonMonomialModel k).phase i j) t) *
          T ((generatedAxisGlobalComparisonMonomialModel k).coordinate *ᵥ t) j) *
        (((generatedAxisGlobalComparisonMonomialWord k).map
          generatedFourthMonomialFiberLetter).prod).val.2.val (Pi.single j 1) i := by
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun z => z *
      (((generatedAxisGlobalComparisonMonomialWord k).map
        generatedFourthMonomialFiberLetter).prod).val.2.val (Pi.single j 1) i)
      (hspin (fun u => T u j) t)
  rw [he]
  have hs (j : Fin 24) :
      (((generatedAxisGlobalComparisonMonomialWord k).map
        generatedFourthMonomialFiberLetter).prod).val.2.val (Pi.single j 1) i =
      (Pi.single j 1 : Fin 24 → ℝ)
        ((((generatedAxisGlobalComparisonMonomialWord k).map
          generatedFourthMonomialPermutationLetter).prod).val.symm i) := by
    rw [generatedAxisGlobalMonomial_word_spatial]
    rfl
  simp_rw [hs]
  simp [Pi.single_apply]

/-- Bounded matrix/phase checks prove this full rational formula at all physical coordinates. -/
theorem generatedAxisGlobalComparisonMonomialTensor_actual (k : Fin 8)
    (hc : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedAxisGlobalComparisonMonomialPlan k))
    (T : GeneratedAxisGlobalRationalTensor) :
    localTensorRepresentation (((generatedAxisGlobalComparisonMonomialWord k).map
      generatedFourthMonomialFiberLetter).prod) (generatedAxisGlobalRationalTensorReal T) =
      generatedAxisGlobalRationalTensorReal (generatedAxisGlobalComparisonMonomialTensor k T) := by
  funext t i
  obtain ⟨a, rfl⟩ := golayLabelCoefficients_bijective.surjective t
  rw [generatedAxisGlobalComparisonMonomialTensor_coordinate k hc]
  simp only [generatedAxisGlobalRationalTensorReal, generatedAxisGlobalComparisonMonomialTensor,
    generatedAxisGlobalSpinLabel_coeff, Rat.cast_mul, Rat.cast_intCast,
    generatedAxisGlobalIntSign_real]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
