/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingNewDestinationSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryActualDestinationClasses

/-! The genuine one-eighth destination is distinct from all five established actual A classes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The original representatives of the five already proved secondary destinations. -/
def generatedFeasibleContainingEstablishedDestinationSource : Fin 5 → GriessSpace :=
  ![conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1,
    generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair,
    generatedFeasibleContainingOctadDestination, generatedFeasibleOutsideOctadDestination,
    generatedFeasibleSecondaryOddDestination]

/-- These are exactly the original representatives of the existing five actual classes. -/
theorem generatedFeasibleContainingEstablishedDestinationSource_class (k : Fin 5) :
    generatedFeasibleSecondaryAClass (generatedFeasibleContainingEstablishedDestinationSource k) =
      generatedFeasibleSecondaryActualDestinations k := by
  fin_cases k <;> rfl

private theorem outside_first :
    (griessConwayEncode generatedFeasibleOutsideOctadDestination).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 0 := by
  rw [generatedFeasibleOutsideOctadDestination, generatedFeasibleOutsideOctadPrototypeLabel,
    generatedAxis_triality_octad_pair_coordinate,
    generatedFeasiblePhysicalRootPair_coordinates]
  have h0 : griessShortVector
      (Sum.inr (Sum.inl (generatedFeasibleOutsideOctadPrototypeIndex, 0))) 0 = 0 := by
    change (griessShortIntegral generatedFeasibleOutsideOctadPrototypeLabel 0 : ℝ) /
      Real.sqrt 8 = 0
    rw [generatedFeasibleOutsideOctadPrototype_integral]
    norm_num
  rw [h0]
  simp

private theorem odd_first :
    (griessConwayEncode generatedFeasibleSecondaryOddDestination).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 1 / 4 := by
  rw [generatedFeasibleSecondaryOddDestination, generatedFeasibleSecondaryOddPrototypeLabel,
    generatedAxis_triality_odd_pair_coordinate, generatedFeasiblePhysicalRootPair_coordinates]
  have hm : golayEncodedMask 0 = 0 := by decide +kernel
  simp only [griessShortVector, griessShortIntegral, Fin.val_zero, hm, Nat.zero_testBit,
    Bool.false_eq_true, ite_false, one_mul]
  norm_num
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  field_simp
  nlinarith

/-- The genuine first coefficients of the five existing representatives. -/
theorem generatedFeasibleContainingEstablishedDestinationSource_first (k : Fin 5) :
    (griessConwayEncode (generatedFeasibleContainingEstablishedDestinationSource k)).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = ![(8 : ℝ), 0, 1, 0, 1 / 4] k := by
  fin_cases k
  · change (griessConwayEncode
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1)).2.1 _ = 8
    rw [conwayShortAxis, griessConwayEncode_decode _]
    · simp [conwayShortAxisRaw]
    · intro i j
      simp [conwayShortAxisRaw, Matrix.vecMulVec_apply, mul_comm]
  · change (griessConwayEncode
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)).2.1 _ = 0
    rw [generatedFeasibleSecondaryAxis_eq_short]
    rw [conwayShortAxis, griessConwayEncode_decode _]
    · simp [conwayShortAxisRaw]
    · intro i j
      simp [conwayShortAxisRaw, Matrix.vecMulVec_apply, mul_comm]
  · exact generatedFeasibleContaining_source_first_coordinate
  · exact outside_first
  · exact odd_first

/-- The actual one-eighth destination differs from every one of the five existing A classes. -/
theorem generatedFeasibleContainingNewDestination_separate (k : Fin 5) :
    generatedFeasibleSecondaryAClass generatedFeasibleContainingNewDestination ≠
      generatedFeasibleSecondaryActualDestinations k := by
  rw [← generatedFeasibleContainingEstablishedDestinationSource_class k]
  intro he
  obtain ⟨h, hh⟩ := (generatedFeasibleSecondaryAClass_eq_iff _ _).mp he
  have hi := generatedFeasibleContaining_first_coordinate_invariant
    generatedFeasiblePhysicalRootPair h generatedFeasibleContainingNewDestination
  rw [hh, generatedFeasibleContainingNewDestination_first_coordinate,
    generatedFeasibleContainingEstablishedDestinationSource_first] at hi
  fin_cases k <;> norm_num at hi

/-- Six genuine, pairwise distinct A classes; completeness of the final feasible list is separate.
-/
def generatedFeasibleContainingSixActualDestinations : Fin 6 →
    generatedFeasibleLocalOrbitSpace generatedFeasiblePhysicalRootPair :=
  Fin.cases (generatedFeasibleSecondaryAClass generatedFeasibleContainingNewDestination)
    generatedFeasibleSecondaryActualDestinations

private theorem fin_prepend_injective {α : Type*} {n : ℕ} (x : α) (f : Fin n → α)
    (hf : Function.Injective f) (hxf : ∀ i, x ≠ f i) :
    Function.Injective (Fin.cases x f) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · intro _
    rfl
  · intro he
    exact False.elim (hxf j he)
  · intro he
    exact False.elim (hxf i he.symm)
  · intro he
    exact congrArg Fin.succ (hf he)

/-- The new actual vector adds a sixth class without asserting full feasible classification. -/
theorem generatedFeasibleContainingSixActualDestinations_injective :
    Function.Injective generatedFeasibleContainingSixActualDestinations :=
  fin_prepend_injective _ _ generatedFeasibleSecondaryActualDestinations_injective
    generatedFeasibleContainingNewDestination_separate

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
