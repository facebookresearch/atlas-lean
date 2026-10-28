/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightFlagData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismIncidence
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightPreparationMonomial

/-! Count the genuine code signs fixing both original vectors in the root-8 flag. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every coordinate occupied by either of the two actual point vectors. -/
def generatedFifthRootEightPointSignCoordinates : Fin 10 → Fin 24 :=
  ![1, 2, 8, 11, 16, 17, 18, 19, 20, 22]

/-- Original code signs vanish at all ten occupied coordinates. -/
def generatedFifthRootEightPointSignCondition (a : Fin 4096) : Prop :=
  ∀ k : Fin 10, (golayEncodedMask a.val).testBit
    (generatedFifthRootEightPointSignCoordinates k).val = false

instance : DecidablePred generatedFifthRootEightPointSignCondition := fun a => by
  unfold generatedFifthRootEightPointSignCondition
  infer_instance

/-- The exact finite labels of signs fixing both actual point vectors. -/
def generatedFifthRootEightPointSignLabels : Finset (Fin 4096) :=
  Finset.univ.filter generatedFifthRootEightPointSignCondition

set_option maxRecDepth 10000 in
set_option maxHeartbeats 64000000 in
-- Count all 4096 original code labels through their complete occupied-coordinate masks.
/-- Exactly eight original Golay sign labels fix this entire point flag. -/
theorem generatedFifthRootEight_point_sign_labels_card :
    generatedFifthRootEightPointSignLabels.card = 8 := by
  decide +kernel

/-- The genuine original code signs fixing the norm 4 and norm 6 vectors pointwise. -/
def generatedFifthRootEightPointSigns : Set golayCode :=
  {c | leechIntegralAction (golaySignIsometry c) generatedFifthRootEightNormFour =
      generatedFifthRootEightNormFour ∧
    leechIntegralAction (golaySignIsometry c) generatedFifthRootEightNormSix =
      generatedFifthRootEightNormSix}

private theorem integer_sign_fix (c : Fin 24 → ZMod 2) (f : Fin 24 → ℤ) :
    golayIntegerSign c f = f ↔ ∀ i, f i ≠ 0 → c i = 0 := by
  constructor
  · intro h i hi
    have hc := congrFun h i
    by_contra hn
    simp only [golayIntegerSign, hn, ite_false] at hc
    omega
  · intro h
    funext i
    by_cases hi : f i = 0
    · simp [golayIntegerSign, hi]
    · simp [golayIntegerSign, h i hi]

private theorem point_support (i : Fin 24) :
    (generatedFifthRootEightNormFourVector i ≠ 0 ∨
      generatedFifthRootEightNormSixVector i ≠ 0) ↔
    ∃ k, generatedFifthRootEightPointSignCoordinates k = i := by
  revert i
  decide +kernel

private theorem point_signs_occupied (c : Fin 24 → ZMod 2) :
    (golayIntegerSign c generatedFifthRootEightNormFourVector =
        generatedFifthRootEightNormFourVector ∧
      golayIntegerSign c generatedFifthRootEightNormSixVector =
        generatedFifthRootEightNormSixVector) ↔
      ∀ k, c (generatedFifthRootEightPointSignCoordinates k) = 0 := by
  rw [integer_sign_fix, integer_sign_fix]
  constructor
  · rintro ⟨hx, hy⟩ k
    rcases (point_support (generatedFifthRootEightPointSignCoordinates k)).mpr ⟨k, rfl⟩ with h | h
    · exact hx _ h
    · exact hy _ h
  · intro h
    constructor
    · intro i hi
      obtain ⟨k, rfl⟩ := (point_support i).mp (Or.inl hi)
      exact h k
    · intro i hi
      obtain ⟨k, rfl⟩ := (point_support i).mp (Or.inr hi)
      exact h k

private theorem point_label_zero (a : Fin 4096) (k : Fin 10) :
    golayEncoder (golayLabelCoefficients a) (generatedFifthRootEightPointSignCoordinates k) = 0 ↔
      (golayEncodedMask a.val).testBit (generatedFifthRootEightPointSignCoordinates k).val =
        false := by
  rw [← ZMod.val_eq_zero, golayLabelEncoder_match]
  cases hb : (golayEncodedMask a.val).testBit
    (generatedFifthRootEightPointSignCoordinates k).val <;> simp

/-- Both full integer conditions are the actual original lattice actions of the code sign. -/
theorem generatedFifthRootEight_point_sign_label_iff (a : Fin 4096) :
    a ∈ generatedFifthRootEightPointSignLabels ↔
      golayCodeLabelEquiv a ∈ generatedFifthRootEightPointSigns := by
  simp only [generatedFifthRootEightPointSignLabels, Finset.mem_filter,
    Finset.mem_univ, true_and, generatedFifthRootEightPointSigns, Set.mem_ofPred_eq]
  have hc : generatedFifthRootEightPointSignCondition a ↔
      (golayIntegerSign (golayEncoder (golayLabelCoefficients a))
          generatedFifthRootEightNormFourVector = generatedFifthRootEightNormFourVector ∧
        golayIntegerSign (golayEncoder (golayLabelCoefficients a))
          generatedFifthRootEightNormSixVector = generatedFifthRootEightNormSixVector) := by
    rw [point_signs_occupied]
    exact (forall_congr' (point_label_zero a)).symm
  rw [hc]
  constructor
  · rintro ⟨h, k⟩
    constructor
    · apply Subtype.ext
      rw [leechIntegralAction_golaySign]
      exact h
    · apply Subtype.ext
      rw [leechIntegralAction_golaySign]
      exact k
  · rintro ⟨h, k⟩
    constructor
    · have hv := congrArg (fun z : leechIntegral => z.val) h
      rw [leechIntegralAction_golaySign] at hv
      exact hv
    · have hv := congrArg (fun z : leechIntegral => z.val) k
      rw [leechIntegralAction_golaySign] at hv
      exact hv

/-- The finite source labels parameterize all genuine pointwise-fixing Golay signs. -/
def generatedFifthRootEightPointSignEquiv :
    ↥generatedFifthRootEightPointSignLabels ≃ generatedFifthRootEightPointSigns :=
  golayCodeLabelEquiv.subtypeEquiv (fun a =>
    generatedFifthRootEight_point_sign_label_iff a)

/-- Exactly eight actual code sign isometries fix both original flag vectors pointwise. -/
theorem generatedFifthRootEight_point_signs_card :
    Nat.card generatedFifthRootEightPointSigns = 8 := by
  rw [← Nat.card_congr generatedFifthRootEightPointSignEquiv,
    Nat.card_eq_fintype_card, Fintype.card_coe, generatedFifthRootEight_point_sign_labels_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
