/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroRootOrbitData

/-! Exact actual action and whole source flags for the complete external-root transport tree.

The three generators are two genuine Golay permutation isometries and one Golay conjugate of the
actual block isometry `co1XiIsometry`. Each numerator formula of the finite tree is bound to the
corresponding genuine integral Leech action, so every certified tree edge is an equality of actual
preferred short lines. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

private theorem strong_word_apply (w : List (Fin 28)) (i : Fin 24) :
    (golayStrongWord w).val i = golayStrongWordArray w i := by
  induction w generalizing i with
  | nil => rfl
  | cons t w ih =>
    change (golayStrongLetter t).val ((golayStrongWord w).val i) = _
    rw [golayOutsidePairOctad_strong_letter_apply, ih]
    rfl

/-- The actual original Mathieu conjugator used for the first-root-fixing Xi. -/
def generatedFeasibleContainingZeroXiConjugator : golayAutomorphismSubgroup :=
  golayStrongWord [0, 27, 14]

private theorem conjugator_apply (i : Fin 24) :
    generatedFeasibleContainingZeroXiConjugator.val i =
      generatedFeasibleContainingZeroXiConjugatorArray i :=
  strong_word_apply [0, 27, 14] i

private theorem conjugator_inverse_apply (i : Fin 24) :
    generatedFeasibleContainingZeroXiConjugator.val.symm i =
      generatedFeasibleContainingZeroXiConjugatorInverseArray i := by
  apply generatedFeasibleContainingZeroXiConjugator.val.injective
  rw [Equiv.apply_symm_apply, conjugator_apply,
    generatedFeasibleContainingZeroXiConjugatorArray_inverse]

/-- The two actual source-preserving Golay permutation generators. -/
def generatedFeasibleContainingZeroRootMonomial (k : Fin 2) : leechIsomSubgroup :=
  golayPermutationIsometry (generatedFeasibleContainingZeroSupportLetter k)

/-- The actual Golay conjugate of the original block isometry Xi. -/
def generatedFeasibleContainingZeroRootXi : leechIsomSubgroup :=
  golayPermutationIsometry generatedFeasibleContainingZeroXiConjugator⁻¹ *
    co1XiIsometry * golayPermutationIsometry generatedFeasibleContainingZeroXiConjugator

/-- The three actual source-preserving Leech isometries used on the root tree. -/
def generatedFeasibleContainingZeroRootGenerator (k : Fin 3) : leechIsomSubgroup :=
  if k = 0 then generatedFeasibleContainingZeroRootMonomial 0
  else if k = 1 then generatedFeasibleContainingZeroRootMonomial 1
  else generatedFeasibleContainingZeroRootXi

private theorem support_inverse_apply_zero (i : Fin 24) :
    (generatedFeasibleContainingZeroSupportLetter 0).val.symm i =
      golayStrongWordArray [18, 23, 19, 11, 13, 6, 5] i := by
  apply (generatedFeasibleContainingZeroSupportLetter 0).val.injective
  rw [Equiv.apply_symm_apply, generatedFeasibleContainingZeroSupportLetter_apply]
  exact (generatedFeasibleContainingZeroRootMonomial_inverse i).1.symm

private theorem support_inverse_apply_one (i : Fin 24) :
    (generatedFeasibleContainingZeroSupportLetter 1).val.symm i =
      golayStrongLetterArray 25 i := by
  apply (generatedFeasibleContainingZeroSupportLetter 1).val.injective
  rw [Equiv.apply_symm_apply, generatedFeasibleContainingZeroSupportLetter_apply]
  exact (generatedFeasibleContainingZeroRootMonomial_inverse i).2.symm

private theorem guarded_mul (a b : ℤ) : (if a = 0 then 0 else a * b) = a * b := by
  by_cases h : a = 0 <;> simp [h]

private theorem permutation_apply (p : golayAutomorphismSubgroup) (u : leechIntegral)
    (i : Fin 24) :
    (leechIntegralAction (golayPermutationIsometry p) u).val i = u.val (p.val.symm i) := by
  rw [leechIntegralAction_golayPermutation]
  rfl

private theorem monomial_zero_double (u : leechIntegral) (i : Fin 24) :
    2 * (leechIntegralAction (generatedFeasibleContainingZeroRootMonomial 0) u).val i =
      2 * u.val (golayStrongWordArray [18, 23, 19, 11, 13, 6, 5] i) := by
  rw [generatedFeasibleContainingZeroRootMonomial, permutation_apply,
    support_inverse_apply_zero]

private theorem monomial_one_double (u : leechIntegral) (i : Fin 24) :
    2 * (leechIntegralAction (generatedFeasibleContainingZeroRootMonomial 1) u).val i =
      2 * u.val (golayStrongLetterArray 25 i) := by
  rw [generatedFeasibleContainingZeroRootMonomial, permutation_apply,
    support_inverse_apply_one]

private theorem conjugator_inverse_val_symm (i : Fin 24) :
    (generatedFeasibleContainingZeroXiConjugator⁻¹).val.symm i =
      generatedFeasibleContainingZeroXiConjugator.val i := by
  rw [InvMemClass.coe_inv, Equiv.Perm.inv_def, Equiv.symm_symm]

private theorem xi_double (u : leechIntegral) (i : Fin 24) :
    2 * (leechIntegralAction generatedFeasibleContainingZeroRootXi u).val i =
      ∑ j : Fin 24,
        if co1XiNumerator (generatedFeasibleContainingZeroXiConjugatorArray i) j = 0 then 0
        else co1XiNumerator (generatedFeasibleContainingZeroXiConjugatorArray i) j *
          u.val (generatedFeasibleContainingZeroXiConjugatorInverseArray j) := by
  let w := leechIntegralAction
    (golayPermutationIsometry generatedFeasibleContainingZeroXiConjugator) u
  let v := leechIntegralAction co1XiIsometry w
  have hv : (leechIntegralAction generatedFeasibleContainingZeroRootXi u).val i =
      v.val (generatedFeasibleContainingZeroXiConjugator.val i) := by
    rw [generatedFeasibleContainingZeroRootXi, map_mul, map_mul, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, permutation_apply, conjugator_inverse_val_symm]
  have hd := congrArg (fun z : Fin 24 → ℤ => z (generatedFeasibleContainingZeroXiConjugator.val i))
    (co1Xi_integral_double w)
  simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at hd
  have hw (j : Fin 24) : w.val j = u.val (generatedFeasibleContainingZeroXiConjugator.val.symm j) :=
    permutation_apply _ u j
  rw [hv]
  change 2 * v.val _ = _
  rw [hd]
  simp only [Matrix.mulVec, dotProduct, hw, conjugator_inverse_apply, conjugator_apply,
    guarded_mul]

/-- Bind every numerator coordinate to the exact actual integral lattice action. -/
theorem generatedFeasibleContainingZeroRootGenerator_double
    (k : Fin 3) (u : leechIntegral) (i : Fin 24) :
    2 * (leechIntegralAction (generatedFeasibleContainingZeroRootGenerator k) u).val i =
      generatedFeasibleContainingZeroRootNumerator k u.val i := by
  unfold generatedFeasibleContainingZeroRootGenerator generatedFeasibleContainingZeroRootNumerator
  by_cases h0 : k = 0
  · simp only [h0, ↓reduceIte]
    exact monomial_zero_double u i
  · by_cases h1 : k = 1
    · simp only [h1, ↓reduceIte]
      exact monomial_one_double u i
    · simp only [h0, h1, ↓reduceIte]
      exact xi_double u i

private theorem standard_permutation (p : golayAutomorphismSubgroup)
    (hp : ∀ i : Fin 24, (p.val i).val < 8 ↔ i.val < 8) :
    generatedStandardOctadPreserves (golayPermutationIsometry p) := by
  apply generatedStandardOctadPreserves_permutation
  ext i
  have hi := hp (p.val.symm i)
  rw [p.val.apply_symm_apply] at hi
  change (if (p.val.symm i).val < 8 then (1 : ZMod 2) else 0) =
    (if i.val < 8 then 1 else 0)
  simp only [← hi]

private theorem conjugator_flags (i : Fin 24) :
    (generatedFeasibleContainingZeroXiConjugator.val i).val < 8 ↔ i.val < 8 := by
  rw [conjugator_apply]
  exact generatedFeasibleContainingZeroXiConjugatorArray_flags.2.2 i

private theorem conjugator_inverse_flags (i : Fin 24) :
    ((generatedFeasibleContainingZeroXiConjugator⁻¹).val i).val < 8 ↔ i.val < 8 := by
  have h := conjugator_flags ((generatedFeasibleContainingZeroXiConjugator⁻¹).val i)
  have he : generatedFeasibleContainingZeroXiConjugator.val
      ((generatedFeasibleContainingZeroXiConjugator⁻¹).val i) = i :=
    generatedFeasibleContainingZeroXiConjugator.val.apply_symm_apply i
  rw [he] at h
  exact h.symm

private theorem generator_preserves (k : Fin 3) :
    generatedStandardOctadPreserves (generatedFeasibleContainingZeroRootGenerator k) := by
  unfold generatedFeasibleContainingZeroRootGenerator
  by_cases h0 : k = 0
  · simp only [h0, ↓reduceIte]
    exact standard_permutation _ (generatedFeasibleContainingZeroSupportLetter_flags 0).2.2
  · by_cases h1 : k = 1
    · simp only [h1, ↓reduceIte]
      exact standard_permutation _ (generatedFeasibleContainingZeroSupportLetter_flags 1).2.2
    · simp only [h0, h1, ↓reduceIte]
      exact generatedStandardOctadPreserves_mul _ _
        (generatedStandardOctadPreserves_mul _ _
          (standard_permutation _ conjugator_inverse_flags)
          generatedStandardOctadPreserves_xi)
        (standard_permutation _ conjugator_flags)

/-- Each actual generator preserves the entire original source E8 section. -/
theorem generatedFeasibleContainingZeroRootGenerator_section (k : Fin 3) :
    generatedAxisE8ImageSection (generatedFeasibleContainingZeroRootGenerator k)
      (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) =
      generatedAxisE8CoordinateSection
        (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) := by
  have hs := generator_preserves k
  rw [generatedFeasibleContaining_selected_source_word]
  apply generatedAxisE8_preserving_image
  intro u
  simpa only [generatedOctadSupported_standard] using hs u

private theorem first_integral :
    griessShortIntegral (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      fun i => if i = 0 then 4 else if i = 1 then -4 else 0 := by
  funext i
  simp only [griessShortIntegral, generatedFeasiblePhysicalRootPair_coordinates, ite_true]
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> simp_all

/-- Each actual generator fixes the positive original first root with its genuine orientation.
-/
theorem generatedFeasibleContainingZeroRootGenerator_first (k : Fin 3) :
    leechIntegralAction (generatedFeasibleContainingZeroRootGenerator k)
      (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))) =
      griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) := by
  apply Subtype.ext
  funext i
  have h := generatedFeasibleContainingZeroRootGenerator_double k
    (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))) i
  have hv : (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))).val =
      fun i => if i = 0 then 4 else if i = 1 then -4 else 0 := first_integral
  rw [hv, generatedFeasibleContainingZeroRootNumerator_first] at h
  rw [hv]
  generalize (leechIntegralAction (generatedFeasibleContainingZeroRootGenerator k)
    (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)))).val i = a at h ⊢
  by_cases h0 : i = 0
  · simp only [h0, ite_true] at h ⊢
    omega
  · by_cases h1 : i = 1
    · simp only [h1, ite_true, show (1 : Fin 24) ≠ 0 by decide, ite_false] at h ⊢
      omega
    · simp only [h0, h1, ite_false] at h ⊢
      omega

/-- Every tree edge is an equality of actual preferred short lines under the actual word. -/
theorem generatedFeasibleContainingZeroRoot_edge_actual
    (n : Fin 2160) (hn : n ≠ 0) :
    griessShortPermutation
      (generatedFeasibleContainingZeroRootGenerator (generatedFeasibleContainingZeroRootLetter n))
      (generatedFeasibleContainingZeroCachedIndex
        (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootParent n))) =
      generatedFeasibleContainingZeroCachedIndex (generatedFeasibleContainingZeroRootNode n) := by
  let g :=
    generatedFeasibleContainingZeroRootGenerator (generatedFeasibleContainingZeroRootLetter n)
  let r := generatedFeasibleContainingZeroCachedIndex
    (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootParent n))
  let s := generatedFeasibleContainingZeroCachedIndex (generatedFeasibleContainingZeroRootNode n)
  have hcoord (i : Fin 24) :
      2 * (leechIntegralAction g (griessShortLatticeVector r)).val i =
        2 * generatedFeasibleContainingZeroRootSign n * griessShortIntegral s i := by
    have h := generatedFeasibleContainingZeroRootGenerator_double
      (generatedFeasibleContainingZeroRootLetter n) (griessShortLatticeVector r) i
    have hr : (griessShortLatticeVector r).val =
        generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootParent n)) :=
      (generatedFeasibleContainingZeroCachedIntegral_actual _).symm
    rw [hr, generatedFeasibleContainingZeroRoot_edge n hn i,
      generatedFeasibleContainingZeroCachedIntegral_actual] at h
    exact h
  apply (leechRootedA2_short_perm_eq_iff _ _ _).mpr
  rcases generatedFeasibleContainingZeroRootSign_values n with hp | hp
  · left
    apply Subtype.ext
    funext i
    have h := hcoord i
    rw [hp] at h
    change (leechIntegralAction g (griessShortLatticeVector r)).val i = griessShortIntegral s i
    omega
  · right
    apply Subtype.ext
    funext i
    have h := hcoord i
    rw [hp] at h
    change (leechIntegralAction g (griessShortLatticeVector r)).val i = -griessShortIntegral s i
    omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
