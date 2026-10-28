/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact physical operators of the literal compact source permutation words. -/
module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsGolayData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every finite coordinate permutation gives its ordinary ambient real relabeling. -/
def representativeRealPermutationHom :
    Equiv.Perm (Fin 24) →* ((Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ)) where
  toFun := golayRealPermute
  map_one' := by ext f i; rfl
  map_mul' _ _ := by ext f i; rfl

/-- The ambient physical operator is a genuine projection of the actual defining fiber. -/
def representativeFiberLeechAmbient :
    localFiberSubgroup →* ((Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ)) where
  toFun g := g.val.2.val
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem representativeNodeLeech_signed (n : Fin 15) (negative : Bool)
    (h : representativeFiberLeechAmbient (representativeNodeFiber n) =
      representativeRealPermutationHom (representativeNodePhysicalPermutation n)⁻¹) :
    representativeFiberLeechAmbient (representativeNodeLetterFiber (n, negative)) =
      representativeRealPermutationHom (representativeNodePhysicalLetter (n, negative)) := by
  cases negative with
  | false => exact h
  | true =>
    change representativeFiberLeechAmbient ((representativeNodeFiber n)⁻¹) = _
    rw [map_inv, h, ← map_inv, inv_inv]
    rfl

private theorem representativeNodeLeech_word (word : List RepresentativeNodeLetter)
    (h : ∀ letter ∈ word,
      representativeFiberLeechAmbient (representativeNodeLetterFiber letter) =
        representativeRealPermutationHom (representativeNodePhysicalLetter letter)) :
    representativeFiberLeechAmbient (word.map representativeNodeLetterFiber).prod =
      representativeRealPermutationHom (word.map representativeNodePhysicalLetter).prod := by
  rw [map_list_prod, map_list_prod]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro letter hletter
  exact h letter hletter

/-- Exact ambient physical operator of actual compact node 0. -/
theorem representativeNodeLeech_certificate0 :
    representativeFiberLeechAmbient (representativeNodeFiber 0) =
      representativeRealPermutationHom (representativeNodePhysicalPermutation 0)⁻¹ := by
  have hc : representativeNodePhysicalPermutation (0 : Fin 15) =
      omegaOrbitPermutation 0 := representativeNodePhysical_original_certificate 0
  rw [hc]
  exact (map_inv representativeRealPermutationHom (omegaOrbitPermutation 0)).symm

/-- Exact ambient physical operator of actual compact node 1. -/
theorem representativeNodeLeech_certificate1 :
    representativeFiberLeechAmbient (representativeNodeFiber 1) =
      representativeRealPermutationHom (representativeNodePhysicalPermutation 1)⁻¹ := by
  have hc : representativeNodePhysicalPermutation (1 : Fin 15) =
      omegaOrbitPermutation 1 := representativeNodePhysical_original_certificate 1
  rw [hc]
  exact (map_inv representativeRealPermutationHom (omegaOrbitPermutation 1)).symm

/-- Exact ambient physical operator of actual compact node 2. -/
theorem representativeNodeLeech_certificate2 :
    representativeFiberLeechAmbient (representativeNodeFiber 2) =
      representativeRealPermutationHom (representativeNodePhysicalPermutation 2)⁻¹ := by
  have hletters : ∀ letter ∈ representativeNodeWord 2,
      representativeFiberLeechAmbient (representativeNodeLetterFiber letter) =
        representativeRealPermutationHom (representativeNodePhysicalLetter letter) := by
    intro letter hletter
    change letter ∈ [
      (0, false),
      (1, false),
      (0, true)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2
    · rw [h0]
      exact representativeNodeLeech_signed 0 false
        representativeNodeLeech_certificate0
    · rw [h1]
      exact representativeNodeLeech_signed 1 false
        representativeNodeLeech_certificate1
    · rw [h2]
      exact representativeNodeLeech_signed 0 true
        representativeNodeLeech_certificate0
  have hw : ((representativeNodeWord 2).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 2 := by
    change ([representativeNodeFiber0, representativeNodeFiber1, representativeNodeFiber0⁻¹] : List
      localFiberSubgroup).prod =
      representativeNodeFiber2
    rw [representativeNodeFiber2]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rw [← hw, representativeNodeLeech_word _ hletters,
    representativeNodePhysical_word_certificate 2 (by decide +kernel)]

/-- Exact ambient physical operator of actual compact node 3. -/
theorem representativeNodeLeech_certificate3 :
    representativeFiberLeechAmbient (representativeNodeFiber 3) =
      representativeRealPermutationHom (representativeNodePhysicalPermutation 3)⁻¹ := by
  have hletters : ∀ letter ∈ representativeNodeWord 3,
      representativeFiberLeechAmbient (representativeNodeLetterFiber letter) =
        representativeRealPermutationHom (representativeNodePhysicalLetter letter) := by
    intro letter hletter
    change letter ∈ [
      (0, false),
      (0, false),
      (1, false),
      (0, true),
      (0, true)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2 | h3 | h4
    · rw [h0]
      exact representativeNodeLeech_signed 0 false
        representativeNodeLeech_certificate0
    · rw [h1]
      exact representativeNodeLeech_signed 0 false
        representativeNodeLeech_certificate0
    · rw [h2]
      exact representativeNodeLeech_signed 1 false
        representativeNodeLeech_certificate1
    · rw [h3]
      exact representativeNodeLeech_signed 0 true
        representativeNodeLeech_certificate0
    · rw [h4]
      exact representativeNodeLeech_signed 0 true
        representativeNodeLeech_certificate0
  have hw : ((representativeNodeWord 3).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 3 := by
    change ([representativeNodeFiber0, representativeNodeFiber0, representativeNodeFiber1,
      representativeNodeFiber0⁻¹, representativeNodeFiber0⁻¹] : List localFiberSubgroup).prod =
      representativeNodeFiber3
    rw [representativeNodeFiber3]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rw [← hw, representativeNodeLeech_word _ hletters,
    representativeNodePhysical_word_certificate 3 (by decide +kernel)]

/-- Exact ambient physical operator of actual compact node 4. -/
theorem representativeNodeLeech_certificate4 :
    representativeFiberLeechAmbient (representativeNodeFiber 4) =
      representativeRealPermutationHom (representativeNodePhysicalPermutation 4)⁻¹ := by
  have hletters : ∀ letter ∈ representativeNodeWord 4,
      representativeFiberLeechAmbient (representativeNodeLetterFiber letter) =
        representativeRealPermutationHom (representativeNodePhysicalLetter letter) := by
    intro letter hletter
    change letter ∈ [
      (1, false),
      (3, false),
      (1, false)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2
    · rw [h0]
      exact representativeNodeLeech_signed 1 false
        representativeNodeLeech_certificate1
    · rw [h1]
      exact representativeNodeLeech_signed 3 false
        representativeNodeLeech_certificate3
    · rw [h2]
      exact representativeNodeLeech_signed 1 false
        representativeNodeLeech_certificate1
  have hw : ((representativeNodeWord 4).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 4 := by
    change ([representativeNodeFiber1, representativeNodeFiber3, representativeNodeFiber1] : List
      localFiberSubgroup).prod =
      representativeNodeFiber4
    rw [representativeNodeFiber4]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rw [← hw, representativeNodeLeech_word _ hletters,
    representativeNodePhysical_word_certificate 4 (by decide +kernel)]

/-- Exact ambient physical operator of actual compact node 5. -/
theorem representativeNodeLeech_certificate5 :
    representativeFiberLeechAmbient (representativeNodeFiber 5) =
      representativeRealPermutationHom (representativeNodePhysicalPermutation 5)⁻¹ := by
  have hletters : ∀ letter ∈ representativeNodeWord 5,
      representativeFiberLeechAmbient (representativeNodeLetterFiber letter) =
        representativeRealPermutationHom (representativeNodePhysicalLetter letter) := by
    intro letter hletter
    change letter ∈ [
      (3, false),
      (1, false),
      (3, false)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2
    · rw [h0]
      exact representativeNodeLeech_signed 3 false
        representativeNodeLeech_certificate3
    · rw [h1]
      exact representativeNodeLeech_signed 1 false
        representativeNodeLeech_certificate1
    · rw [h2]
      exact representativeNodeLeech_signed 3 false
        representativeNodeLeech_certificate3
  have hw : ((representativeNodeWord 5).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 5 := by
    change ([representativeNodeFiber3, representativeNodeFiber1, representativeNodeFiber3] : List
      localFiberSubgroup).prod =
      representativeNodeFiber5
    rw [representativeNodeFiber5]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rw [← hw, representativeNodeLeech_word _ hletters,
    representativeNodePhysical_word_certificate 5 (by decide +kernel)]

/-- Exact ambient physical operator of actual compact node 6. -/
theorem representativeNodeLeech_certificate6 :
    representativeFiberLeechAmbient (representativeNodeFiber 6) =
      representativeRealPermutationHom (representativeNodePhysicalPermutation 6)⁻¹ := by
  have hletters : ∀ letter ∈ representativeNodeWord 6,
      representativeFiberLeechAmbient (representativeNodeLetterFiber letter) =
        representativeRealPermutationHom (representativeNodePhysicalLetter letter) := by
    intro letter hletter
    change letter ∈ [
      (1, false),
      (2, false),
      (3, false),
      (2, false),
      (1, false)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2 | h3 | h4
    · rw [h0]
      exact representativeNodeLeech_signed 1 false
        representativeNodeLeech_certificate1
    · rw [h1]
      exact representativeNodeLeech_signed 2 false
        representativeNodeLeech_certificate2
    · rw [h2]
      exact representativeNodeLeech_signed 3 false
        representativeNodeLeech_certificate3
    · rw [h3]
      exact representativeNodeLeech_signed 2 false
        representativeNodeLeech_certificate2
    · rw [h4]
      exact representativeNodeLeech_signed 1 false
        representativeNodeLeech_certificate1
  have hw : ((representativeNodeWord 6).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 6 := by
    change ([representativeNodeFiber1, representativeNodeFiber2, representativeNodeFiber3,
      representativeNodeFiber2, representativeNodeFiber1] : List localFiberSubgroup).prod =
      representativeNodeFiber6
    rw [representativeNodeFiber6]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rw [← hw, representativeNodeLeech_word _ hletters,
    representativeNodePhysical_word_certificate 6 (by decide +kernel)]

/-- Exact ambient physical operator of actual compact node 7. -/
theorem representativeNodeLeech_certificate7 :
    representativeFiberLeechAmbient (representativeNodeFiber 7) =
      representativeRealPermutationHom (representativeNodePhysicalPermutation 7)⁻¹ := by
  have hletters : ∀ letter ∈ representativeNodeWord 7,
      representativeFiberLeechAmbient (representativeNodeLetterFiber letter) =
        representativeRealPermutationHom (representativeNodePhysicalLetter letter) := by
    intro letter hletter
    change letter ∈ [
      (2, false),
      (3, false),
      (2, false),
      (3, false),
      (1, false),
      (2, false)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2 | h3 | h4 | h5
    · rw [h0]
      exact representativeNodeLeech_signed 2 false
        representativeNodeLeech_certificate2
    · rw [h1]
      exact representativeNodeLeech_signed 3 false
        representativeNodeLeech_certificate3
    · rw [h2]
      exact representativeNodeLeech_signed 2 false
        representativeNodeLeech_certificate2
    · rw [h3]
      exact representativeNodeLeech_signed 3 false
        representativeNodeLeech_certificate3
    · rw [h4]
      exact representativeNodeLeech_signed 1 false
        representativeNodeLeech_certificate1
    · rw [h5]
      exact representativeNodeLeech_signed 2 false
        representativeNodeLeech_certificate2
  have hw : ((representativeNodeWord 7).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 7 := by
    change ([representativeNodeFiber2, representativeNodeFiber3, representativeNodeFiber2,
      representativeNodeFiber3, representativeNodeFiber1, representativeNodeFiber2] : List
      localFiberSubgroup).prod =
      representativeNodeFiber7
    rw [representativeNodeFiber7]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rw [← hw, representativeNodeLeech_word _ hletters,
    representativeNodePhysical_word_certificate 7 (by decide +kernel)]

/-- Exact ambient physical operator of actual compact node 8. -/
theorem representativeNodeLeech_certificate8 :
    representativeFiberLeechAmbient (representativeNodeFiber 8) =
      representativeRealPermutationHom (representativeNodePhysicalPermutation 8)⁻¹ := by
  have hletters : ∀ letter ∈ representativeNodeWord 8,
      representativeFiberLeechAmbient (representativeNodeLetterFiber letter) =
        representativeRealPermutationHom (representativeNodePhysicalLetter letter) := by
    intro letter hletter
    change letter ∈ [
      (4, false),
      (7, false),
      (4, false)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2
    · rw [h0]
      exact representativeNodeLeech_signed 4 false
        representativeNodeLeech_certificate4
    · rw [h1]
      exact representativeNodeLeech_signed 7 false
        representativeNodeLeech_certificate7
    · rw [h2]
      exact representativeNodeLeech_signed 4 false
        representativeNodeLeech_certificate4
  have hw : ((representativeNodeWord 8).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 8 := by
    change ([representativeNodeFiber4, representativeNodeFiber7, representativeNodeFiber4] : List
      localFiberSubgroup).prod =
      representativeNodeFiber8
    rw [representativeNodeFiber8]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rw [← hw, representativeNodeLeech_word _ hletters,
    representativeNodePhysical_word_certificate 8 (by decide +kernel)]

/-- Exact ambient physical operator of actual compact node 9. -/
theorem representativeNodeLeech_certificate9 :
    representativeFiberLeechAmbient (representativeNodeFiber 9) =
      representativeRealPermutationHom (representativeNodePhysicalPermutation 9)⁻¹ := by
  have hletters : ∀ letter ∈ representativeNodeWord 9,
      representativeFiberLeechAmbient (representativeNodeLetterFiber letter) =
        representativeRealPermutationHom (representativeNodePhysicalLetter letter) := by
    intro letter hletter
    change letter ∈ [
      (5, false),
      (8, false),
      (5, false),
      (8, true),
      (5, false)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2 | h3 | h4
    · rw [h0]
      exact representativeNodeLeech_signed 5 false
        representativeNodeLeech_certificate5
    · rw [h1]
      exact representativeNodeLeech_signed 8 false
        representativeNodeLeech_certificate8
    · rw [h2]
      exact representativeNodeLeech_signed 5 false
        representativeNodeLeech_certificate5
    · rw [h3]
      exact representativeNodeLeech_signed 8 true
        representativeNodeLeech_certificate8
    · rw [h4]
      exact representativeNodeLeech_signed 5 false
        representativeNodeLeech_certificate5
  have hw : ((representativeNodeWord 9).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 9 := by
    change ([representativeNodeFiber5, representativeNodeFiber8, representativeNodeFiber5,
      representativeNodeFiber8⁻¹, representativeNodeFiber5] : List localFiberSubgroup).prod =
      representativeNodeFiber9
    rw [representativeNodeFiber9]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rw [← hw, representativeNodeLeech_word _ hletters,
    representativeNodePhysical_word_certificate 9 (by decide +kernel)]

/-- Exact ambient physical operator of actual compact node 10. -/
theorem representativeNodeLeech_certificate10 :
    representativeFiberLeechAmbient (representativeNodeFiber 10) =
      representativeRealPermutationHom (representativeNodePhysicalPermutation 10)⁻¹ := by
  have hletters : ∀ letter ∈ representativeNodeWord 10,
      representativeFiberLeechAmbient (representativeNodeLetterFiber letter) =
        representativeRealPermutationHom (representativeNodePhysicalLetter letter) := by
    intro letter hletter
    change letter ∈ [
      (7, false),
      (4, false),
      (7, true),
      (8, true),
      (8, true),
      (9, false)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2 | h3 | h4 | h5
    · rw [h0]
      exact representativeNodeLeech_signed 7 false
        representativeNodeLeech_certificate7
    · rw [h1]
      exact representativeNodeLeech_signed 4 false
        representativeNodeLeech_certificate4
    · rw [h2]
      exact representativeNodeLeech_signed 7 true
        representativeNodeLeech_certificate7
    · rw [h3]
      exact representativeNodeLeech_signed 8 true
        representativeNodeLeech_certificate8
    · rw [h4]
      exact representativeNodeLeech_signed 8 true
        representativeNodeLeech_certificate8
    · rw [h5]
      exact representativeNodeLeech_signed 9 false
        representativeNodeLeech_certificate9
  have hw : ((representativeNodeWord 10).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 10 := by
    change ([representativeNodeFiber7, representativeNodeFiber4, representativeNodeFiber7⁻¹,
      representativeNodeFiber8⁻¹, representativeNodeFiber8⁻¹, representativeNodeFiber9] : List
      localFiberSubgroup).prod =
      representativeNodeFiber10
    rw [representativeNodeFiber10]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rw [← hw, representativeNodeLeech_word _ hletters,
    representativeNodePhysical_word_certificate 10 (by decide +kernel)]

/-- Exact ambient physical operator of actual compact node 11. -/
theorem representativeNodeLeech_certificate11 :
    representativeFiberLeechAmbient (representativeNodeFiber 11) =
      representativeRealPermutationHom (representativeNodePhysicalPermutation 11)⁻¹ := by
  have hletters : ∀ letter ∈ representativeNodeWord 11,
      representativeFiberLeechAmbient (representativeNodeLetterFiber letter) =
        representativeRealPermutationHom (representativeNodePhysicalLetter letter) := by
    intro letter hletter
    change letter ∈ [
      (0, false),
      (0, false),
      (0, false),
      (1, false),
      (0, true),
      (0, true),
      (0,
      true),
      (3, false),
      (2, false),
      (1, false),
      (3, false),
      (2, false),
      (6, false),
      (7, true),
      (5,
      false),
      (6, false),
      (4, false),
      (8, true),
      (8, true),
      (5, false),
      (8, true),
      (9, false),
      (10,
      true)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 |
      h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22
    · rw [h0]
      exact representativeNodeLeech_signed 0 false
        representativeNodeLeech_certificate0
    · rw [h1]
      exact representativeNodeLeech_signed 0 false
        representativeNodeLeech_certificate0
    · rw [h2]
      exact representativeNodeLeech_signed 0 false
        representativeNodeLeech_certificate0
    · rw [h3]
      exact representativeNodeLeech_signed 1 false
        representativeNodeLeech_certificate1
    · rw [h4]
      exact representativeNodeLeech_signed 0 true
        representativeNodeLeech_certificate0
    · rw [h5]
      exact representativeNodeLeech_signed 0 true
        representativeNodeLeech_certificate0
    · rw [h6]
      exact representativeNodeLeech_signed 0 true
        representativeNodeLeech_certificate0
    · rw [h7]
      exact representativeNodeLeech_signed 3 false
        representativeNodeLeech_certificate3
    · rw [h8]
      exact representativeNodeLeech_signed 2 false
        representativeNodeLeech_certificate2
    · rw [h9]
      exact representativeNodeLeech_signed 1 false
        representativeNodeLeech_certificate1
    · rw [h10]
      exact representativeNodeLeech_signed 3 false
        representativeNodeLeech_certificate3
    · rw [h11]
      exact representativeNodeLeech_signed 2 false
        representativeNodeLeech_certificate2
    · rw [h12]
      exact representativeNodeLeech_signed 6 false
        representativeNodeLeech_certificate6
    · rw [h13]
      exact representativeNodeLeech_signed 7 true
        representativeNodeLeech_certificate7
    · rw [h14]
      exact representativeNodeLeech_signed 5 false
        representativeNodeLeech_certificate5
    · rw [h15]
      exact representativeNodeLeech_signed 6 false
        representativeNodeLeech_certificate6
    · rw [h16]
      exact representativeNodeLeech_signed 4 false
        representativeNodeLeech_certificate4
    · rw [h17]
      exact representativeNodeLeech_signed 8 true
        representativeNodeLeech_certificate8
    · rw [h18]
      exact representativeNodeLeech_signed 8 true
        representativeNodeLeech_certificate8
    · rw [h19]
      exact representativeNodeLeech_signed 5 false
        representativeNodeLeech_certificate5
    · rw [h20]
      exact representativeNodeLeech_signed 8 true
        representativeNodeLeech_certificate8
    · rw [h21]
      exact representativeNodeLeech_signed 9 false
        representativeNodeLeech_certificate9
    · rw [h22]
      exact representativeNodeLeech_signed 10 true
        representativeNodeLeech_certificate10
  have hw : ((representativeNodeWord 11).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 11 := by
    change ([representativeNodeFiber0, representativeNodeFiber0, representativeNodeFiber0,
      representativeNodeFiber1, representativeNodeFiber0⁻¹, representativeNodeFiber0⁻¹,
      representativeNodeFiber0⁻¹, representativeNodeFiber3, representativeNodeFiber2,
      representativeNodeFiber1, representativeNodeFiber3, representativeNodeFiber2,
      representativeNodeFiber6, representativeNodeFiber7⁻¹, representativeNodeFiber5,
      representativeNodeFiber6, representativeNodeFiber4, representativeNodeFiber8⁻¹,
      representativeNodeFiber8⁻¹, representativeNodeFiber5, representativeNodeFiber8⁻¹,
      representativeNodeFiber9, representativeNodeFiber10⁻¹] : List localFiberSubgroup).prod =
      representativeNodeFiber11
    rw [representativeNodeFiber11]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rw [← hw, representativeNodeLeech_word _ hletters,
    representativeNodePhysical_word_certificate 11 (by decide +kernel)]

/-- Exact ambient physical operator of actual compact node 12. -/
theorem representativeNodeLeech_certificate12 :
    representativeFiberLeechAmbient (representativeNodeFiber 12) =
      representativeRealPermutationHom (representativeNodePhysicalPermutation 12)⁻¹ := by
  have hletters : ∀ letter ∈ representativeNodeWord 12,
      representativeFiberLeechAmbient (representativeNodeLetterFiber letter) =
        representativeRealPermutationHom (representativeNodePhysicalLetter letter) := by
    intro letter hletter
    change letter ∈ [
      (10, false),
      (11, false),
      (10, true)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2
    · rw [h0]
      exact representativeNodeLeech_signed 10 false
        representativeNodeLeech_certificate10
    · rw [h1]
      exact representativeNodeLeech_signed 11 false
        representativeNodeLeech_certificate11
    · rw [h2]
      exact representativeNodeLeech_signed 10 true
        representativeNodeLeech_certificate10
  have hw : ((representativeNodeWord 12).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 12 := by
    change ([representativeNodeFiber10, representativeNodeFiber11, representativeNodeFiber10⁻¹] :
      List localFiberSubgroup).prod =
      representativeNodeFiber12
    rw [representativeNodeFiber12]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rw [← hw, representativeNodeLeech_word _ hletters,
    representativeNodePhysical_word_certificate 12 (by decide +kernel)]

/-- Exact ambient physical operator of actual compact node 13. -/
theorem representativeNodeLeech_certificate13 :
    representativeFiberLeechAmbient (representativeNodeFiber 13) =
      representativeRealPermutationHom (representativeNodePhysicalPermutation 13)⁻¹ := by
  have hletters : ∀ letter ∈ representativeNodeWord 13,
      representativeFiberLeechAmbient (representativeNodeLetterFiber letter) =
        representativeRealPermutationHom (representativeNodePhysicalLetter letter) := by
    intro letter hletter
    change letter ∈ [
      (9, false),
      (11, false),
      (9, false)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2
    · rw [h0]
      exact representativeNodeLeech_signed 9 false
        representativeNodeLeech_certificate9
    · rw [h1]
      exact representativeNodeLeech_signed 11 false
        representativeNodeLeech_certificate11
    · rw [h2]
      exact representativeNodeLeech_signed 9 false
        representativeNodeLeech_certificate9
  have hw : ((representativeNodeWord 13).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 13 := by
    change ([representativeNodeFiber9, representativeNodeFiber11, representativeNodeFiber9] : List
      localFiberSubgroup).prod =
      representativeNodeFiber13
    rw [representativeNodeFiber13]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rw [← hw, representativeNodeLeech_word _ hletters,
    representativeNodePhysical_word_certificate 13 (by decide +kernel)]

/-- Exact ambient physical operator of actual compact node 14. -/
theorem representativeNodeLeech_certificate14 :
    representativeFiberLeechAmbient (representativeNodeFiber 14) =
      representativeRealPermutationHom (representativeNodePhysicalPermutation 14)⁻¹ := by
  have hletters : ∀ letter ∈ representativeNodeWord 14,
      representativeFiberLeechAmbient (representativeNodeLetterFiber letter) =
        representativeRealPermutationHom (representativeNodePhysicalLetter letter) := by
    intro letter hletter
    change letter ∈ [
      (10, false),
      (13, false),
      (10, true)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2
    · rw [h0]
      exact representativeNodeLeech_signed 10 false
        representativeNodeLeech_certificate10
    · rw [h1]
      exact representativeNodeLeech_signed 13 false
        representativeNodeLeech_certificate13
    · rw [h2]
      exact representativeNodeLeech_signed 10 true
        representativeNodeLeech_certificate10
  have hw : ((representativeNodeWord 14).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 14 := by
    change ([representativeNodeFiber10, representativeNodeFiber13, representativeNodeFiber10⁻¹] :
      List localFiberSubgroup).prod =
      representativeNodeFiber14
    rw [representativeNodeFiber14]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rw [← hw, representativeNodeLeech_word _ hletters,
    representativeNodePhysical_word_certificate 14 (by decide +kernel)]

/-- All fifteen actual compact node words have their exact physical coordinate operators. -/
theorem representativeNodeLeech_certificate (n : Fin 15) :
    representativeFiberLeechAmbient (representativeNodeFiber n) =
      representativeRealPermutationHom (representativeNodePhysicalPermutation n)⁻¹ := by
  fin_cases n
  · exact representativeNodeLeech_certificate0
  · exact representativeNodeLeech_certificate1
  · exact representativeNodeLeech_certificate2
  · exact representativeNodeLeech_certificate3
  · exact representativeNodeLeech_certificate4
  · exact representativeNodeLeech_certificate5
  · exact representativeNodeLeech_certificate6
  · exact representativeNodeLeech_certificate7
  · exact representativeNodeLeech_certificate8
  · exact representativeNodeLeech_certificate9
  · exact representativeNodeLeech_certificate10
  · exact representativeNodeLeech_certificate11
  · exact representativeNodeLeech_certificate12
  · exact representativeNodeLeech_certificate13
  · exact representativeNodeLeech_certificate14

/-- Every corrected target word has exactly the recorded source physical permutation.
The cocode correction has identity physical action, while its spin sign is retained separately. -/
theorem representativePermutationLeech_certificate (n : Fin 83) :
    representativeFiberLeechAmbient (representativePermutationFiber n) =
      representativeRealPermutationHom (representativePermutationPhysicalPermutation n)⁻¹ := by
  have hletters : ∀ letter ∈ representativePermutationWord n,
      representativeFiberLeechAmbient (representativeNodeLetterFiber letter) =
        representativeRealPermutationHom (representativeNodePhysicalLetter letter) := by
    intro letter _
    exact representativeNodeLeech_signed letter.1 letter.2
      (representativeNodeLeech_certificate letter.1)
  rw [representativePermutationFiber, map_mul]
  have hq : representativeFiberLeechAmbient
      (localFiberIncl (sourceQCocode
        (golayLabelCoefficients (representativePermutationCorrection n)))) = 1 := rfl
  rw [hq, one_mul, representativeNodeLeech_word _ hletters,
    representativePermutationPhysical_word_certificate]

/-- Evaluation gives every coordinate of the actual target's full physical operator. -/
theorem representativePermutationLeech_apply (n : Fin 83) (f : Fin 24 → ℝ) (i : Fin 24) :
    (representativePermutationFiber n).val.2.val f i =
      f (representativePermutationPhysicalImages n i) := by
  change representativeFiberLeechAmbient (representativePermutationFiber n) f i = _
  rw [representativePermutationLeech_certificate]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
