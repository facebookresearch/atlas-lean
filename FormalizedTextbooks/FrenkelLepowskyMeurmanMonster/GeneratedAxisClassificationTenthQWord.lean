/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignFullImage

/-! Complete source extraspecial conjugation of genuine original fifth normalization words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- A genuine original source stage in the complete spin and spatial fiber. -/
def generatedTenthQStageFiber (k : Fin 14) (j : Fin 7) : localFiberSubgroup :=
  (if generatedAxisGlobalFifthShortNormalizationXi k j then xiSpinLocalFiber else 1) *
    (generatedFifthSignFiber (generatedAxisGlobalFifthShortNormalizationSigns k j) 0 *
      ((generatedAxisGlobalFifthShortNormalizationWords k j).map
        generatedFourthMonomialFiberLetter).prod)

/-- Every source stage retains the actual original H word and its central phases. -/
theorem generatedTenth_Q_stage_fiber_local (k : Fin 14) (j : Fin 7) :
    localFiberIntoH (generatedTenthQStageFiber k j) =
      generatedAxisGlobalFifthShortNormalizationLocal k j := by
  rw [generatedTenthQStageFiber, map_mul, map_mul, generatedFifth_sign_fiber_local,
    generatedAxisGlobalFifthShortNormalizationLocal]
  congr 1
  cases generatedAxisGlobalFifthShortNormalizationXi k j <;> simp

/-- The entire genuine original seven-stage source word in the original fiber. -/
def generatedTenthQWordFiber (k : Fin 14) : localFiberSubgroup :=
  generatedAxisGlobalWordChain (fun j => generatedTenthQStageFiber k
    ⟨j % 7, Nat.mod_lt _ (by decide)⟩) 7

/-- The complete actual fiber word maps to the original seven-stage normalization in H. -/
theorem generatedTenth_Q_word_fiber_local (k : Fin 14) :
    localFiberIntoH (generatedTenthQWordFiber k) = generatedAxisGlobalFifthShortLocalWord k := by
  rw [generatedTenthQWordFiber, generatedAxisGlobalWordChain_map,
    generatedAxisGlobalFifthShortLocalWord]
  congr 1
  funext j
  exact generatedTenth_Q_stage_fiber_local k _

/-- The full inverse original monomial image includes its signed source cochain. -/
def generatedTenthQInverseMonomialImage (k : Fin 2) (q : Q) : Q :=
  monsterMonomialDiagonalImage (monsterSourcePermutationPhaseData k)
    (monsterMonomialPermutationImage (monsterSourcePermutationCode k).symm q)

private theorem inverse_diagonal_image (M : Fin 12 → Fin 12 → ZMod 2) (q : Q) :
    spinConjugation (monsterMonomialDiagonalHolomorph M)⁻¹ q =
      monsterMonomialDiagonalImage M q := by
  have hs : monsterMonomialDiagonalHolomorph M * monsterMonomialDiagonalHolomorph M = 1 := by
    apply Subtype.ext
    apply LinearEquiv.ext
    exact monsterMonomialDiagonal_involutive M
  rw [inv_eq_of_mul_eq_one_right hs, monsterMonomialDiagonalHolomorph_conjugation]

private theorem inverse_permutation_image (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex) (q : Q) :
    spinConjugation (monsterMonomialPermutationHolomorph P)⁻¹ q =
      monsterMonomialPermutationImage P.symm q := by
  have he : (monsterMonomialPermutationHolomorph P)⁻¹ =
      monsterMonomialPermutationHolomorph P.symm := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro f
    funext t
    rfl
  rw [he, monsterMonomialPermutationHolomorph_conjugation]

/-- The full inverse source permutation formula is the actual inverse spin conjugation. -/
theorem generatedTenth_Q_inverse_monomial_image (k : Fin 2) (q : Q) :
    spinConjugation (monsterSourcePermutationSpin k)⁻¹ q =
      generatedTenthQInverseMonomialImage k q := by
  rw [monsterSourcePermutationSpin, mul_inv_rev, map_mul]
  change spinConjugation (monsterMonomialDiagonalHolomorph
    (monsterSourcePermutationPhaseData k))⁻¹
      (spinConjugation (monsterMonomialPermutationHolomorph
        (monsterSourcePermutationCode k))⁻¹ q) = _
  rw [inverse_diagonal_image, inverse_permutation_image]
  rfl

/-- The literal forward or inverse source letter on the full original extraspecial group. -/
def generatedTenthQMonomialLetterImage (l : Fin 2 × Bool) (q : Q) : Q :=
  if l.2 then generatedTenthQInverseMonomialImage l.1 q else monsterSourcePermutationImage l.1 q

/-- Every signed monomial letter has exactly its stated full original Q image. -/
theorem generatedTenth_Q_monomial_letter_image (l : Fin 2 × Bool) (q : Q) :
    spinConjugation (generatedFourthMonomialFiberLetter l).val.1 q =
      generatedTenthQMonomialLetterImage l q := by
  rcases l with ⟨k, inv⟩
  cases inv
  · exact monsterSourcePermutationSpin_conjugation k q
  · exact generatedTenth_Q_inverse_monomial_image k q

/-- An entire source monomial word evaluated in its genuine right-to-left atom order. -/
def generatedTenthQMonomialWordImage (l : List (Fin 2 × Bool)) (q : Q) : Q :=
  l.foldr generatedTenthQMonomialLetterImage q

/-- No central coefficient is dropped in the complete original monomial word evaluator. -/
theorem generatedTenth_Q_monomial_word_image (l : List (Fin 2 × Bool)) (q : Q) :
    spinConjugation (l.map generatedFourthMonomialFiberLetter).prod.val.1 q =
      generatedTenthQMonomialWordImage l q := by
  induction l generalizing q with
  | nil =>
    simp only [List.map_nil, List.prod_nil, generatedTenthQMonomialWordImage,
      List.foldr_nil]
    change spinConjugation (1 : SpinHolomorph) q = q
    rw [map_one, MulAut.one_apply]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons]
    change spinConjugation ((generatedFourthMonomialFiberLetter a).val.1 *
      (l.map generatedFourthMonomialFiberLetter).prod.val.1) q = _
    rw [map_mul, MulAut.mul_apply, generatedTenth_Q_monomial_letter_image, ih]
    rfl

/-- The full original sign, permutation and Xi Q evaluator at one genuine source stage. -/
def generatedTenthQStageImage (k : Fin 14) (j : Fin 7) (q : Q) : Q :=
  let r := generatedAxisGlobalSignFullImage (generatedAxisGlobalFifthShortNormalizationSigns k j)
    (generatedTenthQMonomialWordImage (generatedAxisGlobalFifthShortNormalizationWords k j) q)
  if generatedAxisGlobalFifthShortNormalizationXi k j then xiSpinGImage (xiSpinGammaImage r)
    else r

/-- Each entire original source stage acts on Q by exactly the displayed finite evaluator. -/
theorem generatedTenth_Q_stage_image (k : Fin 14) (j : Fin 7) (q : Q) :
    spinConjugation (generatedTenthQStageFiber k j).val.1 q =
      generatedTenthQStageImage k j q := by
  cases hx : generatedAxisGlobalFifthShortNormalizationXi k j
  · rw [generatedTenthQStageFiber, hx]
    change spinConjugation ((1 : SpinHolomorph) *
      ((generatedFifthSignFiber (generatedAxisGlobalFifthShortNormalizationSigns k j) 0).val.1 *
      ((generatedAxisGlobalFifthShortNormalizationWords k j).map
        generatedFourthMonomialFiberLetter).prod.val.1)) q = _
    rw [one_mul, map_mul, MulAut.mul_apply, generatedAxisGlobalSignFull_QImage,
      generatedTenth_Q_monomial_word_image]
    simp only [generatedTenthQStageImage, hx, Bool.false_eq_true, ite_false]
  · rw [generatedTenthQStageFiber, hx]
    change spinConjugation (xiSpinHolomorph *
      ((generatedFifthSignFiber (generatedAxisGlobalFifthShortNormalizationSigns k j) 0).val.1 *
      ((generatedAxisGlobalFifthShortNormalizationWords k j).map
        generatedFourthMonomialFiberLetter).prod.val.1)) q = _
    rw [map_mul, MulAut.mul_apply, map_mul, MulAut.mul_apply,
      generatedAxisGlobalSignFull_QImage, generatedTenth_Q_monomial_word_image,
      xiSpinHolomorph_conjugation]
    simp only [generatedTenthQStageImage, hx, ite_true]

/-- The entire seven-stage original Q image in chronological source order. -/
def generatedTenthQWordImage (k : Fin 14) : ℕ → Q → Q
  | 0, q => q
  | n + 1, q => generatedTenthQStageImage k
      ⟨n % 7, Nat.mod_lt _ (by decide)⟩ (generatedTenthQWordImage k n q)

/-- The explicit full evaluator is the genuine complete original fiber conjugation. -/
theorem generatedTenth_Q_word_image (k : Fin 14) (q : Q) :
    spinConjugation (generatedTenthQWordFiber k).val.1 q =
      generatedTenthQWordImage k 7 q := by
  have h (n : ℕ) : spinConjugation
      (generatedAxisGlobalWordChain (fun j => generatedTenthQStageFiber k
        ⟨j % 7, Nat.mod_lt _ (by decide)⟩) n).val.1 q =
      generatedTenthQWordImage k n q := by
    induction n with
    | zero =>
      simp only [generatedAxisGlobalWordChain, generatedTenthQWordImage]
      change spinConjugation (1 : SpinHolomorph) q = q
      rw [map_one, MulAut.one_apply]
    | succ n ih =>
      rw [generatedAxisGlobalWordChain]
      change spinConjugation ((generatedTenthQStageFiber k
        ⟨n % 7, Nat.mod_lt _ (by decide)⟩).val.1 *
          (generatedAxisGlobalWordChain (fun j => generatedTenthQStageFiber k
            ⟨j % 7, Nat.mod_lt _ (by decide)⟩) n).val.1) q = _
      rw [map_mul, MulAut.mul_apply, generatedTenth_Q_stage_image, ih]
      rfl
  exact h 7

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
