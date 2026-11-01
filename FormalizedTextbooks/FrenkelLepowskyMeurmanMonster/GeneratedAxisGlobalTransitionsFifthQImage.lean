/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMonomialQImage
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignFullImage
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortFiber

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQChain

/-! Complete actual preferred-Q evaluators for every stage and fourteen genuine fifth root words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The full signed source stage followed by its actual optional Xi Q action. -/
def generatedAxisGlobalFifthStageQImage (k : Fin 14) (j : Fin 7) (q : Q) : Q :=
  let r := generatedAxisGlobalSignFullImage (generatedAxisGlobalFifthShortNormalizationSigns k j)
    (generatedAxisGlobalMonomialWordQImage (generatedAxisGlobalFifthShortNormalizationWords k j) q)
  if generatedAxisGlobalFifthShortNormalizationXi k j then xiSpinGImage (xiSpinGammaImage r)
  else r

/-- Every original normalization stage has exactly the displayed full actual Q conjugation. -/
theorem generatedAxisGlobalFifthStage_QImage (k : Fin 14) (j : Fin 7) (q : Q) :
    spinConjugation (generatedAxisGlobalFifthShortNormalizationFiber k j).val.1 q =
      generatedAxisGlobalFifthStageQImage k j q := by
  cases hx : generatedAxisGlobalFifthShortNormalizationXi k j with
  | false =>
    simp only [generatedAxisGlobalFifthShortNormalizationFiber, hx, Bool.false_eq_true,
      ↓reduceIte, one_mul, generatedAxisGlobalFifthStageQImage]
    change spinConjugation
      ((generatedFifthSignFiber (generatedAxisGlobalFifthShortNormalizationSigns k j) 0).val.1 *
        (((generatedAxisGlobalFifthShortNormalizationWords k j).map
          generatedFourthMonomialFiberLetter).prod).val.1) q = _
    rw [map_mul]
    change spinConjugation
      (generatedFifthSignFiber (generatedAxisGlobalFifthShortNormalizationSigns k j) 0).val.1
      (spinConjugation (((generatedAxisGlobalFifthShortNormalizationWords k j).map
        generatedFourthMonomialFiberLetter).prod).val.1 q) = _
    rw [generatedAxisGlobalMonomialWord_QImage, generatedAxisGlobalSignFull_QImage]
  | true =>
    simp only [generatedAxisGlobalFifthShortNormalizationFiber, hx, ↓reduceIte,
      generatedAxisGlobalFifthStageQImage]
    change spinConjugation
      (xiSpinHolomorph *
        ((generatedFifthSignFiber (generatedAxisGlobalFifthShortNormalizationSigns k j) 0).val.1 *
          (((generatedAxisGlobalFifthShortNormalizationWords k j).map
            generatedFourthMonomialFiberLetter).prod).val.1)) q = _
    rw [map_mul, map_mul]
    change spinConjugation xiSpinHolomorph
      (spinConjugation
        (generatedFifthSignFiber (generatedAxisGlobalFifthShortNormalizationSigns k j) 0).val.1
        (spinConjugation (((generatedAxisGlobalFifthShortNormalizationWords k j).map
          generatedFourthMonomialFiberLetter).prod).val.1 q)) = _
    rw [generatedAxisGlobalMonomialWord_QImage, generatedAxisGlobalSignFull_QImage,
      xiSpinHolomorph_conjugation]

/-- The finite chronological Q image follows the exact seven-stage actual source word. -/
def generatedAxisGlobalFifthChainQImage (k : Fin 14) (n : ℕ) (q : Q) : Q :=
  generatedAxisGlobalQImageChain
    (fun j => generatedAxisGlobalFifthStageQImage k ⟨j % 7, Nat.mod_lt _ (by decide)⟩) n q

/-- Every finite chain agrees with the genuine accumulated local fiber conjugation. -/
theorem generatedAxisGlobalFifthChain_QImage (k : Fin 14) (n : ℕ) (q : Q) :
    spinConjugation
      (generatedAxisGlobalWordChain (fun j => generatedAxisGlobalFifthShortNormalizationFiber k
        ⟨j % 7, Nat.mod_lt _ (by decide)⟩) n).val.1 q =
      generatedAxisGlobalFifthChainQImage k n q :=
  generatedAxisGlobalQImageChain_actual _ _
    (fun _j q => generatedAxisGlobalFifthStage_QImage k _ q) n q

/-- The explicit full evaluator is genuine conjugation by each of the fourteen root words. -/
theorem generatedAxisGlobalFifthShortWord_QImage (k : Fin 14) (q : Q) :
    spinConjugation (generatedAxisGlobalFifthShortWordFiber k).val.1 q =
      generatedAxisGlobalFifthChainQImage k 7 q :=
  generatedAxisGlobalFifthChain_QImage k 7 q

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
