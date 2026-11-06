/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQFactors
public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthActiveQImage

/-! The fourteen root words as chronological lists of individual original local source factors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All original permutation letters, then the original sign, then the actual optional Xi. -/
def generatedAxisGlobalFifthStageQFactors (k : Fin 14) (j : Fin 7) :
    List GeneratedAxisGlobalQFactor :=
  ((generatedAxisGlobalFifthShortNormalizationWords k j).reverse.map
    GeneratedAxisGlobalQFactor.monomial) ++
    [GeneratedAxisGlobalQFactor.sign (generatedAxisGlobalFifthShortNormalizationSigns k j)] ++
      (if generatedAxisGlobalFifthShortNormalizationXi k j then
        [GeneratedAxisGlobalQFactor.xi] else [])

private theorem monomial_word (w : List (Fin 2 × Bool)) :
    generatedAxisGlobalQFactorWord (w.reverse.map GeneratedAxisGlobalQFactor.monomial) =
      (w.map generatedFourthMonomialFiberLetter).prod := by
  simp only [generatedAxisGlobalQFactorWord, List.map_map, List.map_reverse,
    List.reverse_reverse]
  rfl

private theorem singleton_word (l : GeneratedAxisGlobalQFactor) :
    generatedAxisGlobalQFactorWord [l] = generatedAxisGlobalQFactorFiber l := by
  simp only [generatedAxisGlobalQFactorWord, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]

/-- The chronological stage has exactly the original actual fiber, with all original phases. -/
theorem generatedAxisGlobalFifthStageQFactors_actual (k : Fin 14) (j : Fin 7) :
    generatedAxisGlobalQFactorWord (generatedAxisGlobalFifthStageQFactors k j) =
      generatedAxisGlobalFifthShortNormalizationFiber k j := by
  rw [generatedAxisGlobalFifthStageQFactors, generatedAxisGlobalQFactorWord_append,
    generatedAxisGlobalQFactorWord_append, monomial_word, singleton_word]
  cases hx : generatedAxisGlobalFifthShortNormalizationXi k j with
  | false =>
    simp only [hx, Bool.false_eq_true, ↓reduceIte, generatedAxisGlobalQFactorWord,
      List.map_nil, List.reverse_nil, List.prod_nil, generatedAxisGlobalQFactorFiber,
      generatedAxisGlobalFifthShortNormalizationFiber, one_mul]
  | true =>
    simp only [hx, ↓reduceIte, singleton_word, generatedAxisGlobalQFactorFiber,
      generatedAxisGlobalFifthShortNormalizationFiber]

/-- The literal chronological source list accumulated through the original stages. -/
def generatedAxisGlobalFifthChainQFactors (k : Fin 14) : ℕ → List GeneratedAxisGlobalQFactor
  | 0 => []
  | n + 1 => generatedAxisGlobalFifthChainQFactors k n ++
      generatedAxisGlobalFifthStageQFactors k ⟨n % 7, Nat.mod_lt _ (by decide)⟩

/-- The chronological source factor list equals the complete genuine accumulated fiber word. -/
theorem generatedAxisGlobalFifthChainQFactors_actual (k : Fin 14) (n : ℕ) :
    generatedAxisGlobalQFactorWord (generatedAxisGlobalFifthChainQFactors k n) =
      generatedAxisGlobalWordChain (fun j => generatedAxisGlobalFifthShortNormalizationFiber k
        ⟨j % 7, Nat.mod_lt _ (by decide)⟩) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [generatedAxisGlobalFifthChainQFactors, generatedAxisGlobalQFactorWord_append,
      generatedAxisGlobalFifthStageQFactors_actual, ih, generatedAxisGlobalWordChain]

/-- The active chronological run retains the entire genuine seven-stage source Q image. -/
theorem generatedAxisGlobalFifthQFactors_run (k : Fin 14) (q : Q) :
    generatedAxisGlobalFifthChainQImage k 7 q =
      generatedAxisGlobalQFactorRun
        (generatedAxisGlobalFifthChainQFactors k (generatedAxisGlobalFifthActiveStages k)) q := by
  rw [generatedAxisGlobalFifthChain_active, ← generatedAxisGlobalFifthChain_QImage,
    ← generatedAxisGlobalFifthChainQFactors_actual, generatedAxisGlobalQFactorRun_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
