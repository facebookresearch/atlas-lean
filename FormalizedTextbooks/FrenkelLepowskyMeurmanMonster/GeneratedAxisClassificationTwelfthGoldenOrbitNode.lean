/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitMonomial

/-! Exact node certificates distinguish the original root from genuine descending source steps. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The exact code, descending rank, and original monomial equation at one finite address. -/
def generatedTwelfthGoldenOrbitNodeProperty (k : Fin 24192) : Prop :=
  generatedTwelfthGoldenMatrixEncode (generatedTwelfthGoldenMatrixState k) =
      generatedTwelfthGoldenMatrixCode k ∧
    (generatedTwelfthGoldenMatrixRank k = 0 ∨
      generatedTwelfthGoldenMatrixRank (generatedTwelfthGoldenMatrixParent k) <
        generatedTwelfthGoldenMatrixRank k) ∧
    (generatedTwelfthGoldenMatrixRank k ≠ 0 →
      if h : (generatedTwelfthGoldenMatrixLetter k).val < 17 then
      ∀ i j : Fin 8,
        generatedTwelfthGoldenMatrixState k i j =
          generatedTwelfthGoldenMonomialSign ⟨(generatedTwelfthGoldenMatrixLetter k).val, h⟩ i *
          generatedTwelfthGoldenMonomialSign ⟨(generatedTwelfthGoldenMatrixLetter k).val, h⟩ j *
          generatedTwelfthGoldenMatrixState (generatedTwelfthGoldenMatrixParent k)
            (generatedTwelfthGoldenMonomialCoordinate
              ⟨(generatedTwelfthGoldenMatrixLetter k).val, h⟩ i)
            (generatedTwelfthGoldenMonomialCoordinate
              ⟨(generatedTwelfthGoldenMatrixLetter k).val, h⟩ j)
    else True)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
