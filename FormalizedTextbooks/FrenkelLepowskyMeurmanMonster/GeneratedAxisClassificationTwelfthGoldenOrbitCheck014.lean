/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitMonomial

/-! A bounded exact portion of the actual golden-matrix descending certificate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check exact increasing codes, descending ranks, and original signed coordinate equations.
/-- The exact block retains its code, rank descent and genuine monomial parent step. -/
theorem generatedTwelfthGoldenOrbitCheck014 : ∀ n : Fin 512,
    let k : Fin 24192 := ⟨7168 + n.val, by omega⟩
    generatedTwelfthGoldenMatrixEncode (generatedTwelfthGoldenMatrixState k) =
      generatedTwelfthGoldenMatrixCode k ∧
    (generatedTwelfthGoldenMatrixRank k = 0 ∨
      generatedTwelfthGoldenMatrixRank (generatedTwelfthGoldenMatrixParent k) <
        generatedTwelfthGoldenMatrixRank k) ∧
    (if h : (generatedTwelfthGoldenMatrixLetter k).val < 17 then
      ∀ i j : Fin 8,
        generatedTwelfthGoldenMatrixState k i j =
          generatedTwelfthGoldenMonomialSign ⟨(generatedTwelfthGoldenMatrixLetter k).val, h⟩ i *
          generatedTwelfthGoldenMonomialSign ⟨(generatedTwelfthGoldenMatrixLetter k).val, h⟩ j *
          generatedTwelfthGoldenMatrixState (generatedTwelfthGoldenMatrixParent k)
            (generatedTwelfthGoldenMonomialCoordinate
              ⟨(generatedTwelfthGoldenMatrixLetter k).val, h⟩ i)
            (generatedTwelfthGoldenMonomialCoordinate
              ⟨(generatedTwelfthGoldenMatrixLetter k).val, h⟩ j)
    else True) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
