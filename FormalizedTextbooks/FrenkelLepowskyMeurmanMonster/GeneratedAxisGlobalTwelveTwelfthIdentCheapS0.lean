/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentCheapData
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentSource
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSourceW

/-! # The first source stage of the incoming Twelfth vector, in compact checkpoints

The kernel checks that the monomial letters of the first stage map the Fifth tensor to
`twelfthS0mLit` and that its Xi and code sign letters map the widened `twelfthS0mLit` to
`twelfthS0Lit` (packed comparisons at field widths `8` and `16`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- A stage splits into its Xi and code sign letters and its monomial letters. -/
theorem twelfthYStage_split (j : Fin 7) :
    twelfthYStage j = (twelfthYStage j).take 2 ++ (twelfthYStage j).drop 2 :=
  (List.take_append_drop 2 _).symm

/-- Denominators and growth factors of the stage parts. -/
theorem twelfthYStage_dens :
    tensorWordDenAll ((twelfthYStage 0).drop 2) = 1 ∧
      tensorWordGrowthAll ((twelfthYStage 0).drop 2) = 1 ∧
      tensorWordDenAll ((twelfthYStage 0).take 2) = 32 ∧
      tensorWordGrowthAll ((twelfthYStage 0).take 2) = 2048 ∧
      tensorWordDenAll ((twelfthYStage 1).drop 2) = 1 ∧
      tensorWordGrowthAll ((twelfthYStage 1).drop 2) = 1 ∧
      tensorWordDenAll ((twelfthYStage 1).take 2) = 32 ∧
      tensorWordGrowthAll ((twelfthYStage 1).take 2) = 2048 ∧
      tensorWordDenAll (twelfthYStage 2) = 2 ∧ tensorWordGrowthAll (twelfthYStage 2) = 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The monomial letters of the first stage map the Fifth tensor to `twelfthS0mLit`. -/
theorem twelfthS0m_check :
    twColCheck 8 2 1 (tensorWordAll 8 ((twelfthYStage 0).drop 2) (fifthSrcXW 8))
      twelfthS0mLit = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Xi and the code sign of the first stage map the widened `twelfthS0mLit` to `twelfthS0Lit`. -/
theorem twelfthS0_check :
    twColCheck 16 2 4 (tensorWordAll 16 ((twelfthYStage 0).take 2) (twWidenT 2 16 twelfthS0mLit))
      twelfthS0Lit = true := by
  decide +kernel

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
