/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW21pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 0) of the identification Twelfth[9]+ <-> Twelfth[21]+ (record
gtwelfth:W21+, e = 1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 0 of the chunks of the target list. -/
def twGtwelfthW21pGTg0 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW21pGT0Labs twGtwelfthW21pGT0Nums 2048 ++
    (decodeTerms twGtwelfthW21pGT1Labs twGtwelfthW21pGT1Nums 2048 ++
    (decodeTerms twGtwelfthW21pGT2Labs twGtwelfthW21pGT2Nums 2048 ++
    (decodeTerms twGtwelfthW21pGT3Labs twGtwelfthW21pGT3Nums 2048 ++
    (decodeTerms twGtwelfthW21pGT4Labs twGtwelfthW21pGT4Nums 2048 ++
    (decodeTerms twGtwelfthW21pGT5Labs twGtwelfthW21pGT5Nums 2048 ++
    (decodeTerms twGtwelfthW21pGT6Labs twGtwelfthW21pGT6Nums 2048 ++
    (decodeTerms twGtwelfthW21pGT7Labs twGtwelfthW21pGT7Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 0 of the target terms. -/
theorem twGtwelfthW21p_og0 : oddSumF 80 true twGtwelfthW21pHX twGtwelfthW21pGTg0 = 372113408 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
