/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW9pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 0) of the identification Twelfth[9]+ <-> Twelfth[21]- (record
gtwelfth:W9+, e = 1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 0 of the chunks of the target list. -/
def twGtwelfthW9pGTg0 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW9pGT0Labs twGtwelfthW9pGT0Nums 2048 ++
    (decodeTerms twGtwelfthW9pGT1Labs twGtwelfthW9pGT1Nums 2048 ++
    (decodeTerms twGtwelfthW9pGT2Labs twGtwelfthW9pGT2Nums 2048 ++
    (decodeTerms twGtwelfthW9pGT3Labs twGtwelfthW9pGT3Nums 2048 ++
    (decodeTerms twGtwelfthW9pGT4Labs twGtwelfthW9pGT4Nums 2048 ++
    (decodeTerms twGtwelfthW9pGT5Labs twGtwelfthW9pGT5Nums 2048 ++
    (decodeTerms twGtwelfthW9pGT6Labs twGtwelfthW9pGT6Nums 2048 ++
    (decodeTerms twGtwelfthW9pGT7Labs twGtwelfthW9pGT7Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 0 of the target terms. -/
theorem twGtwelfthW9p_og0 : oddSumF 80 true twGtwelfthW9pHX twGtwelfthW9pGTg0 = 368443392 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
