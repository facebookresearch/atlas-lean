/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 0) of the identification Twelfth[13]- <-> Twelfth[13]+ (record
gtwelfth:W13+, e = 1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 0 of the chunks of the target list. -/
def twGtwelfthW13pGTg0 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW13pGT0Labs twGtwelfthW13pGT0Nums 2048 ++
    (decodeTerms twGtwelfthW13pGT1Labs twGtwelfthW13pGT1Nums 2048 ++
    (decodeTerms twGtwelfthW13pGT2Labs twGtwelfthW13pGT2Nums 2048 ++
    (decodeTerms twGtwelfthW13pGT3Labs twGtwelfthW13pGT3Nums 2048 ++
    (decodeTerms twGtwelfthW13pGT4Labs twGtwelfthW13pGT4Nums 2048 ++
    (decodeTerms twGtwelfthW13pGT5Labs twGtwelfthW13pGT5Nums 2048 ++
    (decodeTerms twGtwelfthW13pGT6Labs twGtwelfthW13pGT6Nums 2048 ++
    (decodeTerms twGtwelfthW13pGT7Labs twGtwelfthW13pGT7Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 0 of the target terms. -/
theorem twGtwelfthW13p_og0 : oddSumF 80 true twGtwelfthW13pHX twGtwelfthW13pGTg0 = 372637696 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
