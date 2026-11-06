/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW36pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 0) of the identification Twelfth[36]+ <-> Twelfth[36]+ (record
gtwelfth:W36+, e = 1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 0 of the chunks of the target list. -/
def twGtwelfthW36pGTg0 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW36pGT0Labs twGtwelfthW36pGT0Nums 2048 ++
    (decodeTerms twGtwelfthW36pGT1Labs twGtwelfthW36pGT1Nums 2048 ++
    (decodeTerms twGtwelfthW36pGT2Labs twGtwelfthW36pGT2Nums 2048 ++
    (decodeTerms twGtwelfthW36pGT3Labs twGtwelfthW36pGT3Nums 2048 ++
    (decodeTerms twGtwelfthW36pGT4Labs twGtwelfthW36pGT4Nums 2048 ++
    (decodeTerms twGtwelfthW36pGT5Labs twGtwelfthW36pGT5Nums 2048 ++
    (decodeTerms twGtwelfthW36pGT6Labs twGtwelfthW36pGT6Nums 2048 ++
    (decodeTerms twGtwelfthW36pGT7Labs twGtwelfthW36pGT7Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 0 of the target terms. -/
theorem twGtwelfthW36p_og0 : oddSumF 64 true twGtwelfthW36pHX twGtwelfthW36pGTg0 = 23904256 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
