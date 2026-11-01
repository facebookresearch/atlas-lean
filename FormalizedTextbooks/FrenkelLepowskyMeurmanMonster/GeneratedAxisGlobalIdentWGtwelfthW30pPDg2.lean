/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGtwelfthW30pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 2) of the identification Twelfth[30]- <-> Twelfth[30]+ (record
gtwelfth:W30+, e = 1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 2 of the chunks of the target list. -/
def wGtwelfthW30pGTg2 : List (ℕ × ℤ) :=
  decodeTerms wGtwelfthW30pGT16Labs wGtwelfthW30pGT16Nums 2048 ++
    (decodeTerms wGtwelfthW30pGT17Labs wGtwelfthW30pGT17Nums 2048 ++
    (decodeTerms wGtwelfthW30pGT18Labs wGtwelfthW30pGT18Nums 2048 ++
    (decodeTerms wGtwelfthW30pGT19Labs wGtwelfthW30pGT19Nums 2048 ++
    (decodeTerms wGtwelfthW30pGT20Labs wGtwelfthW30pGT20Nums 2048 ++
    (decodeTerms wGtwelfthW30pGT21Labs wGtwelfthW30pGT21Nums 2048 ++
    (decodeTerms wGtwelfthW30pGT22Labs wGtwelfthW30pGT22Nums 1704))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 2 of the target terms. -/
theorem wGtwelfthW30p_og2 : oddSumF 64 true wGtwelfthW30pHX wGtwelfthW30pGTg2 = 18522112 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
