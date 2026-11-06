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

/-! # Factory odd part (group 1) of the identification Twelfth[30]- <-> Twelfth[30]+ (record
gtwelfth:W30+, e = 1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 1 of the chunks of the target list. -/
def wGtwelfthW30pGTg1 : List (ℕ × ℤ) :=
  decodeTerms wGtwelfthW30pGT8Labs wGtwelfthW30pGT8Nums 2048 ++
    (decodeTerms wGtwelfthW30pGT9Labs wGtwelfthW30pGT9Nums 2048 ++
    (decodeTerms wGtwelfthW30pGT10Labs wGtwelfthW30pGT10Nums 2048 ++
    (decodeTerms wGtwelfthW30pGT11Labs wGtwelfthW30pGT11Nums 2048 ++
    (decodeTerms wGtwelfthW30pGT12Labs wGtwelfthW30pGT12Nums 2048 ++
    (decodeTerms wGtwelfthW30pGT13Labs wGtwelfthW30pGT13Nums 2048 ++
    (decodeTerms wGtwelfthW30pGT14Labs wGtwelfthW30pGT14Nums 2048 ++
    (decodeTerms wGtwelfthW30pGT15Labs wGtwelfthW30pGT15Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 1 of the target terms. -/
theorem wGtwelfthW30p_og1 : oddSumF 64 true wGtwelfthW30pHX wGtwelfthW30pGTg1 = 24289280 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
