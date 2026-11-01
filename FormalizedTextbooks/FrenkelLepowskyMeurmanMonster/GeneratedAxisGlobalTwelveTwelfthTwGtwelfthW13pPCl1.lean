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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddSplitL

/-! # Factory tensor part (odd source terms, group 1) of the identification Twelfth[13]- <->
Twelfth[13]+ (record gtwelfth:W13+, e = 1)

Dense source or long words: the tensor part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 1 of the chunks of the source list. -/
def twGtwelfthW13pHTg1 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW13pHT8Labs twGtwelfthW13pHT8Nums 2048 ++
    (decodeTerms twGtwelfthW13pHT9Labs twGtwelfthW13pHT9Nums 2048 ++
    (decodeTerms twGtwelfthW13pHT10Labs twGtwelfthW13pHT10Nums 2048 ++
    (decodeTerms twGtwelfthW13pHT11Labs twGtwelfthW13pHT11Nums 2048 ++
    (decodeTerms twGtwelfthW13pHT12Labs twGtwelfthW13pHT12Nums 2048 ++
    (decodeTerms twGtwelfthW13pHT13Labs twGtwelfthW13pHT13Nums 2048 ++
    (decodeTerms twGtwelfthW13pHT14Labs twGtwelfthW13pHT14Nums 2048 ++
    (decodeTerms twGtwelfthW13pHT15Labs twGtwelfthW13pHT15Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the tensor pairing over group 1 of the source terms. -/
theorem twGtwelfthW13p_ol1 : oddSumL 80 true twGtwelfthW13pGX twGtwelfthW13pHTg1 = 759169024 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
