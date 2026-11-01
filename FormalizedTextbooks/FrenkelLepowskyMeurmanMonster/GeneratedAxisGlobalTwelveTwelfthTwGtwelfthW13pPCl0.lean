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

/-! # Factory tensor part (odd source terms, group 0) of the identification Twelfth[13]- <->
Twelfth[13]+ (record gtwelfth:W13+, e = 1)

Dense source or long words: the tensor part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 0 of the chunks of the source list. -/
def twGtwelfthW13pHTg0 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW13pHT0Labs twGtwelfthW13pHT0Nums 2048 ++
    (decodeTerms twGtwelfthW13pHT1Labs twGtwelfthW13pHT1Nums 2048 ++
    (decodeTerms twGtwelfthW13pHT2Labs twGtwelfthW13pHT2Nums 2048 ++
    (decodeTerms twGtwelfthW13pHT3Labs twGtwelfthW13pHT3Nums 2048 ++
    (decodeTerms twGtwelfthW13pHT4Labs twGtwelfthW13pHT4Nums 2048 ++
    (decodeTerms twGtwelfthW13pHT5Labs twGtwelfthW13pHT5Nums 2048 ++
    (decodeTerms twGtwelfthW13pHT6Labs twGtwelfthW13pHT6Nums 2048 ++
    (decodeTerms twGtwelfthW13pHT7Labs twGtwelfthW13pHT7Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the tensor pairing over group 0 of the source terms. -/
theorem twGtwelfthW13p_ol0 : oddSumL 80 true twGtwelfthW13pGX twGtwelfthW13pHTg0 = 745275392 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
