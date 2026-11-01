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

/-! # Factory tensor part (odd source terms, group 2) of the identification Twelfth[13]- <->
Twelfth[13]+ (record gtwelfth:W13+, e = 1)

Dense source or long words: the tensor part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 2 of the chunks of the source list. -/
def twGtwelfthW13pHTg2 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW13pHT16Labs twGtwelfthW13pHT16Nums 2048 ++
    (decodeTerms twGtwelfthW13pHT17Labs twGtwelfthW13pHT17Nums 2048 ++
    (decodeTerms twGtwelfthW13pHT18Labs twGtwelfthW13pHT18Nums 2048 ++
    (decodeTerms twGtwelfthW13pHT19Labs twGtwelfthW13pHT19Nums 2048 ++
    (decodeTerms twGtwelfthW13pHT20Labs twGtwelfthW13pHT20Nums 2048 ++
    (decodeTerms twGtwelfthW13pHT21Labs twGtwelfthW13pHT21Nums 2048 ++
    (decodeTerms twGtwelfthW13pHT22Labs twGtwelfthW13pHT22Nums 1704))))))

set_option maxRecDepth 100000 in
/-- The odd part of the tensor pairing over group 2 of the source terms. -/
theorem twGtwelfthW13p_ol2 : oddSumL 80 true twGtwelfthW13pGX twGtwelfthW13pHTg2 = 592707584 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
