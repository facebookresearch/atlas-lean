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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddSplitL

/-! # Factory tensor part (odd source terms, group 2) of the identification Twelfth[9]+ <->
Twelfth[21]+ (record gtwelfth:W21+, e = 1)

Dense source or long words: the tensor part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 2 of the chunks of the source list. -/
def twGtwelfthW21pHTg2 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW21pHT16Labs twGtwelfthW21pHT16Nums 2048 ++
    (decodeTerms twGtwelfthW21pHT17Labs twGtwelfthW21pHT17Nums 2048 ++
    (decodeTerms twGtwelfthW21pHT18Labs twGtwelfthW21pHT18Nums 2048 ++
    (decodeTerms twGtwelfthW21pHT19Labs twGtwelfthW21pHT19Nums 2048 ++
    (decodeTerms twGtwelfthW21pHT20Labs twGtwelfthW21pHT20Nums 2048 ++
    (decodeTerms twGtwelfthW21pHT21Labs twGtwelfthW21pHT21Nums 2048 ++
    (decodeTerms twGtwelfthW21pHT22Labs twGtwelfthW21pHT22Nums 1704))))))

set_option maxRecDepth 100000 in
/-- The odd part of the tensor pairing over group 2 of the source terms. -/
theorem twGtwelfthW21p_ol2 : oddSumL 80 true twGtwelfthW21pGX twGtwelfthW21pHTg2 = 592707584 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
