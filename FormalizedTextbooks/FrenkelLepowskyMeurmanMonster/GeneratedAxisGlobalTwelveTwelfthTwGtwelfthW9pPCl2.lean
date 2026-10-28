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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddSplitL

/-! # Factory tensor part (odd source terms, group 2) of the identification Twelfth[9]+ <->
Twelfth[21]- (record gtwelfth:W9+, e = 1)

Dense source or long words: the tensor part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 2 of the chunks of the source list. -/
def twGtwelfthW9pHTg2 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW9pHT16Labs twGtwelfthW9pHT16Nums 2048 ++
    (decodeTerms twGtwelfthW9pHT17Labs twGtwelfthW9pHT17Nums 2048 ++
    (decodeTerms twGtwelfthW9pHT18Labs twGtwelfthW9pHT18Nums 2048 ++
    (decodeTerms twGtwelfthW9pHT19Labs twGtwelfthW9pHT19Nums 2048 ++
    (decodeTerms twGtwelfthW9pHT20Labs twGtwelfthW9pHT20Nums 2048 ++
    (decodeTerms twGtwelfthW9pHT21Labs twGtwelfthW9pHT21Nums 2048 ++
    (decodeTerms twGtwelfthW9pHT22Labs twGtwelfthW9pHT22Nums 1704))))))

set_option maxRecDepth 100000 in
/-- The odd part of the tensor pairing over group 2 of the source terms. -/
theorem twGtwelfthW9p_ol2 : oddSumL 80 true twGtwelfthW9pGX twGtwelfthW9pHTg2 = 592707584 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
