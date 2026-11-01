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

/-! # Factory tensor part (odd source terms, group 0) of the identification Twelfth[9]+ <->
Twelfth[21]- (record gtwelfth:W9+, e = 1)

Dense source or long words: the tensor part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 0 of the chunks of the source list. -/
def twGtwelfthW9pHTg0 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW9pHT0Labs twGtwelfthW9pHT0Nums 2048 ++
    (decodeTerms twGtwelfthW9pHT1Labs twGtwelfthW9pHT1Nums 2048 ++
    (decodeTerms twGtwelfthW9pHT2Labs twGtwelfthW9pHT2Nums 2048 ++
    (decodeTerms twGtwelfthW9pHT3Labs twGtwelfthW9pHT3Nums 2048 ++
    (decodeTerms twGtwelfthW9pHT4Labs twGtwelfthW9pHT4Nums 2048 ++
    (decodeTerms twGtwelfthW9pHT5Labs twGtwelfthW9pHT5Nums 2048 ++
    (decodeTerms twGtwelfthW9pHT6Labs twGtwelfthW9pHT6Nums 2048 ++
    (decodeTerms twGtwelfthW9pHT7Labs twGtwelfthW9pHT7Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the tensor pairing over group 0 of the source terms. -/
theorem twGtwelfthW9p_ol0 : oddSumL 80 true twGtwelfthW9pGX twGtwelfthW9pHTg0 = 744226816 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
