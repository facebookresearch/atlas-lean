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

/-! # Factory tensor part (odd source terms, group 0) of the identification Twelfth[9]+ <->
Twelfth[21]+ (record gtwelfth:W21+, e = 1)

Dense source or long words: the tensor part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 0 of the chunks of the source list. -/
def twGtwelfthW21pHTg0 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW21pHT0Labs twGtwelfthW21pHT0Nums 2048 ++
    (decodeTerms twGtwelfthW21pHT1Labs twGtwelfthW21pHT1Nums 2048 ++
    (decodeTerms twGtwelfthW21pHT2Labs twGtwelfthW21pHT2Nums 2048 ++
    (decodeTerms twGtwelfthW21pHT3Labs twGtwelfthW21pHT3Nums 2048 ++
    (decodeTerms twGtwelfthW21pHT4Labs twGtwelfthW21pHT4Nums 2048 ++
    (decodeTerms twGtwelfthW21pHT5Labs twGtwelfthW21pHT5Nums 2048 ++
    (decodeTerms twGtwelfthW21pHT6Labs twGtwelfthW21pHT6Nums 2048 ++
    (decodeTerms twGtwelfthW21pHT7Labs twGtwelfthW21pHT7Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the tensor pairing over group 0 of the source terms. -/
theorem twGtwelfthW21p_ol0 : oddSumL 80 true twGtwelfthW21pGX twGtwelfthW21pHTg0 = 736886784 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
