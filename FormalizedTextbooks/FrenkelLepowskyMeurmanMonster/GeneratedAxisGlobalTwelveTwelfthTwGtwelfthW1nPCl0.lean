/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddSplitL

/-! # Factory tensor part (odd source terms, group 0) of the identification Twelfth[1]- <->
Twelfth[1]+ (record gtwelfth:W1-, e = -1)

Dense source or long words: the tensor part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 0 of the chunks of the source list. -/
def twGtwelfthW1nHTg0 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW1nHT0Labs twGtwelfthW1nHT0Nums 2048 ++
    (decodeTerms twGtwelfthW1nHT1Labs twGtwelfthW1nHT1Nums 2048 ++
    (decodeTerms twGtwelfthW1nHT2Labs twGtwelfthW1nHT2Nums 2048 ++
    (decodeTerms twGtwelfthW1nHT3Labs twGtwelfthW1nHT3Nums 2048 ++
    (decodeTerms twGtwelfthW1nHT4Labs twGtwelfthW1nHT4Nums 2048 ++
    (decodeTerms twGtwelfthW1nHT5Labs twGtwelfthW1nHT5Nums 2048 ++
    (decodeTerms twGtwelfthW1nHT6Labs twGtwelfthW1nHT6Nums 2048 ++
    (decodeTerms twGtwelfthW1nHT7Labs twGtwelfthW1nHT7Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the tensor pairing over group 0 of the source terms. -/
theorem twGtwelfthW1n_ol0 : oddSumL 64 false twGtwelfthW1nGX twGtwelfthW1nHTg0 = 46399488 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
