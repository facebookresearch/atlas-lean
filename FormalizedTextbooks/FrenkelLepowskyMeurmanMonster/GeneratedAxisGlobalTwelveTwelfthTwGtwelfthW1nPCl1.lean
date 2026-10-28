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

/-! # Factory tensor part (odd source terms, group 1) of the identification Twelfth[1]- <->
Twelfth[1]+ (record gtwelfth:W1-, e = -1)

Dense source or long words: the tensor part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 1 of the chunks of the source list. -/
def twGtwelfthW1nHTg1 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW1nHT8Labs twGtwelfthW1nHT8Nums 2048 ++
    (decodeTerms twGtwelfthW1nHT9Labs twGtwelfthW1nHT9Nums 2048 ++
    (decodeTerms twGtwelfthW1nHT10Labs twGtwelfthW1nHT10Nums 2048 ++
    (decodeTerms twGtwelfthW1nHT11Labs twGtwelfthW1nHT11Nums 2048 ++
    (decodeTerms twGtwelfthW1nHT12Labs twGtwelfthW1nHT12Nums 2048 ++
    (decodeTerms twGtwelfthW1nHT13Labs twGtwelfthW1nHT13Nums 2048 ++
    (decodeTerms twGtwelfthW1nHT14Labs twGtwelfthW1nHT14Nums 2048 ++
    (decodeTerms twGtwelfthW1nHT15Labs twGtwelfthW1nHT15Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the tensor pairing over group 1 of the source terms. -/
theorem twGtwelfthW1n_ol1 : oddSumL 64 false twGtwelfthW1nGX twGtwelfthW1nHTg1 = 47628288 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
