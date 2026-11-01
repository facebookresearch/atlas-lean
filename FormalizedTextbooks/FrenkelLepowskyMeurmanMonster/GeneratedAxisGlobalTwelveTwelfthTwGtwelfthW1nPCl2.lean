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

/-! # Factory tensor part (odd source terms, group 2) of the identification Twelfth[1]- <->
Twelfth[1]+ (record gtwelfth:W1-, e = -1)

Dense source or long words: the tensor part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 2 of the chunks of the source list. -/
def twGtwelfthW1nHTg2 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW1nHT16Labs twGtwelfthW1nHT16Nums 2048 ++
    (decodeTerms twGtwelfthW1nHT17Labs twGtwelfthW1nHT17Nums 2048 ++
    (decodeTerms twGtwelfthW1nHT18Labs twGtwelfthW1nHT18Nums 2048 ++
    (decodeTerms twGtwelfthW1nHT19Labs twGtwelfthW1nHT19Nums 2048 ++
    (decodeTerms twGtwelfthW1nHT20Labs twGtwelfthW1nHT20Nums 2048 ++
    (decodeTerms twGtwelfthW1nHT21Labs twGtwelfthW1nHT21Nums 2048 ++
    (decodeTerms twGtwelfthW1nHT22Labs twGtwelfthW1nHT22Nums 1704))))))

set_option maxRecDepth 100000 in
/-- The odd part of the tensor pairing over group 2 of the source terms. -/
theorem twGtwelfthW1n_ol2 : oddSumL 64 false twGtwelfthW1nGX twGtwelfthW1nHTg2 = 37044224 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
