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

/-! # Factory tensor part (odd source terms, group 1) of the identification Twelfth[9]+ <->
Twelfth[21]- (record gtwelfth:W9+, e = 1)

Dense source or long words: the tensor part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 1 of the chunks of the source list. -/
def twGtwelfthW9pHTg1 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW9pHT8Labs twGtwelfthW9pHT8Nums 2048 ++
    (decodeTerms twGtwelfthW9pHT9Labs twGtwelfthW9pHT9Nums 2048 ++
    (decodeTerms twGtwelfthW9pHT10Labs twGtwelfthW9pHT10Nums 2048 ++
    (decodeTerms twGtwelfthW9pHT11Labs twGtwelfthW9pHT11Nums 2048 ++
    (decodeTerms twGtwelfthW9pHT12Labs twGtwelfthW9pHT12Nums 2048 ++
    (decodeTerms twGtwelfthW9pHT13Labs twGtwelfthW9pHT13Nums 2048 ++
    (decodeTerms twGtwelfthW9pHT14Labs twGtwelfthW9pHT14Nums 2048 ++
    (decodeTerms twGtwelfthW9pHT15Labs twGtwelfthW9pHT15Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the tensor pairing over group 1 of the source terms. -/
theorem twGtwelfthW9p_ol1 : oddSumL 80 true twGtwelfthW9pGX twGtwelfthW9pHTg1 = 760217600 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
