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

/-! # Factory tensor part (odd source terms, group 1) of the identification Twelfth[9]+ <->
Twelfth[21]+ (record gtwelfth:W21+, e = 1)

Dense source or long words: the tensor part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 1 of the chunks of the source list. -/
def twGtwelfthW21pHTg1 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW21pHT8Labs twGtwelfthW21pHT8Nums 2048 ++
    (decodeTerms twGtwelfthW21pHT9Labs twGtwelfthW21pHT9Nums 2048 ++
    (decodeTerms twGtwelfthW21pHT10Labs twGtwelfthW21pHT10Nums 2048 ++
    (decodeTerms twGtwelfthW21pHT11Labs twGtwelfthW21pHT11Nums 2048 ++
    (decodeTerms twGtwelfthW21pHT12Labs twGtwelfthW21pHT12Nums 2048 ++
    (decodeTerms twGtwelfthW21pHT13Labs twGtwelfthW21pHT13Nums 2048 ++
    (decodeTerms twGtwelfthW21pHT14Labs twGtwelfthW21pHT14Nums 2048 ++
    (decodeTerms twGtwelfthW21pHT15Labs twGtwelfthW21pHT15Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the tensor pairing over group 1 of the source terms. -/
theorem twGtwelfthW21p_ol1 : oddSumL 80 true twGtwelfthW21pGX twGtwelfthW21pHTg1 = 767557632 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
