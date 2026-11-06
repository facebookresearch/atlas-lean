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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 1) of the identification Twelfth[1]- <-> Twelfth[1]+ (record
gtwelfth:W1-, e = -1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 1 of the chunks of the target list. -/
def twGtwelfthW1nGTg1 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW1nGT8Labs twGtwelfthW1nGT8Nums 2048 ++
    (decodeTerms twGtwelfthW1nGT9Labs twGtwelfthW1nGT9Nums 2048 ++
    (decodeTerms twGtwelfthW1nGT10Labs twGtwelfthW1nGT10Nums 2048 ++
    (decodeTerms twGtwelfthW1nGT11Labs twGtwelfthW1nGT11Nums 2048 ++
    (decodeTerms twGtwelfthW1nGT12Labs twGtwelfthW1nGT12Nums 2048 ++
    (decodeTerms twGtwelfthW1nGT13Labs twGtwelfthW1nGT13Nums 2048 ++
    (decodeTerms twGtwelfthW1nGT14Labs twGtwelfthW1nGT14Nums 2048 ++
    (decodeTerms twGtwelfthW1nGT15Labs twGtwelfthW1nGT15Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 1 of the target terms. -/
theorem twGtwelfthW1n_og1 : oddSumF 64 false twGtwelfthW1nHX twGtwelfthW1nGTg1 = 23814144 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
