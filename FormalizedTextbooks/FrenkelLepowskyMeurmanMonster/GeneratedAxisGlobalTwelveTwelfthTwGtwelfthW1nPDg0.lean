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

/-! # Factory odd part (group 0) of the identification Twelfth[1]- <-> Twelfth[1]+ (record
gtwelfth:W1-, e = -1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 0 of the chunks of the target list. -/
def twGtwelfthW1nGTg0 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW1nGT0Labs twGtwelfthW1nGT0Nums 2048 ++
    (decodeTerms twGtwelfthW1nGT1Labs twGtwelfthW1nGT1Nums 2048 ++
    (decodeTerms twGtwelfthW1nGT2Labs twGtwelfthW1nGT2Nums 2048 ++
    (decodeTerms twGtwelfthW1nGT3Labs twGtwelfthW1nGT3Nums 2048 ++
    (decodeTerms twGtwelfthW1nGT4Labs twGtwelfthW1nGT4Nums 2048 ++
    (decodeTerms twGtwelfthW1nGT5Labs twGtwelfthW1nGT5Nums 2048 ++
    (decodeTerms twGtwelfthW1nGT6Labs twGtwelfthW1nGT6Nums 2048 ++
    (decodeTerms twGtwelfthW1nGT7Labs twGtwelfthW1nGT7Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 0 of the target terms. -/
theorem twGtwelfthW1n_og0 : oddSumF 64 false twGtwelfthW1nHX twGtwelfthW1nGTg0 = 23199744 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
