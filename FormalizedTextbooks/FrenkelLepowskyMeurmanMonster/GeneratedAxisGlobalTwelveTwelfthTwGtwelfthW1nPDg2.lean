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

/-! # Factory odd part (group 2) of the identification Twelfth[1]- <-> Twelfth[1]+ (record
gtwelfth:W1-, e = -1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 2 of the chunks of the target list. -/
def twGtwelfthW1nGTg2 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW1nGT16Labs twGtwelfthW1nGT16Nums 2048 ++
    (decodeTerms twGtwelfthW1nGT17Labs twGtwelfthW1nGT17Nums 2048 ++
    (decodeTerms twGtwelfthW1nGT18Labs twGtwelfthW1nGT18Nums 2048 ++
    (decodeTerms twGtwelfthW1nGT19Labs twGtwelfthW1nGT19Nums 2048 ++
    (decodeTerms twGtwelfthW1nGT20Labs twGtwelfthW1nGT20Nums 2048 ++
    (decodeTerms twGtwelfthW1nGT21Labs twGtwelfthW1nGT21Nums 2048 ++
    (decodeTerms twGtwelfthW1nGT22Labs twGtwelfthW1nGT22Nums 1704))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 2 of the target terms. -/
theorem twGtwelfthW1n_og2 : oddSumF 64 false twGtwelfthW1nHX twGtwelfthW1nGTg2 = 18522112 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
