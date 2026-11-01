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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 2) of the identification Twelfth[9]+ <-> Twelfth[21]- (record
gtwelfth:W9+, e = 1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 2 of the chunks of the target list. -/
def twGtwelfthW9pGTg2 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW9pGT16Labs twGtwelfthW9pGT16Nums 2048 ++
    (decodeTerms twGtwelfthW9pGT17Labs twGtwelfthW9pGT17Nums 2048 ++
    (decodeTerms twGtwelfthW9pGT18Labs twGtwelfthW9pGT18Nums 2048 ++
    (decodeTerms twGtwelfthW9pGT19Labs twGtwelfthW9pGT19Nums 2048 ++
    (decodeTerms twGtwelfthW9pGT20Labs twGtwelfthW9pGT20Nums 2048 ++
    (decodeTerms twGtwelfthW9pGT21Labs twGtwelfthW9pGT21Nums 2048 ++
    (decodeTerms twGtwelfthW9pGT22Labs twGtwelfthW9pGT22Nums 1704))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 2 of the target terms. -/
theorem twGtwelfthW9p_og2 : oddSumF 80 true twGtwelfthW9pHX twGtwelfthW9pGTg2 = 296353792 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
