/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW36pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 1) of the identification Twelfth[36]+ <-> Twelfth[36]+ (record
gtwelfth:W36+, e = 1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 1 of the chunks of the target list. -/
def twGtwelfthW36pGTg1 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW36pGT8Labs twGtwelfthW36pGT8Nums 2048 ++
    (decodeTerms twGtwelfthW36pGT9Labs twGtwelfthW36pGT9Nums 2048 ++
    (decodeTerms twGtwelfthW36pGT10Labs twGtwelfthW36pGT10Nums 2048 ++
    (decodeTerms twGtwelfthW36pGT11Labs twGtwelfthW36pGT11Nums 2048 ++
    (decodeTerms twGtwelfthW36pGT12Labs twGtwelfthW36pGT12Nums 2048 ++
    (decodeTerms twGtwelfthW36pGT13Labs twGtwelfthW36pGT13Nums 2048 ++
    (decodeTerms twGtwelfthW36pGT14Labs twGtwelfthW36pGT14Nums 2048 ++
    (decodeTerms twGtwelfthW36pGT15Labs twGtwelfthW36pGT15Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 1 of the target terms. -/
theorem twGtwelfthW36p_og1 : oddSumF 64 true twGtwelfthW36pHX twGtwelfthW36pGTg1 = 24682496 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
