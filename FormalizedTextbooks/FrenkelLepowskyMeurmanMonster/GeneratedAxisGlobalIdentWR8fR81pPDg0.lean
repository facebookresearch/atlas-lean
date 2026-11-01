/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR81pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 0) of the identification Root8[16]+ <-> Twelfth[24]+ (record
r8f:R81+, e = 1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 0 of the chunks of the target list. -/
def wR8fR81pGTg0 : List (ℕ × ℤ) :=
  decodeTerms wR8fR81pGT0Labs wR8fR81pGT0Nums 2048 ++
    (decodeTerms wR8fR81pGT1Labs wR8fR81pGT1Nums 2048 ++
    (decodeTerms wR8fR81pGT2Labs wR8fR81pGT2Nums 2048 ++
    (decodeTerms wR8fR81pGT3Labs wR8fR81pGT3Nums 2048 ++
    (decodeTerms wR8fR81pGT4Labs wR8fR81pGT4Nums 2048 ++
    (decodeTerms wR8fR81pGT5Labs wR8fR81pGT5Nums 2048 ++
    (decodeTerms wR8fR81pGT6Labs wR8fR81pGT6Nums 2048 ++
    (decodeTerms wR8fR81pGT7Labs wR8fR81pGT7Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 0 of the target terms. -/
theorem wR8fR81p_og0 : oddSumF 112 true wR8fR81pHX wR8fR81pGTg0 = 374341632 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
