/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddSplitL

/-! # Factory tensor part (odd source terms, group 0) of the identification Root8[12]+ <->
Twelfth[34]- (record r8f:R86+, e = 1)

Dense source or long words: the tensor part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 0 of the chunks of the source list. -/
def wR8fR86pHTg0 : List (ℕ × ℤ) :=
  decodeTerms wR8fR86pHT0Labs wR8fR86pHT0Nums 2048 ++
    (decodeTerms wR8fR86pHT1Labs wR8fR86pHT1Nums 2048 ++
    (decodeTerms wR8fR86pHT2Labs wR8fR86pHT2Nums 2048 ++
    (decodeTerms wR8fR86pHT3Labs wR8fR86pHT3Nums 2048 ++
    (decodeTerms wR8fR86pHT4Labs wR8fR86pHT4Nums 2048 ++
    (decodeTerms wR8fR86pHT5Labs wR8fR86pHT5Nums 2048 ++
    (decodeTerms wR8fR86pHT6Labs wR8fR86pHT6Nums 2048 ++
    (decodeTerms wR8fR86pHT7Labs wR8fR86pHT7Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the tensor pairing over group 0 of the source terms. -/
theorem wR8fR86p_ol0 : oddSumL 96 true wR8fR86pGX wR8fR86pHTg0 = 918552576 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
