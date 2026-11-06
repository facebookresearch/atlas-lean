/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddSplitL

/-! # Factory tensor part (odd source terms, group 0) of the identification Root8[11]- <->
Twelfth[29]- (record r8f:R83-, e = -1)

Dense source or long words: the tensor part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 0 of the chunks of the source list. -/
def wR8fR83nHTg0 : List (ℕ × ℤ) :=
  decodeTerms wR8fR83nHT0Labs wR8fR83nHT0Nums 2048 ++
    (decodeTerms wR8fR83nHT1Labs wR8fR83nHT1Nums 2048 ++
    (decodeTerms wR8fR83nHT2Labs wR8fR83nHT2Nums 2048 ++
    (decodeTerms wR8fR83nHT3Labs wR8fR83nHT3Nums 2048 ++
    (decodeTerms wR8fR83nHT4Labs wR8fR83nHT4Nums 2048 ++
    (decodeTerms wR8fR83nHT5Labs wR8fR83nHT5Nums 2048 ++
    (decodeTerms wR8fR83nHT6Labs wR8fR83nHT6Nums 2048 ++
    (decodeTerms wR8fR83nHT7Labs wR8fR83nHT7Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the tensor pairing over group 0 of the source terms. -/
theorem wR8fR83n_ol0 : oddSumL 72 false wR8fR83nGX wR8fR83nHTg0 = 122945536 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
