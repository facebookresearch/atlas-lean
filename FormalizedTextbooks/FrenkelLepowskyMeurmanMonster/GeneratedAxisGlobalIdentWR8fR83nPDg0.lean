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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 0) of the identification Root8[11]- <-> Twelfth[29]- (record
r8f:R83-, e = -1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 0 of the chunks of the target list. -/
def wR8fR83nGTg0 : List (ℕ × ℤ) :=
  decodeTerms wR8fR83nGT0Labs wR8fR83nGT0Nums 2048 ++
    (decodeTerms wR8fR83nGT1Labs wR8fR83nGT1Nums 2048 ++
    (decodeTerms wR8fR83nGT2Labs wR8fR83nGT2Nums 2048 ++
    (decodeTerms wR8fR83nGT3Labs wR8fR83nGT3Nums 2048 ++
    (decodeTerms wR8fR83nGT4Labs wR8fR83nGT4Nums 2048 ++
    (decodeTerms wR8fR83nGT5Labs wR8fR83nGT5Nums 2048 ++
    (decodeTerms wR8fR83nGT6Labs wR8fR83nGT6Nums 2048 ++
    (decodeTerms wR8fR83nGT7Labs wR8fR83nGT7Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 0 of the target terms. -/
theorem wR8fR83n_og0 : oddSumF 72 false wR8fR83nHX wR8fR83nGTg0 = 20013056 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
