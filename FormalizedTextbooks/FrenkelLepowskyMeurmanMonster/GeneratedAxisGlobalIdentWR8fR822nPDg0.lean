/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR822nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 0) of the identification Root8[4]- <-> Root8[4]- (record r8f:R822-,
e = -1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 0 of the chunks of the target list. -/
def wR8fR822nGTg0 : List (ℕ × ℤ) :=
  decodeTerms wR8fR822nGT0Labs wR8fR822nGT0Nums 2048 ++
    (decodeTerms wR8fR822nGT1Labs wR8fR822nGT1Nums 2048 ++
    (decodeTerms wR8fR822nGT2Labs wR8fR822nGT2Nums 2048 ++
    (decodeTerms wR8fR822nGT3Labs wR8fR822nGT3Nums 2048 ++
    (decodeTerms wR8fR822nGT4Labs wR8fR822nGT4Nums 2048 ++
    (decodeTerms wR8fR822nGT5Labs wR8fR822nGT5Nums 2048 ++
    (decodeTerms wR8fR822nGT6Labs wR8fR822nGT6Nums 2048 ++
    (decodeTerms wR8fR822nGT7Labs wR8fR822nGT7Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 0 of the target terms. -/
theorem wR8fR822n_og0 : oddSumF 64 false wR8fR822nHX wR8fR822nGTg0 = 28868608 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
