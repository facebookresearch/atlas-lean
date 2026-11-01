/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 1) of the identification Root8[12]- <-> Twelfth[34]- (record
r8f:R86-, e = -1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 1 of the chunks of the target list. -/
def wR8fR86nGTg1 : List (ℕ × ℤ) :=
  decodeTerms wR8fR86nGT8Labs wR8fR86nGT8Nums 2048 ++
    (decodeTerms wR8fR86nGT9Labs wR8fR86nGT9Nums 2048 ++
    (decodeTerms wR8fR86nGT10Labs wR8fR86nGT10Nums 2048 ++
    (decodeTerms wR8fR86nGT11Labs wR8fR86nGT11Nums 2048 ++
    (decodeTerms wR8fR86nGT12Labs wR8fR86nGT12Nums 2048 ++
    (decodeTerms wR8fR86nGT13Labs wR8fR86nGT13Nums 2048 ++
    (decodeTerms wR8fR86nGT14Labs wR8fR86nGT14Nums 2048 ++
    (decodeTerms wR8fR86nGT15Labs wR8fR86nGT15Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 1 of the target terms. -/
theorem wR8fR86n_og1 : oddSumF 96 false wR8fR86nHX wR8fR86nGTg1 = 6129975296 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
