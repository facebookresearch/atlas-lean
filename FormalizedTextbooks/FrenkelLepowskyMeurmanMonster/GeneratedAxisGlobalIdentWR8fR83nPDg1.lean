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

/-! # Factory odd part (group 1) of the identification Root8[11]- <-> Twelfth[29]- (record
r8f:R83-, e = -1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 1 of the chunks of the target list. -/
def wR8fR83nGTg1 : List (ℕ × ℤ) :=
  decodeTerms wR8fR83nGT8Labs wR8fR83nGT8Nums 2048 ++
    (decodeTerms wR8fR83nGT9Labs wR8fR83nGT9Nums 2048 ++
    (decodeTerms wR8fR83nGT10Labs wR8fR83nGT10Nums 2048 ++
    (decodeTerms wR8fR83nGT11Labs wR8fR83nGT11Nums 2048 ++
    (decodeTerms wR8fR83nGT12Labs wR8fR83nGT12Nums 2048 ++
    (decodeTerms wR8fR83nGT13Labs wR8fR83nGT13Nums 2048 ++
    (decodeTerms wR8fR83nGT14Labs wR8fR83nGT14Nums 2048 ++
    (decodeTerms wR8fR83nGT15Labs wR8fR83nGT15Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 1 of the target terms. -/
theorem wR8fR83n_og1 : oddSumF 72 false wR8fR83nHX wR8fR83nGTg1 = 25608192 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
