/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR817pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightCF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 1) of the identification Root8[26]+ <-> Root8[26]+ (record
r8f:R817+, e = 1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 1 of the chunks of the target list. -/
def wR8fR817pGTg1 : List (ℕ × ℤ) :=
  decodeTerms wR8fR817pGT8Labs wR8fR817pGT8Nums 2048 ++
    (decodeTerms wR8fR817pGT9Labs wR8fR817pGT9Nums 2048 ++
    (decodeTerms wR8fR817pGT10Labs wR8fR817pGT10Nums 2048 ++
    (decodeTerms wR8fR817pGT11Labs wR8fR817pGT11Nums 2048 ++
    (decodeTerms wR8fR817pGT12Labs wR8fR817pGT12Nums 2048 ++
    (decodeTerms wR8fR817pGT13Labs wR8fR817pGT13Nums 2048 ++
    (decodeTerms wR8fR817pGT14Labs wR8fR817pGT14Nums 2048 ++
    (decodeTerms wR8fR817pGT15Labs wR8fR817pGT15Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 1 of the target terms. -/
theorem wR8fR817p_og1 : oddSumF 64 true wR8fR817pHX wR8fR817pGTg1 = 33245184 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
