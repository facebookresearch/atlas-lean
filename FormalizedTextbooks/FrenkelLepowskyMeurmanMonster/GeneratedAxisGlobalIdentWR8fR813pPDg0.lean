/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR813pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightCF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 0) of the identification Root8[7]+ <-> Root8[7]+ (record r8f:R813+,
e = 1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 0 of the chunks of the target list. -/
def wR8fR813pGTg0 : List (ℕ × ℤ) :=
  decodeTerms wR8fR813pGT0Labs wR8fR813pGT0Nums 2048 ++
    (decodeTerms wR8fR813pGT1Labs wR8fR813pGT1Nums 2048 ++
    (decodeTerms wR8fR813pGT2Labs wR8fR813pGT2Nums 2048 ++
    (decodeTerms wR8fR813pGT3Labs wR8fR813pGT3Nums 2048 ++
    (decodeTerms wR8fR813pGT4Labs wR8fR813pGT4Nums 2048 ++
    (decodeTerms wR8fR813pGT5Labs wR8fR813pGT5Nums 2048 ++
    (decodeTerms wR8fR813pGT6Labs wR8fR813pGT6Nums 2048 ++
    (decodeTerms wR8fR813pGT7Labs wR8fR813pGT7Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 0 of the target terms. -/
theorem wR8fR813p_og0 : oddSumF 64 true wR8fR813pHX wR8fR813pGTg0 = 471859200 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
