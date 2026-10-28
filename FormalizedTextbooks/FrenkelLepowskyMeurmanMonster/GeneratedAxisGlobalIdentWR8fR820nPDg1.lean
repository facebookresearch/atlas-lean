/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightCF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 1) of the identification Root8[25]- <-> Root8[25]- (record
r8f:R820-, e = -1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 1 of the chunks of the target list. -/
def wR8fR820nGTg1 : List (ℕ × ℤ) :=
  decodeTerms wR8fR820nGT8Labs wR8fR820nGT8Nums 2048 ++
    (decodeTerms wR8fR820nGT9Labs wR8fR820nGT9Nums 2048 ++
    (decodeTerms wR8fR820nGT10Labs wR8fR820nGT10Nums 2048 ++
    (decodeTerms wR8fR820nGT11Labs wR8fR820nGT11Nums 2048 ++
    (decodeTerms wR8fR820nGT12Labs wR8fR820nGT12Nums 2048 ++
    (decodeTerms wR8fR820nGT13Labs wR8fR820nGT13Nums 2048 ++
    (decodeTerms wR8fR820nGT14Labs wR8fR820nGT14Nums 2048 ++
    (decodeTerms wR8fR820nGT15Labs wR8fR820nGT15Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 1 of the target terms. -/
theorem wR8fR820n_og1 : oddSumF 64 false wR8fR820nHX wR8fR820nGTg1 = 1966080 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
