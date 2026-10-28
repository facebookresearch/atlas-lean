/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 1) of the identification Ninth[1]- <-> Tenth[33]+ (record
gninth:N1-, e = -1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 1 of the chunks of the target list. -/
def wGninthN1nGTg1 : List (ℕ × ℤ) :=
  decodeTerms wGninthN1nGT8Labs wGninthN1nGT8Nums 2048 ++
    (decodeTerms wGninthN1nGT9Labs wGninthN1nGT9Nums 2048 ++
    (decodeTerms wGninthN1nGT10Labs wGninthN1nGT10Nums 2048 ++
    (decodeTerms wGninthN1nGT11Labs wGninthN1nGT11Nums 2048 ++
    (decodeTerms wGninthN1nGT12Labs wGninthN1nGT12Nums 2048 ++
    (decodeTerms wGninthN1nGT13Labs wGninthN1nGT13Nums 2048 ++
    (decodeTerms wGninthN1nGT14Labs wGninthN1nGT14Nums 2048 ++
    (decodeTerms wGninthN1nGT15Labs wGninthN1nGT15Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 1 of the target terms. -/
theorem wGninthN1n_og1 : oddSumF 64 false wGninthN1nHX wGninthN1nGTg1 = 1452416 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
