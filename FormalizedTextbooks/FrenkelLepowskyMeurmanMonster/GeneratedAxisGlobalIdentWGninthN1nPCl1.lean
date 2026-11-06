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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddSplitL

/-! # Factory tensor part (odd source terms, group 1) of the identification Ninth[1]- <->
Tenth[33]+ (record gninth:N1-, e = -1)

Dense source or long words: the tensor part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 1 of the chunks of the source list. -/
def wGninthN1nHTg1 : List (ℕ × ℤ) :=
  decodeTerms wGninthN1nHT8Labs wGninthN1nHT8Nums 2048 ++
    (decodeTerms wGninthN1nHT9Labs wGninthN1nHT9Nums 2048 ++
    (decodeTerms wGninthN1nHT10Labs wGninthN1nHT10Nums 2048 ++
    (decodeTerms wGninthN1nHT11Labs wGninthN1nHT11Nums 2048 ++
    (decodeTerms wGninthN1nHT12Labs wGninthN1nHT12Nums 2048 ++
    (decodeTerms wGninthN1nHT13Labs wGninthN1nHT13Nums 2048 ++
    (decodeTerms wGninthN1nHT14Labs wGninthN1nHT14Nums 2048 ++
    (decodeTerms wGninthN1nHT15Labs wGninthN1nHT15Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the tensor pairing over group 1 of the source terms. -/
theorem wGninthN1n_ol1 : oddSumL 64 false wGninthN1nGX wGninthN1nHTg1 = 44466176 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
