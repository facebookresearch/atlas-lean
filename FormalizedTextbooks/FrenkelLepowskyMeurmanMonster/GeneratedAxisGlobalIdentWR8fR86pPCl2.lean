/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddSplitL

/-! # Factory tensor part (odd source terms, group 2) of the identification Root8[12]+ <->
Twelfth[34]- (record r8f:R86+, e = 1)

Dense source or long words: the tensor part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 2 of the chunks of the source list. -/
def wR8fR86pHTg2 : List (ℕ × ℤ) :=
  decodeTerms wR8fR86pHT16Labs wR8fR86pHT16Nums 808

set_option maxRecDepth 100000 in
/-- The odd part of the tensor pairing over group 2 of the source terms. -/
theorem wR8fR86p_ol2 : oddSumL 96 true wR8fR86pGX wR8fR86pHTg2 = 56229888 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
