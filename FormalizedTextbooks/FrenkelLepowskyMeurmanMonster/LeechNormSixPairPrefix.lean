/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightCountTypes

/-! The exact paired-prefix catalogue in the original bounded source interval. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Original bounded pairs with prescribed residues and integer coordinate sum four. -/
def leechNormSixPairPrefix (m : Bool) (a b : ZMod 2) : Finset (Fin 17 × Fin 17) :=
  Finset.univ.filter fun p =>
    (leechNormEightCoordinate p.1 : ZMod 4) =
      (m.toNat : ZMod 4) + 2 * (a.val : ZMod 4) ∧
    (leechNormEightCoordinate p.2 : ZMod 4) =
      (m.toNat : ZMod 4) + 2 * (b.val : ZMod 4) ∧
    leechNormEightCoordinate p.1 + leechNormEightCoordinate p.2 = 4

/-- Literal interval addresses of every permitted pair, including pairs above the target norm. -/
def leechNormSixPairPrefixCatalogue (m : Bool) (a b : ZMod 2) :
    Finset (Fin 17 × Fin 17) :=
  if m then
    if a = 0 ∧ b = 1 then {(5, 15), (9, 11), (13, 7)}
    else if a = 1 ∧ b = 0 then {(15, 5), (11, 9), (7, 13)} else ∅
  else
    if a = 0 ∧ b = 0 then {(12, 8), (8, 12), (4, 16), (16, 4)}
    else if a = 1 ∧ b = 1 then {(6, 14), (10, 10), (14, 6)} else ∅

set_option maxHeartbeats 4000000 in
-- Check all original interval pairs and both source parity/code-bit choices.
set_option maxRecDepth 10000 in
/-- The displayed prefix catalogue is exactly the original residue and pairing predicate. -/
theorem leechNormSixPairPrefix_catalogue : ∀ m : Bool, ∀ a b : ZMod 2,
    leechNormSixPairPrefix m a b = leechNormSixPairPrefixCatalogue m a b := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
