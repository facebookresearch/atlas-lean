/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairCountParts

/-! Exact finite coefficients for the paired source count. All coordinate histograms are the
previously verified original histograms; these checks select their lower-degree coefficients. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Literal source prefixes that fit square sum 48. -/
def leechNormSixPairBoundedPrefixCatalogue (m : Bool) (a b : ZMod 2) :
    Finset (Fin 17 × Fin 17) :=
  if m then
    if a = 0 ∧ b = 1 then {(9, 11), (13, 7)}
    else if a = 1 ∧ b = 0 then {(11, 9), (7, 13)} else ∅
  else
    if a = 0 ∧ b = 0 then {(12, 8), (8, 12)}
    else if a = 1 ∧ b = 1 then {(6, 14), (10, 10), (14, 6)} else ∅

/-- The bounded prefix table follows from the complete original prefix catalogue. -/
theorem leechNormSixPairBoundedPrefix_catalogue (m : Bool) (a b : ZMod 2) :
    leechNormSixPairBoundedPrefix m a b = leechNormSixPairBoundedPrefixCatalogue m a b := by
  unfold leechNormSixPairBoundedPrefix
  rw [leechNormSixPairPrefix_catalogue]
  have hc : ∀ m : Bool, ∀ a b : ZMod 2,
      (leechNormSixPairPrefixCatalogue m a b).filter
        (fun p => leechNormSixPairPrefixSquare p ≤ 48) =
      leechNormSixPairBoundedPrefixCatalogue m a b := by
    decide +kernel
  exact hc m a b

/-- An exact coefficient of the already verified 22-coordinate source convolution. -/
def leechNormSixTailCount (m : Bool) (w q : ℕ) (h : ZMod 8) : ℕ :=
  if hw : w < 23 then if hq : q < 65 then
    ∑ r : Fin (q + 1), ∑ b : ZMod 8,
      leechNormEightCountTable m 0 ⟨22 - w, by omega⟩ ⟨r.val, by omega⟩ b *
      leechNormEightCountTable m 1 ⟨w, by omega⟩ ⟨q - r.val, by omega⟩ (h - b)
  else 0 else 0

/-- Sum the exact remaining-coordinate coefficients over every permitted original prefix. -/
def leechNormSixPairContribution (m : Bool) (w : ℕ) (a b : ZMod 2) : ℕ :=
  ∑ p ∈ leechNormSixPairBoundedPrefixCatalogue m a b,
    leechNormSixTailCount m (w - a.val - b.val)
      (48 - leechNormSixPairPrefixSquare p) (4 * (m.toNat : ZMod 8) - 4)

/-- The finite convolution evaluates to these contributions for each actual
Golay weight and bit pair. -/
def leechNormSixPairExpectedContribution (m : Bool) (w : ℕ) (a b : ZMod 2) : ℕ :=
  if m then if a ≠ b then 232 else 0
  else if a = 0 ∧ b = 0 ∧ w = 8 then 256
  else if a = 1 ∧ b = 1 then if w = 8 then 1024 else if w = 12 then 512 else 0
  else 0

set_option maxHeartbeats 8000000 in
-- Evaluate the verified histogram convolutions for every permitted weight and paired source bit.
set_option maxRecDepth 10000 in
/-- Exact source-fiber contributions; the weight and bit bounds are genuine
coordinate constraints. -/
theorem leechNormSixPairContribution_expected : ∀ m : Bool, ∀ w : Fin 25, ∀ a b : ZMod 2,
    (w.val = 0 ∨ w.val = 8 ∨ w.val = 12 ∨ w.val = 16 ∨ w.val = 24) →
    a.val + b.val ≤ w.val → w.val ≤ 22 + a.val + b.val →
    leechNormSixPairContribution m w.val a b =
      leechNormSixPairExpectedContribution m w.val a b := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
