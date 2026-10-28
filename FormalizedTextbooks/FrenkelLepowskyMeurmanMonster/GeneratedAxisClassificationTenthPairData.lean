/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthFinalShortNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPairCoordinates

/-! A compressed original-source inverse for every pair row of the complete root-2 packet. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 10000

/-- Every genuine incoming short label in its original finite packet order. -/
def generatedTenthIncomingShortLabel (n : Fin 4136) : GriessShortIndex :=
  generatedAxisGlobalFifthRoot02ShortLabels
    ⟨n.val / 256, by omega⟩ ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩

/-- Every original central phase in the identical packet order. -/
def generatedTenthIncomingShortPhase (n : Fin 4136) : ZMod 2 :=
  generatedAxisGlobalFifthRoot02ShortPhases
    ⟨n.val / 256, by omega⟩ ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩

/-- The unique original packet entry for a pair row, or 4136 when no entry maps to that row. -/
def generatedTenthPairSource : Fin 552 → ℕ :=
  ![
    4136, 4136, 3435, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 2194,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 3361, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4102, 4136, 4136, 4136, 3142, 4136, 4136, 4136, 4136, 4136, 3592, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 2829, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 2951, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    1890, 4136, 4136, 4136, 4136, 4136, 1536, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 655, 4136, 4136, 4136, 4136, 4136, 2042, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 1289, 4136, 4136, 4136,
    4136, 4136, 3708, 4136, 4136, 4136, 3516, 4136, 4136, 4136, 4136, 4136, 3218, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 2568, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 1408, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 1644, 4136, 4136,
    4136, 4136, 4136, 1742, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136
  ]

/-- All source identifiers are valid packet numbers or the unique outside sentinel. -/
theorem generatedTenth_pair_source_bound (p : Fin 552) :
    generatedTenthPairSource p ≤ 4136 := by
  revert p
  decide +kernel

/-- The actual outgoing pair number, or 552 for either nonpair family. -/
def generatedTenthIncomingPairNumber (n : Fin 4136) : ℕ :=
  match generatedTenthIncomingShortLabel n with
  | Sum.inl (s, p) => 276 * s.val + p.val
  | Sum.inr _ => 552

set_option maxHeartbeats 64000000 in
-- Check every original finite dictionary label against the compressed source inverse.
/-- The complete outgoing pair-number graph has exactly the recorded original source. -/
theorem generatedTenth_pair_source_graph : ∀ n : Fin 4136,
    if h : generatedTenthIncomingPairNumber n < 552 then
      generatedTenthPairSource ⟨generatedTenthIncomingPairNumber n, h⟩ = n.val
    else True := by
  decide +kernel

/-- Every actual packet entry reaching a pair row has its unique recorded original source. -/
theorem generatedTenth_pair_source_forward (n : Fin 4136) :
    match generatedTenthIncomingShortLabel n with
    | Sum.inl (s, p) => generatedTenthPairSource ⟨276 * s.val + p.val, by omega⟩ = n.val
    | Sum.inr _ => True := by
  have h := generatedTenth_pair_source_graph n
  cases he : generatedTenthIncomingShortLabel n with
  | inl p =>
    rcases p with ⟨s, p⟩
    have hb : 276 * s.val + p.val < 552 := by omega
    simpa only [generatedTenthIncomingPairNumber, he, hb, dite_eq_left] using h
  | inr _ => trivial

set_option maxHeartbeats 64000000 in
-- Check all 552 original inverse rows, including each outside sentinel.
/-- Every finite nonsentinel inverse reconstructs exactly its actual outgoing pair row. -/
theorem generatedTenth_pair_source_reverse_checked : ∀ (s : Fin 2) (p : Fin 276),
    if h : generatedTenthPairSource ⟨276 * s.val + p.val, by omega⟩ < 4136 then
      generatedTenthIncomingShortLabel
        ⟨generatedTenthPairSource ⟨276 * s.val + p.val, by omega⟩, h⟩ = Sum.inl (s, p)
    else True := by
  decide +kernel

/-- Every nonsentinel inverse identifies exactly the actual original pair row. -/
theorem generatedTenth_pair_source_reverse (s : Fin 2) (p : Fin 276)
    (h : generatedTenthPairSource ⟨276 * s.val + p.val, by omega⟩ < 4136) :
    generatedTenthIncomingShortLabel
      ⟨generatedTenthPairSource ⟨276 * s.val + p.val, by omega⟩, h⟩ = Sum.inl (s, p) := by
  simpa only [h, dite_eq_left] using generatedTenth_pair_source_reverse_checked s p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
