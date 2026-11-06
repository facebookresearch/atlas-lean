/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthFinalShortNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPairCoordinates

/-! A compressed original-source inverse for every pair row of the complete root-3 packet. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 10000

/-- Every genuine incoming short label in its original finite packet order. -/
def generatedEleventhIncomingShortLabel (n : Fin 4136) : GriessShortIndex :=
  generatedAxisGlobalFifthRoot03ShortLabels
    ⟨n.val / 256, by omega⟩ ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩

/-- Every original central phase in the identical packet order. -/
def generatedEleventhIncomingShortPhase (n : Fin 4136) : ZMod 2 :=
  generatedAxisGlobalFifthRoot03ShortPhases
    ⟨n.val / 256, by omega⟩ ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩

/-- The unique original packet entry for a pair row, or 4136 when no entry maps to that row. -/
def generatedEleventhPairSource : Fin 552 → ℕ :=
  ![
    2946, 2951, 344, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 279, 2936, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 2941, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 1214, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 1207, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 3638,
    3637, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 2533, 2534, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 106, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 23, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 1193, 3351, 3470, 4136, 4136, 4136, 4136, 3473,
    3336, 4136, 4136, 4136, 4136, 1216, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 1357,
    4136, 4136, 1342, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 3316, 4136, 3435, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 3444, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 3307,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 457, 4136, 4136, 4136, 2529, 2530, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    444, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 3634, 3633, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 2850, 2849, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 2846, 2845, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 1365, 4136, 235, 242, 4136, 1350
  ]

/-- All source identifiers are valid packet numbers or the unique outside sentinel. -/
theorem generatedEleventh_pair_source_bound (p : Fin 552) :
    generatedEleventhPairSource p ≤ 4136 := by
  revert p
  decide +kernel

/-- The actual outgoing pair number, or 552 for either nonpair family. -/
def generatedEleventhIncomingPairNumber (n : Fin 4136) : ℕ :=
  match generatedEleventhIncomingShortLabel n with
  | Sum.inl (s, p) => 276 * s.val + p.val
  | Sum.inr _ => 552

set_option maxHeartbeats 64000000 in
-- Check every original finite dictionary label against the compressed source inverse.
/-- The complete outgoing pair-number graph has exactly the recorded original source. -/
theorem generatedEleventh_pair_source_graph : ∀ n : Fin 4136,
    if h : generatedEleventhIncomingPairNumber n < 552 then
      generatedEleventhPairSource ⟨generatedEleventhIncomingPairNumber n, h⟩ = n.val
    else True := by
  decide +kernel

/-- Every actual packet entry reaching a pair row has its unique recorded original source. -/
theorem generatedEleventh_pair_source_forward (n : Fin 4136) :
    match generatedEleventhIncomingShortLabel n with
    | Sum.inl (s, p) => generatedEleventhPairSource ⟨276 * s.val + p.val, by omega⟩ = n.val
    | Sum.inr _ => True := by
  have h := generatedEleventh_pair_source_graph n
  cases he : generatedEleventhIncomingShortLabel n with
  | inl p =>
    rcases p with ⟨s, p⟩
    have hb : 276 * s.val + p.val < 552 := by omega
    simpa only [generatedEleventhIncomingPairNumber, he, hb, dite_eq_left] using h
  | inr _ => trivial

set_option maxHeartbeats 64000000 in
-- Check all 552 original inverse rows, including each outside sentinel.
/-- Every finite nonsentinel inverse reconstructs exactly its actual outgoing pair row. -/
theorem generatedEleventh_pair_source_reverse_checked : ∀ (s : Fin 2) (p : Fin 276),
    if h : generatedEleventhPairSource ⟨276 * s.val + p.val, by omega⟩ < 4136 then
      generatedEleventhIncomingShortLabel
        ⟨generatedEleventhPairSource ⟨276 * s.val + p.val, by omega⟩, h⟩ = Sum.inl (s, p)
    else True := by
  decide +kernel

/-- Every nonsentinel inverse identifies exactly the actual original pair row. -/
theorem generatedEleventh_pair_source_reverse (s : Fin 2) (p : Fin 276)
    (h : generatedEleventhPairSource ⟨276 * s.val + p.val, by omega⟩ < 4136) :
    generatedEleventhIncomingShortLabel
      ⟨generatedEleventhPairSource ⟨276 * s.val + p.val, by omega⟩, h⟩ = Sum.inl (s, p) := by
  simpa only [h, dite_eq_left] using generatedEleventh_pair_source_reverse_checked s p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
