/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00ShortBatch00Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00ShortBatch01Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00ShortBatch02Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison01ShortBatch00Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison01ShortBatch01Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison01ShortBatch02Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison02ShortBatch00Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison02ShortBatch01Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison02ShortBatch02Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortAssembly

/-! Complete candidate preferred short packets for the three original local comparison words. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- All separately stored complete preferred label batches. -/
def generatedAxisGlobalOddComparisonShortLabelBatches : Fin 3 → Fin 3 → Fin 256 →
    GriessShortIndex :=
  ![![generatedAxisGlobalOddComparison00ShortBatch00Label,
    generatedAxisGlobalOddComparison00ShortBatch01Label,
    generatedAxisGlobalOddComparison00ShortBatch02Label],
    ![generatedAxisGlobalOddComparison01ShortBatch00Label,
    generatedAxisGlobalOddComparison01ShortBatch01Label,
    generatedAxisGlobalOddComparison01ShortBatch02Label],
    ![generatedAxisGlobalOddComparison02ShortBatch00Label,
    generatedAxisGlobalOddComparison02ShortBatch01Label,
    generatedAxisGlobalOddComparison02ShortBatch02Label]]

/-- The original candidate label of every preferred packet input. -/
def generatedAxisGlobalOddComparisonShortLabels (k : Fin 3) (n : Fin 552) : GriessShortIndex :=
  generatedAxisGlobalOddComparisonShortLabelBatches k ⟨n.val / 256, by omega⟩
    ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩

/-- All separately stored complete preferred phase batches. -/
def generatedAxisGlobalOddComparisonShortPhaseBatches : Fin 3 → Fin 3 → Fin 256 → ZMod 2 :=
  ![![generatedAxisGlobalOddComparison00ShortBatch00Phase,
    generatedAxisGlobalOddComparison00ShortBatch01Phase,
    generatedAxisGlobalOddComparison00ShortBatch02Phase],
    ![generatedAxisGlobalOddComparison01ShortBatch00Phase,
    generatedAxisGlobalOddComparison01ShortBatch01Phase,
    generatedAxisGlobalOddComparison01ShortBatch02Phase],
    ![generatedAxisGlobalOddComparison02ShortBatch00Phase,
    generatedAxisGlobalOddComparison02ShortBatch01Phase,
    generatedAxisGlobalOddComparison02ShortBatch02Phase]]

/-- The original candidate phase of every preferred packet input. -/
def generatedAxisGlobalOddComparisonShortPhases (k : Fin 3) (n : Fin 552) : ZMod 2 :=
  generatedAxisGlobalOddComparisonShortPhaseBatches k ⟨n.val / 256, by omega⟩
    ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
