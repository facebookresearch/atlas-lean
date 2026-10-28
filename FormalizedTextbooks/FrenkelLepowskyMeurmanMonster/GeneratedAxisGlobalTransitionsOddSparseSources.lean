/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortNumbers
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRational
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsIntegerPrimitives
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSparseTree00Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSparseTree01Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSparseTree02Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSparseTree03Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSparseTree04Data

/-! Original labels, phases and exact sparse keys for two inputs and three comparison outputs. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- Five complete original coordinate trees: input roots zero and six, then comparison zero through two. -/
def generatedAxisGlobalOddSparseTree : Fin 5 →
    GeneratedAxisGlobalSparseLookupTree GeneratedAxisGlobalOddShortPacketIndex :=
  ![generatedAxisGlobalOddSparseTree00, generatedAxisGlobalOddSparseTree01,
    generatedAxisGlobalOddSparseTree02, generatedAxisGlobalOddSparseTree03,
    generatedAxisGlobalOddSparseTree04]

/-- Every stored source unit has its literal original preferred coordinate. -/
def generatedAxisGlobalOddSparseLabel (k : Fin 5)
    (p : GeneratedAxisGlobalOddShortPacketIndex) : GriessShortIndex :=
  ![generatedAxisGlobalOddShortRootLabels 0 (generatedAxisGlobalOddShortPacketNumber p),
    generatedAxisGlobalOddShortRootLabels 6 (generatedAxisGlobalOddShortPacketNumber p),
    generatedAxisGlobalOddComparisonShortLabels 0 (generatedAxisGlobalOddShortPacketNumber p),
    generatedAxisGlobalOddComparisonShortLabels 1 (generatedAxisGlobalOddShortPacketNumber p),
    generatedAxisGlobalOddComparisonShortLabels 2 (generatedAxisGlobalOddShortPacketNumber p)] k

/-- Every sparse coefficient retains the original source central phase. -/
def generatedAxisGlobalOddSparsePhase (k : Fin 5)
    (p : GeneratedAxisGlobalOddShortPacketIndex) : ZMod 2 :=
  ![generatedAxisGlobalOddShortRootPhases 0 (generatedAxisGlobalOddShortPacketNumber p),
    generatedAxisGlobalOddShortRootPhases 6 (generatedAxisGlobalOddShortPacketNumber p),
    generatedAxisGlobalOddComparisonShortPhases 0 (generatedAxisGlobalOddShortPacketNumber p),
    generatedAxisGlobalOddComparisonShortPhases 1 (generatedAxisGlobalOddShortPacketNumber p),
    generatedAxisGlobalOddComparisonShortPhases 2 (generatedAxisGlobalOddShortPacketNumber p)] k

/-- The coefficient is the original rational preferred-pair source coefficient with its actual sign. -/
def generatedAxisGlobalOddSparseCoefficient (k : Fin 5)
    (p : GeneratedAxisGlobalOddShortPacketIndex) : ℚ :=
  generatedAxisGlobalOddShortCoefficientQ p *
    (generatedAxisGlobalIntSign (generatedAxisGlobalOddSparsePhase k p) : ℚ)

/-- A successful lookup is an original preferred-pair index; absent coordinates return no index. -/
def generatedAxisGlobalOddSparseSource (k : Fin 5) (r : GriessShortIndex) :
    Option GeneratedAxisGlobalOddShortPacketIndex :=
  generatedAxisGlobalSparseLookup (generatedAxisGlobalOddSparseTree k)
    (generatedAxisGlobalShortNumber r)

/-- An executable exact rational coefficient at any original preferred short coordinate. -/
def generatedAxisGlobalOddSparseShortQ (k : Fin 5) (r : GriessShortIndex) : ℚ :=
  match generatedAxisGlobalOddSparseSource k r with
  | none => 0
  | some p => generatedAxisGlobalOddSparseCoefficient k p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
