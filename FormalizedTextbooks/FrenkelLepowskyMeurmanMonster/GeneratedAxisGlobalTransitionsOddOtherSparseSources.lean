/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortNumbers
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRationalCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddOtherSparseTree02Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddOtherSparseTree03Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddOtherSparseTree04Data

/-! Executable sparse coefficients retain the complete original preferred-source indices and phases for roots two, three, and four. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- The exact original root index of each complete sparse source packet. -/
def generatedAxisGlobalOddOtherSparseRoot : Fin 3 → Fin 9 := ![2, 3, 4]

/-- The complete exact source coordinate tree for each actual root word. -/
def generatedAxisGlobalOddOtherSparseTree : Fin 3 →
    GeneratedAxisGlobalSparseLookupTree GeneratedAxisGlobalOddShortPacketIndex :=
  ![generatedAxisGlobalOddOtherSparseTree02, generatedAxisGlobalOddOtherSparseTree03,
    generatedAxisGlobalOddOtherSparseTree04]

/-- Every sparse index keeps its original preferred short coordinate. -/
def generatedAxisGlobalOddOtherSparseLabel (k : Fin 3)
    (p : GeneratedAxisGlobalOddShortPacketIndex) : GriessShortIndex :=
  generatedAxisGlobalOddShortRootLabels (generatedAxisGlobalOddOtherSparseRoot k)
    (generatedAxisGlobalOddShortPacketNumber p)

/-- The complete original rational coefficient includes its actual source central phase. -/
def generatedAxisGlobalOddOtherSparseCoefficient (k : Fin 3)
    (p : GeneratedAxisGlobalOddShortPacketIndex) : ℚ :=
  generatedAxisGlobalOddShortCoefficientQ p *
    (generatedAxisGlobalIntSign (generatedAxisGlobalOddShortRootPhases
      (generatedAxisGlobalOddOtherSparseRoot k) (generatedAxisGlobalOddShortPacketNumber p)) : ℚ)

/-- An exact coordinate lookup returns only its original preferred source index. -/
def generatedAxisGlobalOddOtherSparseSource (k : Fin 3) (r : GriessShortIndex) :
    Option GeneratedAxisGlobalOddShortPacketIndex :=
  generatedAxisGlobalSparseLookup (generatedAxisGlobalOddOtherSparseTree k)
    (generatedAxisGlobalShortNumber r)

/-- Every original coordinate is assigned its exact complete source coefficient, including zero. -/
def generatedAxisGlobalOddOtherSparseShortQ (k : Fin 3) (r : GriessShortIndex) : ℚ :=
  match generatedAxisGlobalOddOtherSparseSource k r with
  | none => 0
  | some p => generatedAxisGlobalOddOtherSparseCoefficient k p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
