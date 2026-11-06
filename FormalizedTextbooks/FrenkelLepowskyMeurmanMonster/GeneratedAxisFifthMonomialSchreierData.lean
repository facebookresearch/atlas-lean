/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthMonomialSystemOrbit

/-! Bounded original-word certificates for the six-generator monomial system stabilizer. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Literal inverses of the six already bound actual physical permutations. -/
def generatedFifthSixBackward : Fin 6 → Fin 24 → Fin 24 :=
  ![![0, 2, 1, 3, 4, 7, 6, 5, 21, 20, 22, 23, 13, 12, 14, 15, 17, 16, 18, 19, 9, 8, 10, 11],
    ![2, 3, 0, 1, 7, 6, 5, 4, 8, 9, 10, 11, 13, 12, 15, 14, 16, 17, 18, 19, 21, 20, 23, 22],
    ![3, 1, 2, 0, 4, 7, 6, 5, 22, 23, 21, 20, 12, 13, 15, 14, 17, 16, 18, 19, 11, 10, 8, 9],
    ![0, 2, 1, 3, 14, 12, 15, 13, 11, 9, 10, 8, 5, 7, 4, 6, 17, 16, 18, 19, 20, 23, 22, 21],
    ![18, 1, 17, 0, 9, 4, 10, 6, 23, 13, 12, 21, 15, 14, 20, 22, 2, 16, 3, 19, 5, 11, 7, 8],
    ![2, 16, 3, 19, 6, 10, 4, 9, 20, 15, 14, 22, 13, 12, 23, 21, 18, 1, 17, 0, 8, 7, 11, 5]]

/-- Literal forward coordinates of the fifteen original system representative words. -/
def generatedFifthSystemRepForward : Fin 15 → Fin 24 → Fin 24 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    ![18, 1, 19, 3, 7, 9, 8, 4, 6, 5, 11, 10, 12, 23, 14, 20, 16, 17, 0, 2, 15, 21, 22, 13],
    ![0, 1, 2, 18, 9, 13, 22, 7, 8, 4, 15, 21, 12, 5, 20, 10, 17, 16, 3, 19, 14, 11, 6, 23],
    ![1, 19, 2, 17, 12, 15, 21, 20, 5, 10, 4, 8, 23, 13, 14, 22, 18, 0, 3, 16, 11, 9, 7, 6],
    ![18, 2, 19, 3, 5, 20, 21, 4, 6, 7, 23, 22, 13, 11, 14, 9, 17, 16, 0, 1, 15, 8, 10, 12],
    ![18, 3, 19, 1, 4, 9, 8, 7, 5, 6, 11, 10, 13, 22, 15, 21, 16, 17, 2, 0, 14, 20, 23, 12],
    ![3, 19, 16, 17, 20, 10, 5, 12, 21, 15, 8, 4, 23, 6, 14, 11, 18, 0, 1, 2, 22, 9, 7, 13],
    ![18, 1, 19, 0, 5, 23, 22, 4, 6, 7, 20, 21, 12, 9, 15, 11, 17, 16, 3, 2, 14, 10, 8, 13],
    ![2, 3, 0, 18, 9, 12, 23, 4, 8, 7, 14, 20, 13, 6, 21, 10, 17, 16, 1, 19, 15, 11, 5, 22],
    ![1, 19, 2, 3, 10, 13, 7, 20, 5, 12, 22, 9, 23, 15, 11, 4, 0, 18, 17, 16, 14, 8, 21, 6],
    ![2, 19, 1, 16, 13, 15, 8, 9, 7, 22, 4, 21, 11, 12, 14, 10, 18, 0, 3, 17, 23, 20, 5, 6],
    ![0, 19, 2, 3, 9, 15, 21, 7, 8, 4, 13, 22, 23, 10, 14, 5, 17, 16, 18, 1, 20, 6, 11, 12],
    ![0, 3, 2, 1, 7, 5, 6, 4, 9, 8, 10, 11, 23, 22, 20, 21, 16, 17, 19, 18, 14, 15, 13, 12],
    ![3, 18, 19, 1, 9, 4, 8, 7, 13, 22, 21, 15, 5, 6, 10, 11, 17, 16, 2, 0, 20, 14, 23, 12],
    ![19, 3, 18, 0, 5, 12, 13, 7, 6, 4, 14, 15, 23, 8, 21, 11, 17, 16, 1, 2, 20, 10, 9, 22]]

/-- Literal backward coordinates of those actual word representatives. -/
def generatedFifthSystemRepBackward : Fin 15 → Fin 24 → Fin 24 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    ![18, 1, 19, 3, 7, 9, 8, 4, 6, 5, 11, 10, 12, 23, 14, 20, 16, 17, 0, 2, 15, 21, 22, 13],
    ![0, 1, 2, 18, 9, 13, 22, 7, 8, 4, 15, 21, 12, 5, 20, 10, 17, 16, 3, 19, 14, 11, 6, 23],
    ![17, 0, 2, 18, 10, 8, 23, 22, 11, 21, 9, 20, 4, 13, 14, 5, 19, 3, 16, 1, 7, 6, 15, 12],
    ![18, 19, 1, 3, 7, 4, 8, 9, 21, 15, 22, 13, 23, 12, 14, 20, 17, 16, 0, 2, 5, 6, 11, 10],
    ![19, 3, 18, 1, 4, 8, 9, 7, 6, 5, 11, 10, 23, 12, 20, 14, 16, 17, 0, 2, 21, 15, 13, 22],
    ![17, 18, 19, 0, 11, 6, 13, 22, 10, 21, 5, 15, 7, 23, 14, 9, 2, 3, 16, 1, 4, 8, 20, 12],
    ![3, 1, 19, 18, 7, 4, 8, 9, 22, 13, 21, 15, 12, 23, 20, 14, 17, 16, 0, 2, 10, 11, 6, 5],
    ![2, 18, 0, 1, 7, 22, 13, 9, 8, 4, 15, 21, 5, 12, 10, 20, 17, 16, 3, 19, 11, 14, 23, 6],
    ![16, 0, 2, 3, 15, 8, 23, 6, 21, 11, 4, 14, 9, 5, 20, 13, 19, 18, 17, 1, 7, 22, 10, 12],
    ![17, 2, 0, 18, 10, 22, 23, 8, 6, 7, 15, 12, 13, 4, 14, 5, 3, 19, 16, 1, 21, 11, 9, 20],
    ![0, 19, 2, 3, 9, 15, 21, 7, 8, 4, 13, 22, 23, 10, 14, 5, 17, 16, 18, 1, 20, 6, 11, 12],
    ![0, 3, 2, 1, 7, 5, 6, 4, 9, 8, 10, 11, 23, 22, 20, 21, 16, 17, 19, 18, 14, 15, 13, 12],
    ![19, 3, 18, 0, 5, 12, 13, 7, 6, 4, 14, 15, 23, 8, 21, 11, 17, 16, 1, 2, 20, 10, 9, 22],
    ![3, 18, 19, 1, 9, 4, 8, 7, 13, 22, 21, 15, 5, 6, 10, 11, 17, 16, 2, 0, 20, 14, 23, 12]]

/-- Original six-generator words for all75 stabilizer Schreier transitions. -/
def generatedFifthSixSchreierWord : Fin 5 → Fin 15 → List (Fin 6 × Bool) :=
  ![![[], [], [], [(0, false)], [], [], [(4, false), (1, false), (4, false), (0, false), (5,
    true), (0, false)], [], [], [(3, false)], [(0, false), (5, false), (0, false), (4, true),
    (1, false), (4, true)], [], [], [(3, false), (5, false), (5, false), (3, false), (2,
    false)], []], ![[(0, false)], [], [(3, false)], [], [], [(5, false), (1, false), (5, false),
    (1, false), (4, true), (1, false)], [(1, false), (4, false), (1, false), (5, true), (1,
    false), (5, true)], [(5, true), (1, false), (0, false), (4, false), (2, false)], [(1,
    false), (4, false), (5, false), (1, false), (5, true), (3, false), (0, false)], [(2, false),
    (4, true), (0, false), (1, false), (5, false)], [], [(0, false), (5, false), (1, false), (3,
    false), (5, true), (4, true), (0, false)], [(0, false), (5, false), (5, false), (3, false),
    (1, false), (2, false)], [(2, false), (1, false), (3, false), (5, false), (5, false), (0,
    false)], [(0, false), (5, false), (5, false), (3, false), (5, false), (5, false), (0,
    false)]], ![[(1, false)], [], [], [(4, false)], [(4, true), (5, true), (1, false), (3,
    false), (2, false), (4, true)], [], [(5, false), (2, false), (4, false), (1, false), (4,
    false), (1, false)], [(1, false), (4, true), (1, false), (5, true), (4, false), (2, false)],
    [], [(4, true)], [(4, false), (3, false), (1, false), (5, false), (4, false), (1, false)],
    [(3, false), (5, false), (3, false), (0, false), (5, false), (1, false)], [(1, false)], [(5,
    true), (4, false), (1, false), (5, true), (4, false), (2, false)], [(5, false), (1, false),
    (5, true), (4, true), (1, false), (2, false)]], ![[], [(2, false)], [], [(4, false), (1,
    false), (3, false), (2, false), (4, true), (1, false)], [(1, false), (3, false), (1,
    false)], [], [(3, false), (1, false), (2, false), (3, false), (5, true), (4, false), (0,
    false)], [(3, false), (0, false), (1, false), (5, false), (5, false)], [(5, false), (5,
    false), (1, false), (3, false), (0, false)], [(4, false), (3, false), (1, false), (3,
    false), (5, false), (0, false)], [(4, false), (1, false), (3, false), (4, false), (1,
    false), (0, false)], [(5, true), (0, false), (4, false), (1, false), (4, true), (1, false)],
    [(4, true), (3, false), (5, false), (0, false), (4, true), (2, false), (1, false)], [], [(1,
    false), (2, false), (1, false)]], ![[], [], [], [(5, false)], [(4, false), (1, false), (4,
    false), (0, false), (5, true), (0, false)], [(4, true), (1, false), (5, false), (3, false),
    (2, false), (0, false)], [(2, false), (3, false), (4, true), (1, false), (4, true), (1,
    false)], [(1, false), (0, false), (5, true), (0, false)], [(2, false), (4, true), (1,
    false), (3, false), (5, true), (2, false)], [(5, true), (4, false), (1, false), (2, false),
    (4, false), (4, false)], [(5, false)], [(5, false), (0, false), (5, true), (4, false), (3,
    false), (4, false)], [(0, false), (5, false), (3, false), (5, false), (2, false), (4,
    false), (0, false)], [(5, false), (4, false), (4, false), (2, false), (1, false), (4,
    false), (0, false)], [(5, false), (1, false), (5, false), (1, false), (5, false)]]]

/-- Physical evaluation of an original six-generator word. -/
def generatedFifthSixFiniteWord (w : List (Fin 6 × Bool)) (i : Fin 24) : Fin 24 :=
  w.foldr (fun l x => if l.2 then generatedFifthSixBackward l.1 x
    else generatedFifthMonomialSpatialForward l.1 x) i

set_option maxRecDepth 100000 in
/-- The displayed six backward arrays are genuine inverses of the bound forward arrays. -/
theorem generatedFifthSixBackward_certificate : ∀ k : Fin 6, ∀ i : Fin 24,
    generatedFifthMonomialSpatialForward k (generatedFifthSixBackward k i) = i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The displayed representative arrays evaluate their original selected-generator words. -/
theorem generatedFifthSystemRepForward_certificate : ∀ i : Fin 15, ∀ j : Fin 24,
    (generatedFifthMonomialSystemWord i).foldr
      (fun k x => generatedFifthSelectedOctadForward k x) j =
      generatedFifthSystemRepForward i j := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Each displayed inverse is inverse to its genuinely bound representative array. -/
theorem generatedFifthSystemRepBackward_certificate : ∀ i : Fin 15, ∀ j : Fin 24,
    generatedFifthSystemRepForward i (generatedFifthSystemRepBackward i j) = j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Verify all75 original Schreier transitions on all24 physical coordinate positions.
/-- Each stabilizer transition equals its bounded original six-generator word. -/
theorem generatedFifthSixSchreier_certificate : ∀ k : Fin 5, ∀ i : Fin 15, ∀ j : Fin 24,
    generatedFifthSystemRepBackward (generatedFifthMonomialSystemTransition k i)
        (generatedFifthSelectedOctadForward k (generatedFifthSystemRepForward i j)) =
      generatedFifthSixFiniteWord (generatedFifthSixSchreierWord k i) j := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
