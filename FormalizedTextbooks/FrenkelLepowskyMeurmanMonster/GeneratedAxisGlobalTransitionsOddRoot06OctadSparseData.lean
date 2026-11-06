/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadSupportData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSparseLookup
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortNumbers

/-! Exact candidate sparse lookup of the full root-six positive nonzero short support. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- Balanced lookup retaining all 120 original nonzero outgoing source labels. -/
def generatedAxisGlobalOddRoot06OctadSparseTree : GeneratedAxisGlobalSparseLookupTree (Fin 120) :=
  (.branch 54208 60 (.branch 16104 30 (.branch 2353 15 (.branch 610 7 (.branch 529 3 (.branch 273 1 (.branch 250 0 .empty .empty) (.branch 528 2 .empty .empty)) (.branch 544 5 (.branch 543 4 .empty .empty) (.branch 571 6 .empty .empty))) (.branch 1033 11 (.branch 1001 9 (.branch 1000 8 .empty .empty) (.branch 1008 10 .empty .empty)) (.branch 1041 13 (.branch 1040 12 .empty .empty) (.branch 2350 14 .empty .empty)))) (.branch 2434 23 (.branch 2385 19 (.branch 2369 17 (.branch 2366 16 .empty .empty) (.branch 2382 18 .empty .empty)) (.branch 2418 21 (.branch 2413 20 .empty .empty) (.branch 2429 22 .empty .empty))) (.branch 2481 27 (.branch 2450 25 (.branch 2445 24 .empty .empty) (.branch 2478 26 .empty .empty)) (.branch 2546 29 (.branch 2541 28 .empty .empty) .empty)))) (.branch 40500 45 (.branch 16440 38 (.branch 16184 34 (.branch 16168 32 (.branch 16119 31 .empty .empty) (.branch 16183 33 .empty .empty)) (.branch 16200 36 (.branch 16199 35 .empty .empty) (.branch 16215 37 .empty .empty))) (.branch 33201 42 (.branch 16520 40 (.branch 16455 39 .empty .empty) (.branch 16535 41 .empty .empty)) (.branch 40491 44 (.branch 33224 43 .empty .empty) .empty))) (.branch 40724 53 (.branch 40532 49 (.branch 40516 47 (.branch 40507 46 .empty .empty) (.branch 40523 48 .empty .empty)) (.branch 40564 51 (.branch 40555 50 .empty .empty) (.branch 40715 52 .empty .empty))) (.branch 54139 57 (.branch 40772 55 (.branch 40763 54 .empty .empty) (.branch 54136 56 .empty .empty)) (.branch 54142 59 (.branch 54141 58 .empty .empty) .empty))))) (.branch 68061 90 (.branch 54646 75 (.branch 54496 68 (.branch 54424 64 (.branch 54213 62 (.branch 54211 61 .empty .empty) (.branch 54214 63 .empty .empty)) (.branch 54429 66 (.branch 54427 65 .empty .empty) (.branch 54430 67 .empty .empty))) (.branch 54640 72 (.branch 54501 70 (.branch 54499 69 .empty .empty) (.branch 54502 71 .empty .empty)) (.branch 54645 74 (.branch 54643 73 .empty .empty) .empty))) (.branch 54742 83 (.branch 54670 79 (.branch 54667 77 (.branch 54664 76 .empty .empty) (.branch 54669 78 .empty .empty)) (.branch 54739 81 (.branch 54736 80 .empty .empty) (.branch 54741 82 .empty .empty))) (.branch 54766 87 (.branch 54763 85 (.branch 54760 84 .empty .empty) (.branch 54765 86 .empty .empty)) (.branch 68059 89 (.branch 68056 88 .empty .empty) .empty)))) (.branch 68371 105 (.branch 68157 98 (.branch 68133 94 (.branch 68128 92 (.branch 68062 91 .empty .empty) (.branch 68131 93 .empty .empty)) (.branch 68152 96 (.branch 68134 95 .empty .empty) (.branch 68155 97 .empty .empty))) (.branch 68229 102 (.branch 68224 100 (.branch 68158 99 .empty .empty) (.branch 68227 101 .empty .empty)) (.branch 68368 104 (.branch 68230 103 .empty .empty) .empty))) (.branch 68659 113 (.branch 68395 109 (.branch 68374 107 (.branch 68373 106 .empty .empty) (.branch 68392 108 .empty .empty)) (.branch 68398 111 (.branch 68397 110 .empty .empty) (.branch 68656 112 .empty .empty))) (.branch 68683 117 (.branch 68662 115 (.branch 68661 114 .empty .empty) (.branch 68680 116 .empty .empty)) (.branch 68686 119 (.branch 68685 118 .empty .empty) .empty))))))

/-- Candidate outgoing preferred-label lookup in the complete original short catalogue. -/
def generatedAxisGlobalOddRoot06OctadSparseSource (r : GriessShortIndex) : Option (Fin 120) :=
  generatedAxisGlobalSparseLookup generatedAxisGlobalOddRoot06OctadSparseTree (generatedAxisGlobalShortNumber r)

/-- Candidate outgoing coefficient includes every retained original support phase. -/
def generatedAxisGlobalOddRoot06OctadSparseShortQ (r : GriessShortIndex) : ℚ :=
  match generatedAxisGlobalOddRoot06OctadSparseSource r with
  | some p => generatedAxisGlobalOddRoot06OctadSourceCoefficient p
  | none => 0

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
