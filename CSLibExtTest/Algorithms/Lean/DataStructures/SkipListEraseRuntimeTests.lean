/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.SkipList
public meta import CSLibExt.Algorithms.Lean.DataStructures.SkipList.Erase
public meta import Mathlib.Data.Nat.Basic

/-!
# Skip-list erasure runtime tests

Executable rows compare complete entries and complete derived levels.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SkipListEraseRuntimeTests

open SkipList

private meta def e1 : Entry Nat String := { key := 1, value := "one", height := 1 }
private meta def e2 : Entry Nat String := { key := 2, value := "two", height := 3 }
private meta def e3 : Entry Nat String := { key := 3, value := "three", height := 2 }
private meta def e4 : Entry Nat String := { key := 4, value := "four", height := 4 }

private meta def singleton : SkipList Nat String := insert 2 "two" 3 empty

private meta def gapped : SkipList Nat String :=
  insert 3 "three" 2 <| insert 1 "one" 1 empty

private meta def populated : SkipList Nat String :=
  insert 4 "four" 4 <|
    insert 1 "one" 1 <|
      insert 3 "three" 2 <|
        insert 2 "two" 3 empty

private meta def reinserted : SkipList Nat String :=
  insert 2 "TWO" 5 (erase 2 populated)

private meta def replaced : SkipList Nat String :=
  insert 2 "TWO" 9 populated

private meta def runtimeRows : List (String × Bool) :=
  [
    ("empty", (erase 1 (empty : SkipList Nat String)).entries == []),
    ("singleton-hit", (erase 2 singleton).entries == []),
    ("singleton-miss", (erase 1 singleton).entries == [e2]),
    ("before-minimum", (erase 0 populated).entries == [e1, e2, e3, e4]),
    ("absent-between", (erase 2 gapped).entries == [e1, e3]),
    ("after-maximum", (erase 5 populated).entries == [e1, e2, e3, e4]),
    ("delete-minimum", (erase 1 populated).entries == [e2, e3, e4]),
    ("delete-middle", (erase 2 populated).entries == [e1, e3, e4]),
    ("delete-maximum-tallest", (erase 4 populated).entries == [e1, e2, e3]),
    ("level-0", level 0 populated ==
      [(1, "one"), (2, "two"), (3, "three"), (4, "four")]),
    ("level-1", level 1 populated == [(2, "two"), (3, "three"), (4, "four")]),
    ("level-2", level 2 populated == [(2, "two"), (4, "four")]),
    ("level-3", level 3 populated == [(4, "four")]),
    ("level-above-maximum", level 4 populated == []),
    ("erase-tallest-level-0", level 0 (erase 4 populated) ==
      [(1, "one"), (2, "two"), (3, "three")]),
    ("erase-tallest-level-1", level 1 (erase 4 populated) ==
      [(2, "two"), (3, "three")]),
    ("erase-tallest-level-2", level 2 (erase 4 populated) == [(2, "two")]),
    ("erase-tallest-level-3", level 3 (erase 4 populated) == []),
    ("erase-tallest-above", level 4 (erase 4 populated) == []),
    ("repeated-erase", (erase 2 (erase 2 populated)).entries == [e1, e3, e4]),
    ("reinsertion-new-height", reinserted.entries ==
      [e1, { key := 2, value := "TWO", height := 5 }, e3, e4]),
    ("reinsertion-level-4", level 4 reinserted == [(2, "TWO")]),
    ("replacement-preserves-height", replaced.entries ==
      [e1, { key := 2, value := "TWO", height := 3 }, e3, e4]),
    ("replacement-level-3", level 3 replaced == [(4, "four")])
  ]

private meta def expectedRows : List (String × Bool) :=
  [
    ("empty", true),
    ("singleton-hit", true),
    ("singleton-miss", true),
    ("before-minimum", true),
    ("absent-between", true),
    ("after-maximum", true),
    ("delete-minimum", true),
    ("delete-middle", true),
    ("delete-maximum-tallest", true),
    ("level-0", true),
    ("level-1", true),
    ("level-2", true),
    ("level-3", true),
    ("level-above-maximum", true),
    ("erase-tallest-level-0", true),
    ("erase-tallest-level-1", true),
    ("erase-tallest-level-2", true),
    ("erase-tallest-level-3", true),
    ("erase-tallest-above", true),
    ("repeated-erase", true),
    ("reinsertion-new-height", true),
    ("reinsertion-level-4", true),
    ("replacement-preserves-height", true),
    ("replacement-level-3", true)
  ]

#eval runtimeRows
#eval expectedRows

#guard runtimeRows = expectedRows


end Cslib.Algorithms.Lean.SkipListEraseRuntimeTests
