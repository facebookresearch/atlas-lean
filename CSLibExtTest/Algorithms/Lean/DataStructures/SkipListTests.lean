/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.SkipList
public import Mathlib.Data.Nat.Basic

/-!
# Skip-list tests

Executable examples cover the representation invariant, genuine carried-suffix navigation,
lookup, level nesting, and duplicate replacement.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SkipListTests

open SkipList

private def singleton : SkipList Nat String :=
  insert 7 "seven" 2 empty

public def populated : SkipList Nat String :=
  insert 4 "four" 4 <|
    insert 1 "one" 1 <|
      insert 3 "three" 2 <|
        insert 2 "two" 3 empty

private theorem populatedValid : Valid populated :=
  valid_insert (valid_insert (valid_insert (valid_insert valid_empty)))

example : Valid (empty : SkipList Nat String) := valid_empty
example : lookup 5 (empty : SkipList Nat String) = none := by decide
example : Valid singleton := valid_insert valid_empty
example : lookup 7 singleton = some "seven" := by decide
example : lookup 8 singleton = none := by decide

/-- At level two, the visible predecessor `2` skips the prefix through that key. -/
public theorem upper_level_progress_example :
    (advanceAtLevel 4 2 populated.entries).map Entry.key = [3, 4] := by
  decide

/-- The next lower level continues from the upper-level suffix instead of restarting. -/
public theorem lower_level_continues_example :
    (advanceAtLevel 4 1 (advanceAtLevel 4 2 populated.entries)).map Entry.key = [4] := by
  decide

/-- The complete top-down search retains the narrowed lower-level window. -/
public theorem search_window_example :
    (searchWindow 4 populated).map Entry.key = [4] := by
  decide

example : lookup 3 populated = some "three" := by decide
example : lookup 5 populated = none := by decide
example : level 0 populated = [(1, "one"), (2, "two"), (3, "three"), (4, "four")] := by
  decide
example : level 1 populated = [(2, "two"), (3, "three"), (4, "four")] := by decide
example : level 2 populated = [(2, "two"), (4, "four")] := by decide
example : level 3 populated = [(4, "four")] := by decide

private def replaced : SkipList Nat String :=
  insert 2 "TWO" 9 populated

example : Valid replaced := valid_insert populatedValid
example : lookup 2 replaced = some "TWO" := by decide
example : heightOf 2 replaced = some 3 :=
  heightOf_insert_of_present 2 "TWO" 9 3 populated populatedValid (by decide)
example : level 8 replaced = [] := by decide

example : heightOf 5 (insert 5 "five" 0 populated) = some 1 :=
  heightOf_insert_of_absent 5 "five" 0 populated (by decide)
example : heightOf 6 (insert 6 "six" 3 populated) = some 3 :=
  heightOf_insert_of_absent 6 "six" 3 populated (by decide)

example : lookup 4 populated = (abstraction populated).lookup 4 :=
  lookup_eq_abstraction 4 populated

#check abstraction_keys_nodup
#check level_keys_nodup
#check level_succ_sublist_level
#check advanceAtLevel_suffix
#check searchWindow
#check searchWindow_suffix
#check lookup_insert
#check lookup_insert_of_ne
#check heightOf_insert_of_present
#check heightOf_insert_of_absent
#check valid_insert
#check lookup_eq_abstraction

#print axioms abstraction_keys_nodup
#print axioms level_keys_nodup
#print axioms level_succ_sublist_level
#print axioms advanceAtLevel_suffix
#print axioms searchWindow_suffix
#print axioms search_window_example
#print axioms valid_insert
#print axioms lookup_eq_abstraction
#print axioms lookup_insert
#print axioms lookup_insert_of_ne
#print axioms heightOf_insert_of_present
#print axioms heightOf_insert_of_absent

end Cslib.Algorithms.Lean.SkipListTests
