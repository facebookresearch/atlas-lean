/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import CSLibExt.Algorithms.Lean.DataStructures.Treap
public meta import CSLibExt.Algorithms.Lean.DataStructures.Treap

/-! # Importing runtime checks of deterministic treap operations -/

open Cslib.Algorithms.Lean.Treap
open Tree

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError name)
  IO.println ("PASS " ++ name)

private def populated : Tree Nat Nat :=
  .node (.node .empty 5 50 20 .empty) 10 100 10
    (.node .empty 15 150 30 .empty)

#eval do
  check "empty_lookup" (lookup 7 (.empty : Tree Nat Nat) == none)
  check "empty_cost" (lookupWithCost 7 (.empty : Tree Nat Nat) == (none, 0))
  check "empty_erase" (contents (erase 7 (.empty : Tree Nat Nat)) == [])
  check "contents" (contents populated == [(5,50),(10,100),(15,150)])
  check "lookup_left" (lookup 5 populated == some 50)
  check "lookup_right" (lookup 15 populated == some 150)
  check "lookup_root" (lookupWithCost 10 populated == (some 100,1))
  check "lookup_miss" (lookupWithCost 99 populated == (none,2))
  check "split_below" (contents (split 1 populated).greater == contents populated)
  check "split_above" (contents (split 99 populated).less == contents populated)
  check "split_equal" ((split 10 populated).found == some (100,10))
  check "split_left" ((split 5 populated).found == some (50,20))
  check "split_right" ((split 15 populated).found == some (150,30))
  check "insert_new" (contents (insert 12 120 5 populated) == [(5,50),(10,100),(12,120),(15,150)])
  check "replace_value" (contents (insert 10 101 1 populated) == [(5,50),(10,101),(15,150)])
  check "replace_priority" (rootPriority (insert 10 101 1 populated) == some 1)
  check "erase_root" (contents (erase 10 populated) == [(5,50),(15,150)])
  check "erase_left" (contents (erase 5 populated) == [(10,100),(15,150)])
  check "erase_right" (contents (erase 15 populated) == [(5,50),(10,100)])
  check "erase_miss" (contents (erase 99 populated) == contents populated)
  check "merge_left_wins" (rootPriority (merge (.node .empty 1 1 1 .empty) (.node .empty 2 2 2 .empty)) == some 1)
  check "merge_right_wins" (rootPriority (merge (.node .empty 1 1 2 .empty) (.node .empty 2 2 1 .empty)) == some 1)
  check "merge_tie" (contents (merge (.node .empty 1 1 1 .empty) (.node .empty 2 2 1 .empty)) == [(1,1),(2,2)])
