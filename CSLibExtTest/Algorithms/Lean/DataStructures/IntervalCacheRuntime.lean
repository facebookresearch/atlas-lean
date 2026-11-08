/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.DataStructures.IntervalTree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
# Asserting interval metadata diagnostics

Each PASS label is emitted only after its IO assertion succeeds.
-/

open Cslib.Algorithms.Lean.IntervalTree

namespace IntervalMetadataRuntime

private meta def entry (id : Nat) (low high : Int) : Entry :=
  ⟨id, ⟨low, high⟩⟩

private meta def check (name : String) (condition : Bool) : IO Unit := do
  unless condition do
    throw (IO.userError s!"interval metadata assertion failed: {name}")
  IO.println s!"PASS {name}"

public meta def main : IO Unit := do
  let emptyTree : Tree := .empty
  let singleton := Tree.singleton (entry 0 (-8) (-3))
  let left := Tree.singleton (entry 0 (-9) (-7))
  let right := Tree.singleton (entry 2 (-2) (-1))
  let root := entry 1 (-6) (-3)
  let good := Tree.mkNode left root right
  let tied := Tree.mkNode (Tree.singleton (entry 0 (-7) (-2)))
    (entry 1 (-5) (-2)) (Tree.singleton (entry 2 (-3) (-2)))
  check "empty_checker" emptyTree.cacheOK
  check "empty_maximum" (emptyTree.cachedMax? == none)
  check "negative_singleton" (singleton.cacheOK &&
    (singleton.height, singleton.size, singleton.cachedMax?) == (1, 1, some (-3)))
  check "negative_tree" (good.cacheOK &&
    (good.height, good.size, good.cachedMax?) == (2, 3, some (-1)))
  check "tied_maximum" (tied.cacheOK && tied.cachedMax? == some (-2))
  check "computed_maximum" (good.computedMax? == good.cachedMax?)
  check "root_wrong_maximum" (!(Tree.node 2 3 (-2) left root right).cacheOK)
  check "root_wrong_height" (!(Tree.node 3 3 (-1) left root right).cacheOK)
  check "root_wrong_size" (!(Tree.node 2 2 (-1) left root right).cacheOK)
  let badMaxChild : Tree := .node 1 1 (-6) .empty (entry 0 (-9) (-7)) .empty
  let badHeightChild : Tree := .node 2 1 (-7) .empty (entry 0 (-9) (-7)) .empty
  let badSizeChild : Tree := .node 1 2 (-7) .empty (entry 0 (-9) (-7)) .empty
  let withBadMax := Tree.mkNode badMaxChild root right
  let withBadHeight := Tree.mkNode badHeightChild root right
  let withBadSize := Tree.mkNode badSizeChild root right
  check "child_wrong_maximum" (!withBadMax.cacheOK)
  check "child_wrong_height" (!withBadHeight.cacheOK)
  check "child_wrong_size" (!withBadSize.cacheOK)
  check "parent_local_maximum" (withBadMax.cachedMax? == some (-1))
  check "maximum_not_height" (!withBadHeight.cacheOK &&
    withBadHeight.computedMax? == withBadHeight.cachedMax?)
  check "valid_children" (Tree.mkNode left root right).cacheOK
  let unordered := Tree.mkNode (Tree.singleton (entry 0 10 12))
    (entry 1 4 7) (Tree.singleton (entry 2 0 2))
  check "cache_not_order" (unordered.cacheOK && !unordered.orderedValid none none)
  let unbalanced := Tree.mkNode
    (Tree.mkNode (Tree.singleton (entry 0 0 1)) (entry 1 2 3) .empty)
    (entry 2 4 5) .empty
  check "cache_not_balance" (unbalanced.cacheOK && !unbalanced.balanced)
  let invalidInterval := Tree.singleton (entry 0 3 2)
  check "cache_not_interval_validity" (invalidInterval.cacheOK &&
    !invalidInterval.orderedValid none none)
  let first := entry 0 (-9) (-7)
  let last := entry 2 (-2) (-1)
  let leftLeft := Tree.mkNode (Tree.mkNode left root .empty) last .empty
  let leftRight := Tree.mkNode (Tree.mkNode .empty first (Tree.singleton root))
    last .empty
  let rightRight := Tree.mkNode .empty first (Tree.mkNode .empty root right)
  let rightLeft := Tree.mkNode .empty first
    (Tree.mkNode (Tree.singleton root) last .empty)
  check "right_rotation" (leftLeft.rotateRight.cacheOK &&
    leftLeft.rotateRight.entries == leftLeft.entries)
  check "left_rotation" (rightRight.rotateLeft.cacheOK &&
    rightRight.rotateLeft.entries == rightRight.entries)
  check "left_right_rotation" (leftRight.rotateLeftRight.cacheOK &&
    leftRight.rotateLeftRight.entries == leftRight.entries)
  check "right_left_rotation" (rightLeft.rotateRightLeft.cacheOK &&
    rightLeft.rotateRightLeft.entries == rightLeft.entries)
  let ll := leftLeft.rebalanceWithCost
  let lr := leftRight.rebalanceWithCost
  let rr := rightRight.rebalanceWithCost
  let rl := rightLeft.rebalanceWithCost
  check "rebalance_left_left" (ll.1 == leftLeft.rotateRight &&
    ll.1.cacheOK && ll.2.rotations == 1 && ll.2.cacheWrites == 2)
  check "rebalance_left_right" (lr.1 == leftRight.rotateLeftRight &&
    lr.1.cacheOK && lr.2.rotations == 2 && lr.2.cacheWrites == 3)
  check "rebalance_right_right" (rr.1 == rightRight.rotateLeft &&
    rr.1.cacheOK && rr.2.rotations == 1 && rr.2.cacheWrites == 2)
  check "rebalance_right_left" (rl.1 == rightLeft.rotateRightLeft &&
    rl.1.cacheOK && rl.2.rotations == 2 && rl.2.cacheWrites == 3)
  check "rebalance_no_rotation" (good.rebalanceWithCost == (good, ({} : Cost)))
  let inserted := [first, root, last].foldl (fun tree item => tree.insertKey item) Tree.empty
  check "insert_cache" (inserted.cacheOK && inserted.entries == [first, root, last])
  let replaced := inserted.insertKey (entry 1 (-6) 4)
  check "replace_cache" (replaced.cacheOK && replaced.cachedMax? == some 4 &&
    replaced.entries.length == 3)
  let erased := good.eraseKey root.key
  check "erase_two_children_cache" (erased.cacheOK && erased.entries == [first, last])
  check "erase_absent_cache" (good.eraseKey (100, 42) == good)
  let emptied := erased.eraseKey first.key |>.eraseKey last.key
  check "erase_to_empty_cache" (emptied == Tree.empty && emptied.cacheOK)
  let firstFalse := (Tree.singleton (entry 0 20 25)).searchWithCost ⟨0, 1⟩
  check "search_first_endpoint_false_cost1" (firstFalse.1 == none &&
    firstFalse.2.endpointComparisons == 1 && firstFalse.2.nodeVisits == 2)
  let secondFalse := (Tree.singleton (entry 0 0 1)).searchWithCost ⟨20, 25⟩
  check "search_second_endpoint_false_cost2" (secondFalse.1 == none &&
    secondFalse.2.endpointComparisons == 2 && secondFalse.2.nodeVisits == 2)
  let bothTrue := (Tree.singleton (entry 0 0 3)).searchWithCost ⟨1, 2⟩
  check "search_both_endpoints_true_cost2" (bothTrue.1 == some (entry 0 0 3) &&
    bothTrue.2.endpointComparisons == 2 && bothTrue.2.nodeVisits == 1)
  let touching := (Tree.singleton (entry 0 0 1)).searchWithCost ⟨1, 2⟩
  check "search_touching_endpoint_cost2" (touching.1 == some (entry 0 0 1) &&
    touching.2.endpointComparisons == 2)
  let negative := (Tree.singleton (entry 0 (-4) (-2))).searchWithCost ⟨-3, -1⟩
  check "search_negative_endpoint_cost2" (negative.1 == some (entry 0 (-4) (-2)) &&
    negative.2.endpointComparisons == 2)
  let pruningTree := Tree.mkNode (Tree.singleton (entry 0 0 1))
    (entry 1 20 25) (Tree.singleton (entry 2 30 35))
  let pruning := pruningTree.searchWithCost ⟨2, 3⟩
  check "search_pruning_adds_one_comparison" (pruning.1 == none &&
    pruning.2.endpointComparisons == 3 && pruning.2.maxCacheReads == 1 &&
    pruning.2.nodeVisits == 3)
  -- Public indexed IndexedIntervalTree API, end to end.
  let pub0 : IndexedIntervalTree := IndexedIntervalTree.empty
  check "public_empty_check" pub0.check
  let pub1 := (pub0.insert (entry 0 0 10)).getD pub0
  let pub2 := (pub1.insert (entry 1 20 30)).getD pub1
  let pub3 := (pub2.insert (entry 2 5 7)).getD pub2
  check "public_insert_check" pub3.check
  check "public_search_hit" ((pub3.search ⟨6, 6⟩).isSome &&
    (pub3.oracleSearch ⟨6, 6⟩).isSome)
  check "public_search_some" ((pub3.search ⟨6, 6⟩).isSome)
  check "public_search_miss" ((pub3.search ⟨40, 50⟩) == none)
  let pub4 := (pub3.insert (entry 1 15 18)).getD pub3
  check "public_replace_changed_low_check" pub4.check
  check "public_replace_finds_new" ((pub4.search ⟨16, 16⟩).map (·.id) == some 1)
  check "public_replace_old_gone" ((pub4.search ⟨25, 25⟩) == none)
  check "public_replace_matches_oracle" ((pub4.search ⟨16, 16⟩).map (·.id) ==
    (pub4.oracleSearch ⟨16, 16⟩).map (·.id))
  let pub5 := pub4.erase 0
  check "public_erase_present_check" (pub5.check && (pub5.search ⟨1, 1⟩) == none)
  let pub6 := pub5.erase 99
  check "public_erase_absent" (pub6.check && pub6.root.entries == pub5.root.entries)
  check "public_invalid_insert_rejected" ((pub3.insert (entry 5 9 2)).isNone)
  check "public_invalid_query_rejected" ((pub3.search ⟨7, 3⟩) == none)

end IntervalMetadataRuntime

#eval IntervalMetadataRuntime.main
