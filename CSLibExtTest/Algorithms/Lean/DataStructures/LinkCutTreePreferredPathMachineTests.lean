/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree.PreferredPathMachine
meta import CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree.PreferredPathMachine

/-!
# Tests for the costed link-cut pointer machine

Probe actual records (ordinary and dashed parents share one field), rotation pairing, exact
charges, independent legality, and noncommutative root-to-vertex edge products.
-/

namespace Cslib.Algorithms.Lean.LinkCutTree.SplayForestTests

open SplayForest

private def cell (l r u : Option Nat) : Cell Nat := ⟨l, r, u, 1, 1⟩

-- The preferred path 0,1,2,3 is one left-leaning auxiliary tree with root 3.
private def chain : Heap Nat := ⟨#[cell none none (some 1), cell (some 0) none (some 2),
  cell (some 1) none (some 3), cell (some 2) none none], 0⟩

-- Access at 3 costs three blocks with no rotations. Find-root also pays for the operation,
-- four left-walk visits and the final three-rotation splay (bottom zig-zig, then top zig).
example : step chain (.findRoot 3) = some (⟨#[cell none (some 3) none, cell none (some 2) (some 3),
    cell none none (some 1), cell (some 1) none (some 0)], 12⟩, .vertex 0) := by decide

-- The second auxiliary tree has inorder [3,4], root 4, and a dashed pointer to 0, the
-- represented parent of 3, NOT of 4. Off the accessed path the solid edge 1→2 must survive.
private def fork : Heap Nat := ⟨#[cell none (some 1) none, cell none (some 2) (some 0),
  cell none none (some 1), cell none none (some 4), cell (some 3) none (some 0)], 0⟩

example : fork.expose 4 = some ⟨#[cell none (some 3) (some 4), cell none (some 2) (some 0),
    cell none none (some 1), cell none none (some 0), cell (some 0) none none], 6⟩ := by decide

-- Zig-zag under a dashed pointer: 3 has left child 1, whose right child is 2. The new root
-- must inherit the path-parent pointer to 0, without installing 2 as an ordinary child of 0.
private def bent : Heap Nat := ⟨#[cell none none none, cell none (some 2) (some 3),
  cell none none (some 1), cell (some 1) none (some 0)], 0⟩

example : bent.splay 2 = some ⟨#[cell none none none, cell none none (some 2),
    cell (some 1) (some 3) (some 0), cell none none (some 2)], 3⟩ := by decide

-- Illegal represented histories fail even though the pointer machine is for prevalidated calls.
private def legal (ops : List (Call Nat)) : Bool := (replay specStep {} ops).isSome

#guard !legal [.makeTree, .cut 0]
#guard !legal [.makeTree, .findRoot 1]
#guard !legal [.makeTree, .makeTree, .link 1 0 7, .link 0 1 9]
#guard !legal [.makeTree, .makeTree, .makeTree, .link 1 0 7, .link 1 2 9]
#guard legal [.makeTree, .makeTree, .link 1 0 7, .cut 1, .link 0 1 9]

-- Boolean endomorphisms form a fixed-size noncommutative monoid. Probe on both inputs.
private structure Bits where
  run : Bool → Bool

private instance : Monoid Bits where
  one := ⟨id⟩
  mul a b := ⟨a.run ∘ b.run⟩
  one_mul := by intro a; rfl
  mul_one := by intro a; rfl
  mul_assoc := by intros; rfl

-- At descendant 2 the lower edge acts by negation. Its root-path product is constant false
-- with the old upper edge, negation after the cut, and constant true under the new root 3.
-- Reversing the factors in that last query would instead return constant false.
private def history : List (Call Bits) := [
  .makeTree, .makeTree, .makeTree, .link 1 0 ⟨fun _ => false⟩, .link 2 1 ⟨Bool.not⟩,
  .pathAggregate 2, .findRoot 2, .cut 1, .pathAggregate 2, .findRoot 2, .pathAggregate 1,
  .makeTree, .link 1 3 ⟨fun _ => true⟩, .findRoot 2, .pathAggregate 2]

private def observe : Answer Bits → Nat × Nat
  | .vertex v => (2, v)
  | .done => (3, 0)
  | .aggregate a => ((a.run false).toNat, (a.run true).toNat)

private def answers := [(2, 0), (2, 1), (2, 2), (3, 0), (3, 0), (0, 0), (2, 0),
  (3, 0), (1, 0), (2, 1), (0, 1), (2, 3), (3, 0), (2, 3), (1, 1)]

#guard (replay specStep {} history).map (fun (_, out) => out.map observe) == some answers

example : (replay step {} history).map (fun (_, out) => out.map observe) = some answers :=
  by decide

end Cslib.Algorithms.Lean.LinkCutTree.SplayForestTests
