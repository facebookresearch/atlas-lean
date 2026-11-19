/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree

/-!
# Joinable binary search trees: public API tests

Importing only the facade exposes the generic join framework, the
red–black join, the AVL join, the 2–3-tree join, and the strongly joinable
instances, with their documented types. These tests prevent accidentally
changing a name or a signature.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.JoinableBinarySearchTree.Tests.API

/-- The generic join framework: carrier, specification, derived operations. -/
example (α : Type) (β : Type) : Type _ := Tree α β
example (α : Type) [LinearOrder α] (β : Type) [Inhabited β] : Type _ := JoinData α β
example (J : JoinData Nat Unit) : JoinData Nat Unit := J
example (J : JoinData Nat Unit) : Tree Nat Unit → Option (Nat × Tree Nat Unit) := split_min J
example (J : JoinData Nat Unit) : Tree Nat Unit → Tree Nat Unit → Tree Nat Unit := join2 J
example (J : JoinData Nat Unit) : Nat → Tree Nat Unit → Tree Nat Unit × Bool × Tree Nat Unit := split J
example (J : JoinData Nat Unit) : Nat → Tree Nat Unit → Tree Nat Unit := insert J
example (J : JoinData Nat Unit) : Nat → Tree Nat Unit → Tree Nat Unit := delete J
example (J : JoinData Nat Unit) : Tree Nat Unit → Tree Nat Unit → Tree Nat Unit := union J
example (J : JoinData Nat Unit) : Tree Nat Unit → Tree Nat Unit → Tree Nat Unit := inter J
example (J : JoinData Nat Unit) : Tree Nat Unit → Tree Nat Unit → Tree Nat Unit := diff J
example (J : JoinData Nat Unit) : Tree Nat Unit → Tree Nat Unit → Tree Nat Unit := diff1 J
example (J : JoinData Nat Unit) : Nat → Tree Nat Unit → Tree Nat Unit := insert' J
example (J : JoinData Nat Unit) : Nat → Tree Nat Unit → Tree Nat Unit := delete' J

/-- The red–black join (Figure 10.4). -/
example : Type := Color
example : Tree Nat Color → Color := col
example : Tree Nat Color → Nat := bheight
example : Tree Nat Color → Prop := invc
example : Tree Nat Color → Prop := invc2
example : Tree Nat Color → Prop := invh
example : Tree Nat Color → Nat → Tree Nat Color → Tree Nat Color := RNode
example : Tree Nat Color → Nat → Tree Nat Color → Tree Nat Color := BNode
example : Tree Nat Color → Nat → Tree Nat Color → Tree Nat Color := baliL
example : Tree Nat Color → Nat → Tree Nat Color → Tree Nat Color := baliR
example : Color → Tree Nat Color → Tree Nat Color := paint
example : Tree Nat Color → Nat → Tree Nat Color → Tree Nat Color := joinL
example : Tree Nat Color → Nat → Tree Nat Color → Tree Nat Color := joinR
example : Tree Nat Color → Nat → Tree Nat Color → Tree Nat Color := rbtJoin
example : JoinData Nat Color := rbtJoinData
example : Tree Nat Color → Tree Nat Color → Tree Nat Color := rbtUnion
example : Tree Nat Color → Tree Nat Color → Tree Nat Color := rbtInter
example : Tree Nat Color → Tree Nat Color → Tree Nat Color := rbtDiff
example : Nat → Tree Nat Color → Tree Nat Color := rbtInsert
example : Nat → Tree Nat Color → Tree Nat Color := rbtDelete
example : Tree Nat Color → List Nat := inorder
example : Tree Nat Color → Nat := tsize

/-- The AVL join. -/
example : Tree Nat Nat → Nat := ht
example : Tree Nat Nat → Nat := height
example : Tree Nat Nat → Nat → Tree Nat Nat → Tree Nat Nat := node
example : Tree Nat Nat → Prop := avl
example : Tree Nat Nat → Nat → Tree Nat Nat → Tree Nat Nat := balL
example : Tree Nat Nat → Nat → Tree Nat Nat → Tree Nat Nat := balR
example : Tree Nat Nat → Nat → Tree Nat Nat → Tree Nat Nat := avlJoinR
example : Tree Nat Nat → Nat → Tree Nat Nat → Tree Nat Nat := avlJoinL
example : Tree Nat Nat → Nat → Tree Nat Nat → Tree Nat Nat := avlJoin
example : JoinData Nat Nat := avlJoinData
example : Tree Nat Nat → Tree Nat Nat → Tree Nat Nat := avlUnion
example : Tree Nat Nat → Tree Nat Nat → Tree Nat Nat := avlInter
example : Tree Nat Nat → Tree Nat Nat → Tree Nat Nat := avlDiff
example : Nat → Tree Nat Nat → Tree Nat Nat := avlInsert
example : Nat → Tree Nat Nat → Tree Nat Nat := avlDelete

/-- The 2–3-tree join (Exercise 10.3). -/
example : Type := Tree23 Nat
example : Tree23 Nat → Nat := height23
example : Tree23 Nat → Prop := complete23
example : Tree23 Nat → List Nat := inorder23
example : Type := Upi23 Nat
example : Upi23 Nat → Tree23 Nat := treei
example : Upi23 Nat → Nat := hi23
example : Tree23 Nat → Nat → Tree23 Nat → Upi23 Nat := joinL23
example : Tree23 Nat → Nat → Tree23 Nat → Upi23 Nat := joinR23
example : Tree23 Nat → Nat → Tree23 Nat → Tree23 Nat := join23

/-- The strongly joinable framework and its instances. -/
example : (Tree Nat Unit → ℝ) → ℝ → ℝ → Tree Nat Unit → Prop := balancedOf
example (α : Type) [LinearOrder α] (β : Type) [Inhabited β] : Type _ := StronglyJoinableData α β
example : Tree Nat (Color × Nat) → Color := scol
example : Tree Nat (Color × Nat) → Nat := sbh
example : Tree Nat (Color × Nat) → Nat → Tree Nat (Color × Nat) → Tree Nat (Color × Nat) := sR
example : Tree Nat (Color × Nat) → Nat → Tree Nat (Color × Nat) → Tree Nat (Color × Nat) := sB
example : Tree Nat (Color × Nat) → Prop := sinvc
example : Tree Nat (Color × Nat) → Prop := sinvc2
example : Tree Nat (Color × Nat) → Prop := sinvh
example : Tree Nat (Color × Nat) → Prop := srbt
example : Tree Nat (Color × Nat) → Nat → Tree Nat (Color × Nat) → Tree Nat (Color × Nat) := sbaliL
example : Tree Nat (Color × Nat) → Nat → Tree Nat (Color × Nat) → Tree Nat (Color × Nat) := sbaliR
example : Tree Nat (Color × Nat) → Nat → Tree Nat (Color × Nat) → Tree Nat (Color × Nat) := sjoinL
example : Tree Nat (Color × Nat) → Nat → Tree Nat (Color × Nat) → Tree Nat (Color × Nat) := sjoinR
example : Tree Nat (Color × Nat) → Tree Nat (Color × Nat) := sblacken
example : Tree Nat (Color × Nat) → Nat → Tree Nat (Color × Nat) → Tree Nat (Color × Nat) := sjoin
example : JoinData Nat (Color × Nat) := sjoinData
example : Tree Nat (Color × Nat) → Nat := srk
example : Tree Nat (Color × Nat) → Nat → Tree Nat (Color × Nat) → Nat := TsjoinL
example : Tree Nat (Color × Nat) → Nat → Tree Nat (Color × Nat) → Nat := TsjoinR
example : Tree Nat (Color × Nat) → Nat → Tree Nat (Color × Nat) → Nat := Tsjoin
example : StronglyJoinableData Nat (Color × Nat) := sStronglyJoinable
example : Tree Nat Nat → Nat → Tree Nat Nat → Nat := TavlJoinR
example : Tree Nat Nat → Nat → Tree Nat Nat → Nat := TavlJoinL
example : Tree Nat Nat → Nat → Tree Nat Nat → Nat := TavlJoin
example : StronglyJoinableData Nat Nat := avlStronglyJoinable

end Cslib.Algorithms.Lean.JoinableBinarySearchTree.Tests.API
