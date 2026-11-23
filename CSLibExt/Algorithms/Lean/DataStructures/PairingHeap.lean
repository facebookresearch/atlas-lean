/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.PairingHeap.Basic
public import CSLibExt.Algorithms.Lean.DataStructures.PairingHeap.PriorityQueue
public import CSLibExt.Algorithms.Lean.DataStructures.PairingHeap.List2
public import CSLibExt.Algorithms.Lean.DataStructures.PairingHeap.Tree
public import CSLibExt.Algorithms.Lean.DataStructures.PairingHeap.List1
public import CSLibExt.Algorithms.Lean.DataStructures.PairingHeap.Amortized

/-!
# Pairing heaps

Pairing heaps (Fredman–Sedgewick–Sleator–Tarjan) are mergeable priority
queues with a simple implementation: `merge` links the two roots and
pushes the loser onto the winner's child list, and `del_min` merges the
child list in two passes. The AFP formalizes three variants, all ported
here with a uniform API: `List2` (the book version, children as a list
of heaps under an `Option` wrapper), `Tree` (the original binary-tree
representation, where heaps *are* binary trees), and `List1` (Okasaki's
list version with direct `merge`). Each variant proves the
`Priority_Queue_Merge` specification in both the locale's and the book's
forms, and `List2` additionally proves Exercise 23.1 (`mergePairs`).
Import the submodules separately when only one API is needed:
`PairingHeap.Basic` (shared two-step list induction),
`PairingHeap.PriorityQueue` (the specification conjunctions),
`PairingHeap.List2` / `PairingHeap.Tree` / `PairingHeap.List1`
(the three variants), `PairingHeap.Amortized` (potential, `ΔΦ` lemmas,
`A_*` bounds, the `Amortized` instantiations, the §23.3 mapping).

Ported from the Chapter 23 Lean conversion in
`converted_proofs/ch23/lean/Chapter23.lean`, itself a conversion of the
Isabelle/HOL sources: the AFP entries `Pairing_Heap`
(`Pairing_Heap_List1.thy`, `Pairing_Heap_List2.thy`,
`Pairing_Heap_Tree.thy`) and `Amortized_Complexity`
(`Pairing_Heap_List2_Analysis.thy`, `Pairing_Heap_Tree_Analysis2.thy`,
`Amortized_Framework.thy`, `Priority_Queue_ops_merge.thy`), and
Tobias Nipkow (ed.), *Functional Data Structures and Algorithms: A Proof
Assistant Approach*, Chapter 23 (Pairing Heaps, pp. 257–264) with
Appendix B.11. Isabelle-derived names are kept for traceability to those
sources.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace PairingHeap


end PairingHeap

end Cslib.Algorithms.Lean
