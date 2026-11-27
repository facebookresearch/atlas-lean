/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Basic
public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Splice
public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Array
public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.FlexibleArray
public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.OfList
public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.ToList
public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Size
public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Balance

/-!
# Braun trees and arrays via Braun trees

The Chapter 11 development of *Functional Data Structures and
Algorithms*: Braun trees, the array and flexible-array ADTs built on
them, linear-time conversions between lists and Braun trees, and the
running-time bounds for the book's sketches. Import the submodules
separately when only one API is needed.

Module map:

* `BraunTree.Basic` — the `Tree` carrier, `size` / `height` /
  `minHeight`, `braun` / `acomplete` / `complete`, and the height /
  size / logarithm bounds.
* `BraunTree.Splice` — list interleaving (`splice`) and its cost.
* `BraunTree.Array` — the array implementation on Braun trees
  (`list`, `lookup1`, `update1`, `adds`, `ofList`), the `Array` ADT,
  tries (Exercise 11.5), the Braun-indices characterisation, and the
  §11.3.2 running-time bounds.
* `BraunTree.FlexibleArray` — `del_hi` / `add_lo` / `merge` /
  `del_lo`, the flexible-array operations, `del_lo2` (Exercise 11.6),
  and the §11.4 running-time bounds.
* `BraunTree.OfList` — `take_nths`, `braun_list`, `nodes`, `brauns`
  (Theorem 11.5, Corollary 11.6), and Lemma 11.7.
* `BraunTree.ToList` — `list_fast_rec` / `list_fast` (Theorem 11.8)
  and `Tlist_fast_rec` (Theorem 11.9).
* `BraunTree.Size` — `diff` / `size_fast` (Lemma 11.3), `braun_of`,
  `braun_of_naive` (Exercise 11.7), and Exercise 11.8.
* `BraunTree.Balance` — `bal` (Exercise 11.4, Corollary 4.12) and
  its linear running time (Exercise 4.9).

The Ω(n lg n) lower bound for `array` (§7.3's Θ(n lg n) claim) is
not formalised; only the O(n lg n) upper bound (`Tadds_le_array`)
is proved. The `T*` counters measure calls of their respective
functions, not total runtime; see each module for its cost model.

## Provenance

A Lean formalisation of the Chapter 11 Isabelle development in the
Isabelle distribution's `HOL-Data_Structures` theories
(`Braun_Tree.thy`, `Array_Braun.thy`, `Array_Specs.thy`,
`Balance.thy`). The book is Tobias Nipkow (ed.), *Functional Data
Structures and Algorithms* (ACM Books, 2025; text version of July 27,
2026), Chapter 11 (Arrays via Braun Trees) and Chapter 4.
-/
