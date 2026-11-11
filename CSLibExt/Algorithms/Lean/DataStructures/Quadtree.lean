/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.Quadtree.Boolean
public import CSLibExt.Algorithms.Lean.DataStructures.Quadtree.OfFunction

/-!
# Region quadtrees

The shared `Cslib.Algorithms.Lean.QTree` carrier supports Boolean region
operations in `QTree.Boolean` and polymorphic function reconstruction in
`QTree`. Import the submodules separately when only one API is needed.

The two source tasks are `auto-fdsa-13-01/solution/Solution.lean` and
`auto-fdsa-13-02/solution/Solution.lean` in `codimango/sw-verification-zhih`
at commit
`16412d086eb5af2e74da78731bde50da0667bc79`. Their graded theorem names survive
as `QTree.Boolean.fdsa_chap13_ex01` and `QTree.fdsa_chap13_ex02`.

The lookup functions are deliberately distinct: `QTree.Boolean.get` returns
`false` on a branch at scale zero, whereas `QTree.get` descends its first
child at `(0, 0)`. See each submodule for the exact correctness scope.
-/
