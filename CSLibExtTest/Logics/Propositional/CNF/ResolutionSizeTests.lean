/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Propositional.CNF.ResolutionSize

namespace Cslib.Logic.LegacyPL.CNF.ResolutionSizeTests

open Cslib.Logic.LegacyPL.CNF

/-- The two-variable refutation has seven nodes and occurrence width two. -/
example : exTwoVarDerivation.size = 7 ∧ exTwoVarDerivation.width = 2 :=
  ⟨exTwoVar_size, exTwoVar_width⟩

/-- The exhibited DAG refutation has fewer entries than its exhibited
tree unfolding (other refutations of the same formula are smaller still). -/
example : exDagList.length < exTreeDerivation.size := by
  rw [exDag_size, exTree_size]; decide

/-- The forward tree bridge applies to the two-variable refutation. -/
example : exTwoVar.ResolutionDerivable [] :=
  TreeDerivation.toDerivable exTwoVarDerivation

/-- The reverse bridge returns a tree derivation. -/
example : Nonempty (TreeDerivation exTwoVar []) :=
  TreeDerivation.ofDerivable (TreeDerivation.toDerivable exTwoVarDerivation)

/-- The DAG bridge applies to the empty clause of the sharing example. -/
example : Nonempty (TreeDerivation exDagFormula []) :=
  DAGDerivation.exists_tree exDag_valid (by decide)

/-- Occurrence width counts duplicate literals: this resolvent has length
four with only two distinct literals. -/
def wideDerivation : TreeDerivation
    [[(0, true), (2, true), (1, true)], [(0, true), (2, true), (1, false)]]
    [(0, true), (2, true), (0, true), (2, true)] :=
  .resolve (C := [(0, true), (2, true), (1, true)])
    (D := [(0, true), (2, true), (1, false)]) 1
    (.ax (by decide)) (.ax (by decide)) (by decide) (by decide)

/-- Its occurrence width is `4` (a set-based count would give `3`,
from the input clauses). -/
example : wideDerivation.width = 4 := by rfl

/-- A regrouped tree refutation of the sharing formula with `9` nodes:
resolve the two `(0, false)` partners first, then the shared clause. -/
def regroupedTree : TreeDerivation exDagFormula [] :=
  .resolve (C := [(0, true), (0, true)]) (D := [(0, false), (0, false)]) 0
    (.resolve (C := [(0, true), (1, true)]) (D := [(0, true), (1, false)]) 1
      (.ax (by decide)) (.ax (by decide)) (by decide) (by decide))
    (.resolve (C := [(0, false), (3, true)]) (D := [(0, false), (3, false)]) 3
      (.ax (by decide))
      (.resolve (C := [(0, false), (4, true)]) (D := [(3, false), (4, false)]) 4
        (.ax (by decide)) (.ax (by decide)) (by decide) (by decide))
      (by decide) (by decide))
    (by decide) (by decide)

/-- Its size is `9`, below both exhibited proofs: the comparison in the
module is about the two exhibited proofs, not about optima. -/
example : regroupedTree.size = 9 := by rfl

/-- The empty clause occurs in the DAG example. -/
example : [] ∈ exDagList := by decide

/-- The tree-to-DAG simulation applies to the exhibited tree. -/
example : ∃ l, DAGDerivation exDagFormula l ∧ [] ∈ l ∧
    l.length ≤ exTreeDerivation.size :=
  TreeDerivation.exists_dag exTreeDerivation

end Cslib.Logic.LegacyPL.CNF.ResolutionSizeTests
