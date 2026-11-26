/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Algorithms.Lean.DataStructures.KdTree.Planar
public import Mathlib.Data.Nat.Sqrt

/-!
# Planar kd-tree range reporting

P. K. Agarwal, *Orthogonal Range Searching*, CPS234 Lecture 8, Duke University,
22 September 2005 (scribe: Mason F. Matthews), §§8.3.1–8.3.3, pp. 8-3–8-5.
The leaf-oriented variant, rank encoding and work model are specified in
`CSLibExt.Algorithms.Lean.DataStructures.KdTree.Planar`.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.KdTree.Planar

/-- **Orthogonal range reporting in a kd-tree.** Over any linearly ordered coordinate type,
let $P$ have $n$ points with distinct x coordinates and distinct y coordinates. Preprocessing
once produces a valid alternating median-split rank tree rooted at the x axis. There is a
uniform constant $C>0$ bounding the stored tree constructors plus dictionary entries by
$C(n+1)$ and preprocessing work by $C(n+1)(1+\lceil\log_2 n\rceil)$. For any two corners,
the report is a permutation of the input filtered by the four closed inequalities, and query
work is at most $C(1+\lfloor\sqrt n\rfloor+k)$, where $k$ is its actual output length.
The logarithm convention at zero is zero. Each coordinate comparison, rank operation and
indexed lookup costs constant time. The same dictionaries are reused for every query. -/
theorem_wanted orthogonalRangeReporting :
    ∃ C : Nat, 0 < C ∧ ∀ (α : Type) [LinearOrder α] (pts : List (α × α)),
      (pts.map Prod.fst).Nodup → (pts.map Prod.snd).Nodup →
      let n := pts.length
      let (idx, buildWork) := preprocess pts
      idx.tree.Valid ∧ MedianShape 0 n idx.tree ∧
        idx.tree.storedNodes + idx.byX.size + idx.byY.size ≤ C * (n + 1) ∧
        buildWork ≤ C * (n + 1) * (1 + Nat.clog 2 n) ∧
        ∀ lo hi : α × α,
          let (out, queryWork) := idx.query lo hi
          out.Perm (pts.filter (fun p => lo.1 ≤ p.1 ∧ p.1 ≤ hi.1 ∧ lo.2 ≤ p.2 ∧ p.2 ≤ hi.2)) ∧
            queryWork ≤ C * (1 + n.sqrt + out.length)

end Cslib.Algorithms.Lean.KdTree.Planar
