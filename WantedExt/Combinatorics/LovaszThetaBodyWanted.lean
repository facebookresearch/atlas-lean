/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.LovaszThetaBodySup

/-!
# Perfection and stable set polytopes (wanted)

A finite graph is perfect exactly when its stable set polytope equals its clique-constrained
polytope.

Source: D. E. Knuth, "The Sandwich Theorem", Electron. J. Combin. 1 (1994), #A1
(arXiv:math/9312214v1), Theorem 32.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.LovaszThetaBodyWanted

open MathlibExt.Combinatorics.SimpleGraph.LovaszTheta

/-- **Perfect graphs are those with STAB = QSTAB.** A finite graph `G` is perfect if and only if
`STAB(G) = QSTAB(G)` (Knuth, *The Sandwich Theorem*, 1994, Theorem 32; the direction "perfect
implies equal" is his Theorem 31). -/
theorem_wanted isPerfect_iff_stab_eq_qstab {V : Type*} [Fintype V] (G : SimpleGraph V) :
    MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted.IsPerfect G ↔ stab G = qstab G

end MathlibExt.Combinatorics.SimpleGraph.LovaszThetaBodyWanted
