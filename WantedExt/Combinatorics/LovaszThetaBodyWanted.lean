/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.LovaszThetaBody

/-!
# The theta body: theta as a linear maximum, and perfection (wanted)

Two theorems of Grötschel, Lovász and Schrijver's theory of the theta body, in Knuth's account:
the Lovász number is the maximum of `∑_v x_v` over `TH(G)`, and a graph is perfect exactly when its
stable set polytope equals its clique-constrained polytope.

Source: D. E. Knuth, "The Sandwich Theorem", Electron. J. Combin. 1 (1994), #A1
(arXiv:math/9312214v1), eq. (5.1) and Theorem 32.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.LovaszThetaBodyWanted

open MathlibExt.Combinatorics.SimpleGraph.LovaszTheta

/-- **Theta is the maximum of the coordinate sum over the theta body.** For a finite graph `G`,
`ϑ(G) = sup {∑_v x_v : x ∈ TH(G)}` (Knuth, *The Sandwich Theorem*, 1994, eq. (5.1) with unit
weights: `ϑ = ϑ₁`, the theorem of Grötschel, Lovász and Schrijver that Knuth proves in §§5-12).
Knuth measures costs against the first coordinate vector, here any handle is allowed; an
orthogonal change of coordinates (Knuth, Lemma 0) shows that both choices give the same `TH(G)`
and the same `ϑ(G)`. -/
theorem_wanted lovaszTheta_eq_sSup_th {V : Type*} [Fintype V] (G : SimpleGraph V) :
    lovaszTheta G = sSup ((fun x : V → ℝ => ∑ v, x v) '' th G)

/-- **Perfect graphs are those with STAB = QSTAB.** A finite graph `G` is perfect if and only if
`STAB(G) = QSTAB(G)` (Knuth, *The Sandwich Theorem*, 1994, Theorem 32; the direction "perfect
implies equal" is his Theorem 31). -/
theorem_wanted isPerfect_iff_stab_eq_qstab {V : Type*} [Fintype V] (G : SimpleGraph V) :
    MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted.IsPerfect G ↔ stab G = qstab G

end MathlibExt.Combinatorics.SimpleGraph.LovaszThetaBodyWanted
