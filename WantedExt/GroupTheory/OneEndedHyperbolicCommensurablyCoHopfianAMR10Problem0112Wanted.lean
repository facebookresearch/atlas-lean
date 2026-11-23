/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite-index subgroups isomorphic to infinite-index subgroups (Bestvina, Q 1.12)

M. Bestvina, Questions in Geometric Group Theory, Q 1.12 (Whyte): let `Γ` be a one-ended hyperbolic
group. Can a finite index subgroup of `Γ` be isomorphic to a subgroup of `Γ` of infinite index?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Ends.Defs
public import Mathlib.GroupTheory.Index
public import MathlibExt.GroupTheory.HyperbolicGroup

@[expose] public section

namespace MathlibExt.GroupTheory.OneEndedHyperbolicCommensurablyCoHopfianAMR10Problem0112Wanted

/-!
Source: M. Bestvina, Questions in Geometric Group Theory (updated July 2004), Q 1.12 (Whyte),
https://www.math.utah.edu/~bestvina/eprints/questions-updated.pdf. UnsolvedMath record UM-01100112
(`AMR-010-0112`), dataset ulamai/UnsolvedMath v1.8.0.

Hyperbolic is `Group.IsHyperbolic` (MathlibExt: some finite generating set has a Gromov-hyperbolic
word metric). One-ended means that for some finite generating set `S` the Cayley graph
`SimpleGraph.mulCayley S` has exactly one end in the sense of Mathlib's `SimpleGraph.end` (the
number of ends does not depend on `S`); finite groups have no end and two-ended groups two, so both
are excluded. Infinite index is `K.index = 0`.
-/

/-- `Γ` is one-ended: for some finite generating set `S`, the Cayley graph `SimpleGraph.mulCayley S`
has exactly one end (Mathlib's `SimpleGraph.end`: the compatible choices of a connected component
of the complement of every finite set of vertices). -/
def IsOneEnded (Γ : Type*) [Group Γ] : Prop :=
  ∃ S : Finset Γ, Subgroup.closure (S : Set Γ) = ⊤ ∧
    (SimpleGraph.mulCayley (S : Set Γ)).end.ncard = 1

/-- Whyte's question (Bestvina Q 1.12), answered: some one-ended word-hyperbolic group has a
finite-index subgroup isomorphic to a subgroup of infinite index. -/
def oneEndedHyperbolicFiniteIndexIsoInfiniteIndex : Prop :=
  ∃ (Γ : Type) (_ : Group Γ), Group.IsHyperbolic Γ ∧ IsOneEnded Γ ∧
    ∃ H K : Subgroup Γ, H.FiniteIndex ∧ K.index = 0 ∧ Nonempty (H ≃* K)

/--
Resolved true: Stark and Woodhouse proved that there are one-ended hyperbolic groups that are not
commensurably coHopfian, i.e. with a finite-index subgroup isomorphic to an infinite-index subgroup
(for example fundamental groups of simple surface amalgams). Source: M. Bestvina, Questions in
Geometric Group Theory (updated July 2004), Q 1.12 (Whyte),
https://www.math.utah.edu/~bestvina/eprints/questions-updated.pdf; resolution: E. Stark and D. J.
Woodhouse, Hyperbolic groups that are not commensurably coHopfian, Int. Math. Res. Not. IMRN,
arXiv:1812.07799, Theorem 1.1: "There exist one-ended hyperbolic groups that are not commensurably
coHopfian", where Γ is commensurably coHopfian if no finite-index subgroup of Γ is isomorphic to an
infinite-index subgroup; stated as answering Whyte's Q 1.12 on Bestvina's list,
https://arxiv.org/abs/1812.07799.
-/
public theorem_wanted oneEndedHyperbolicFiniteIndexIsoInfiniteIndex_holds :
    oneEndedHyperbolicFiniteIndexIsoInfiniteIndex

end MathlibExt.GroupTheory.OneEndedHyperbolicCommensurablyCoHopfianAMR10Problem0112Wanted
