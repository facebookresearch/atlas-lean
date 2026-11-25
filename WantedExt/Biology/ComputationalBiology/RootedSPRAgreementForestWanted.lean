/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rooted subtree prune and regraft distance equals the maximum agreement forest number

A rooted binary phylogenetic `X`-tree has a root of degree two, all other interior vertices of
degree three and leaf set `X`. Bordewich and Semple (2005, Section 2) regard the root as a leaf
`ρ` at the end of a pendant edge adjoined to the original root, with `ρ` in the label set; a
rooted binary phylogenetic `X`-tree is then an unrooted binary phylogenetic tree on `X ∪ {ρ}`.
Here the taxa are any finite type `Y` with a distinguished label `ρ : Y`.

A rooted subtree prune and regraft (rSPR) deletes an edge `{u, v}`, `u` on the path from the
root to `v`, and reattaches the pruned subtree at `v` by a new edge to a new vertex subdividing an
edge of the other component, or above the original root (the paper's operations (i) and (ii)),
followed by forced contractions. On `ρ`-augmented trees both are recorded by what they preserve
(`IsRSPRStep`): the pruned leaf set `A` (with `ρ ∉ A`) is a side of an edge of both trees, the
remaining trees agree, `T|Aᶜ = T'|Aᶜ`, and the pruned subtree keeps its root, `T|(A ∪ {ρ}) =
T'|(A ∪ {ρ})`. (Regrafting above the root is regrafting onto the pendant edge of `ρ`.)

An agreement forest (Bordewich and Semple 2005, Section 2) is a collection `{T_ρ, T₁, …, T_k}`
whose label sets `L_ρ, L₁, …, L_k` partition `X ∪ {ρ}` with `ρ ∈ L_ρ`, with
`Tᵢ ≅ T|Lᵢ ≅ T'|Lᵢ` as rooted trees, and with the subtrees `T(Lᵢ)` vertex-disjoint, and
likewise `T'(Lᵢ)`; `m(T, T')` is the least `k`. Rooted restrictions to `L` are compared by their
rooted triplets, which are the quartets `ab|cρ` with `a, b, c ∈ L \ {ρ}`; a rooted binary tree is
determined by its triplets (`Splits.eq_of_displaysTriplet_iff`, for cluster systems). The
minimal subtree `T(L)` is `spanVerts T L` of `WantedExt.Complexity.NPComplete.TBRDistanceWanted`.

Recorded: Theorem 2.1 (`d_rSPR = m`) and Corollary 2.2 (the rSPR distance decision problem is
NP-complete; NP-hardness is Theorem 1.1). Not recorded: Theorem 1.2 and Section 3 (fixed-parameter
tractability, the subtree and chain reductions and the `28 k` kernel), which need the reduction
operations and a parameterized complexity class.

Sources: M. Bordewich and C. Semple, "On the computational complexity of the rooted subtree prune
and regraft distance", Annals of Combinatorics 8 (2005) 409–423, doi:10.1007/s00026-004-0229-z,
Section 2, Theorems 1.1 and 2.1, Corollary 2.2; J. Hein, T. Jiang, L. Wang and K. Zhang, "On the
complexity of comparing evolutionary trees", Discrete Applied Mathematics 71 (1996) 153–169,
doi:10.1016/S0166-218X(96)00062-5.
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Complexity.NPComplete.TBRDistanceWanted

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.RootedSPRAgreementForestWanted

open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount
open Cslib.Bioinformatics.Phylogenetics.Splits
open MetaMathlibExt.Complexity.NPComplete.TBRDistance

variable {Y : Type} [Fintype Y] [DecidableEq Y]

/-- The rooted restrictions of the `ρ`-augmented trees `T` and `T'` to `L` agree: they display
the same rooted triplets `ab|c`, that is, the same quartets `ab|cρ`, for distinct `a, b, c` in
`L` other than `ρ`. -/
def RootedRestrictionsAgree (ρ : Y) (T T' : UnrootedBinaryTree Y) (L : Finset Y) : Prop :=
  ∀ a ∈ L, ∀ b ∈ L, ∀ c ∈ L, [a, b, c, ρ].Nodup →
    (DisplaysQuartet T a b c ρ ↔ DisplaysQuartet T' a b c ρ)

/-- `T'` is obtained from `T` by one **rooted subtree prune and regraft**: the pruned leaf set
`A`, not containing `ρ`, is a side of an edge of both trees, the remaining trees agree on `Aᶜ`,
and the pruned subtree keeps its rooted shape (agreement on `A ∪ {ρ}`). -/
def IsRSPRStep (ρ : Y) (T T' : UnrootedBinaryTree Y) : Prop :=
  ∃ A : Finset Y, ρ ∉ A ∧ A ∈ edgeSplits T ∧ A ∈ edgeSplits T' ∧
    RootedRestrictionsAgree ρ T T' Aᶜ ∧ RootedRestrictionsAgree ρ T T' (insert ρ A)

/-- `T` is transformed into a tree isomorphic to `T'` by `k` rSPR operations. -/
def RSPRReachIn (ρ : Y) (k : ℕ) (T T' : UnrootedBinaryTree Y) : Prop :=
  ∃ f : Fin (k + 1) → UnrootedBinaryTree Y, f 0 = T ∧ (f (Fin.last k)).Iso T' ∧
    ∀ i : Fin k, IsRSPRStep ρ (f i.castSucc) (f i.succ)

/-- The **rSPR distance** `d_rSPR(T, T')`: the least number of rSPR operations transforming `T`
into `T'`. -/
noncomputable def rsprDist (ρ : Y) (T T' : UnrootedBinaryTree Y) : ℕ :=
  sInf {k | RSPRReachIn ρ k T T'}

/-- The partition `F` of `X ∪ {ρ}` is a **rooted agreement forest** for `T` and `T'`: on each
part the rooted restrictions agree, and for each tree the minimal subtrees spanned by distinct
parts are vertex-disjoint. (The part containing `ρ` is `L_ρ`.) -/
def IsRootedAgreementForest (ρ : Y) (T T' : UnrootedBinaryTree Y)
    (F : Finpartition (Finset.univ : Finset Y)) : Prop :=
  (∀ L ∈ F.parts, RootedRestrictionsAgree ρ T T' L) ∧
  ∀ L ∈ F.parts, ∀ L' ∈ F.parts, L ≠ L' →
    Disjoint (spanVerts T L) (spanVerts T L') ∧ Disjoint (spanVerts T' L) (spanVerts T' L')

/-- The **maximum agreement forest number** `m(T, T')`: the least `k` such that some rooted
agreement forest has `k + 1` parts (`L_ρ, L₁, …, L_k`). -/
noncomputable def rootedMafNumber (ρ : Y) (T T' : UnrootedBinaryTree Y) : ℕ :=
  sInf {k | ∃ F : Finpartition (Finset.univ : Finset Y), IsRootedAgreementForest ρ T T' F ∧
    F.parts.card = k + 1}

/-- **rSPR distance equals the maximum agreement forest number** (Bordewich and Semple 2005,
Theorem 2.1): for rooted binary phylogenetic trees `T` and `T'` on the same taxa, given as
`ρ`-augmented unrooted binary trees, `d_rSPR(T, T') = m(T, T')`.

Source: Bordewich and Semple (2005), Theorem 2.1. -/
public theorem_wanted rsprDist_eq_rootedMafNumber (ρ : Y) (T T' : UnrootedBinaryTree Y) :
    rsprDist ρ T T' = rootedMafNumber ρ T T'

/-- An rSPR distance instance: the number of taxa `m` other than the root, two trees on the
labels `Fin (m + 1)` (the root leaf `ρ` is the label `m`), and the bound `K`. Trees use the
encoding of `TBRDistanceWanted` (`TreeData`, `IsPhyloTree`). -/
abbrev RSPRDistanceInstance := ℕ × TreeData × TreeData × ℕ

/-- Some sequence of at most `K` rSPR operations transforms `T₁` into `T₂`. -/
def RSPRDistanceFeasible (i : RSPRDistanceInstance) : Prop :=
  ∃ (h₁ : IsPhyloTree (i.1 + 1) i.2.1) (h₂ : IsPhyloTree (i.1 + 1) i.2.2.1),
    rsprDist (Fin.last i.1) (toTree h₁) (toTree h₂) ≤ i.2.2.2

open Classical in
/-- rSPR DISTANCE as a decision problem over bitstrings: undecodable bitstrings, and bitstrings
decoding to instances with fewer than two taxa or malformed trees, are no-instances. -/
noncomputable def rsprDistanceDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := RSPRDistanceInstance) x with
  | some i => decide (2 ≤ i.1 ∧ RSPRDistanceFeasible i)
  | none => false

/-- **rSPR DISTANCE is NP-complete** (Bordewich and Semple 2005, Theorem 1.1 and Corollary 2.2,
by the reduction of Hein, Jiang, Wang and Zhang 1996, Theorem 8): the decision problem "is
`d_rSPR(T₁, T₂) ≤ K`?" is in NP and every NP language reduces to it in polynomial time.

Source: Bordewich and Semple (2005), Theorem 1.1 and Corollary 2.2. -/
public theorem_wanted rsprDistance_npComplete :
    rsprDistanceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rsprDistanceDec

end WantedExt.Biology.ComputationalBiology.RootedSPRAgreementForestWanted
