/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Identifiability of the general Markov model on trees

Chang (1996, Section 2): an evolutionary tree has no node of degree two, and its terminal nodes
(degree one) are the taxa. The states `X_s` at the nodes form a Markov random field on the tree,
with node marginals `π^s(i) = P{X_s = i}` and, for each edge `{r, s}`, the two edge transition
matrices `P^{rs}(i, j) = P{X_s = j | X_r = i}` and `P^{sr}`. Such a field is recorded here through
its root factorization: for a node `m`, a probability vector at `m` and Markov matrices on the
edges directed away from `m` (`IsTreeMarkovField`, built on `treeJoint` of
`GeneralMarkovFlatteningWanted`); every such product is a Markov random field on the tree, and
its transition matrices are computed from its pair marginals (`transition`).

A class `𝓜` of matrices is *reconstructible from rows* if for each `M ∈ 𝓜` and each permutation
matrix `R ≠ I`, `RM ∉ 𝓜` (Section 4); for example the matrices that are diagonal largest in
column. Theorem 4.1: if the tree has no node of degree two, some node `m` has `π^m(i) > 0` for
all states `i`, and every edge transition matrix is invertible, is not a permutation matrix and
lies in a class reconstructible from rows, then the topology and all of the transition matrices
are uniquely determined by the joint distribution of the states at the terminal nodes. The
hypothesis "for each edge `{r, s}`" is read for both orientations `P^{rs}` and `P^{sr}`, since the
edge `{r, s} = {s, r}` is unordered. Topologies are equal when they agree up to relabelling of the
nonterminal nodes, that is, a graph isomorphism fixing the terminal labels.

Not recorded here: Theorem 5.1 (consistency of maximum likelihood under strong reconstructibility
from rows), which needs a framework of maximum-likelihood estimators over a parameter class.

Trees use the carrier `UnrootedPhyloTree` of `NoCommonMechanismParsimonyWanted` (degree at least
three at every unlabelled vertex, the taxa labelling the leaves bijectively). The pair-law
identifiability of the narrower general time-reversible model is a separate development in
`Domains.Biology.Phylogenetics`.

Sources: J. T. Chang, "Full reconstruction of Markov models on evolutionary trees:
identifiability and consistency", Mathematical Biosciences 137 (1996) 51–73,
doi:10.1016/S0025-5564(96)00075-2, Section 2, the definition of reconstructibility from rows,
Theorem 4.1.
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Biology.ComputationalBiology.GeneralMarkovFlatteningWanted
public import WantedExt.Biology.ComputationalBiology.NoCommonMechanismParsimonyWanted
public import Mathlib.LinearAlgebra.Matrix.Permutation

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.GeneralMarkovIdentifiabilityWanted

open WantedExt.Biology.ComputationalBiology.GeneralMarkovFlatteningWanted
open WantedExt.Biology.ComputationalBiology.NoCommonMechanismParsimonyWanted

variable {X K : Type} [Fintype K] [DecidableEq K]

/-- `μ`, a distribution of the states at all nodes of `T`, is a **Markov random field on the
tree** in root form: for some node `m`, a probability vector at `m` and Markov matrices on the
edges directed away from `m` multiply to `μ`. -/
def IsTreeMarkovField (T : UnrootedPhyloTree X) (μ : (T.V → K) → ℝ) : Prop :=
  ∃ (m : T.V) (π : K → ℝ) (M : T.V → T.V → Matrix K K ℝ),
    IsStochastic T.G m π M ∧ μ = treeJoint T.G m π M

open Classical in
/-- The marginal `π^s(i) = P{X_s = i}`. -/
noncomputable def marginal {V : Type} [Fintype V] (μ : (V → K) → ℝ) (s : V) (i : K) : ℝ :=
  ∑ σ ∈ Finset.univ.filter (fun σ : V → K => σ s = i), μ σ

open Classical in
/-- The edge transition matrix `P^{rs}(i, j) = P{X_s = j | X_r = i}`. -/
noncomputable def transition {V : Type} [Fintype V] (μ : (V → K) → ℝ) (r s : V) :
    Matrix K K ℝ :=
  fun i j => (∑ σ ∈ Finset.univ.filter (fun σ : V → K => σ r = i ∧ σ s = j), μ σ) /
    marginal μ r i

open Classical in
/-- The joint distribution of the states at the terminal nodes: the probability that the leaf of
each taxon `x` has state `u x`. -/
noncomputable def terminalDist (T : UnrootedPhyloTree X) (μ : (T.V → K) → ℝ) (u : X → K) : ℝ :=
  ∑ σ ∈ Finset.univ.filter (fun σ : T.V → K => ∀ x, σ (T.label x) = u x), μ σ

/-- A class of matrices is **reconstructible from rows**: no nontrivial row permutation of a
member is a member. -/
def ReconstructibleFromRows (𝓜 : Set (Matrix K K ℝ)) : Prop :=
  ∀ M ∈ 𝓜, ∀ R : Equiv.Perm K, R ≠ 1 → M.submatrix R id ∉ 𝓜

/-- The hypotheses of Theorem 4.1 for the field `μ` on `T` and the class `𝓜`: some node has a
positive marginal, and every edge transition matrix, in both orientations, is invertible, is not
a permutation matrix and lies in `𝓜`. -/
def SatisfiesChangConditions (T : UnrootedPhyloTree X) (μ : (T.V → K) → ℝ)
    (𝓜 : Set (Matrix K K ℝ)) : Prop :=
  (∃ m, ∀ i, 0 < marginal μ m i) ∧
    ∀ r s, T.G.Adj r s → IsUnit (transition μ r s).det ∧
      (∀ R : Equiv.Perm K, transition μ r s ≠ R.permMatrix ℝ) ∧ transition μ r s ∈ 𝓜

/-- **Full identifiability of the general Markov model** (Chang 1996, Theorem 4.1): let `𝓜` be a
class of matrices reconstructible from rows, and let `μ` on `T` and `μ'` on `T'` be Markov random
fields on trees without nodes of degree two, with the same taxa, both satisfying the conditions
of the theorem for `𝓜`. If they give the same joint distribution of the states at the terminal
nodes, then the topologies agree up to relabelling of the nonterminal nodes (a graph isomorphism
fixing the terminal labels) and this isomorphism carries every edge transition matrix of `μ` to
the corresponding one of `μ'`.

Source: Chang (1996), Theorem 4.1. -/
public theorem_wanted identifiable_of_reconstructibleFromRows (𝓜 : Set (Matrix K K ℝ))
    (h𝓜 : ReconstructibleFromRows 𝓜) (T T' : UnrootedPhyloTree X)
    (μ : (T.V → K) → ℝ) (μ' : (T'.V → K) → ℝ)
    (hμ : IsTreeMarkovField T μ) (hμ' : IsTreeMarkovField T' μ')
    (hc : SatisfiesChangConditions T μ 𝓜) (hc' : SatisfiesChangConditions T' μ' 𝓜)
    (heq : terminalDist T μ = terminalDist T' μ') :
    ∃ e : T.G ≃g T'.G, (∀ x, e (T.label x) = T'.label x) ∧
      ∀ r s, T.G.Adj r s → transition μ r s = transition μ' (e r) (e s)

end WantedExt.Biology.ComputationalBiology.GeneralMarkovIdentifiabilityWanted
