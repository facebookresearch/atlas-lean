/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Maximum likelihood under no common mechanism equals maximum parsimony

A phylogenetic tree (Tuffley and Steel 1997, Definition 1) is a tree with no vertex of degree two
whose leaves (degree one) carry distinct labels from the taxon set `X`, every leaf labelled; for
a rooted tree the root, and only the root, may have degree two, and it may be a leaf. An `r`-state
character is a map `χ : X → S` with `|S| = r ≥ 2`; an extension `χ̂` is a state at every vertex
agreeing with `χ` at the leaves; its changing number `ch(χ̂)` counts the edges whose endpoints get
different states, and the length `l(χ, T)` is the least changing number of an extension
(Definition 2).

In the fully symmetric model (p.584) the root state is uniform, a net change across an edge `e`
has probability `p_e`, with each of the other `r - 1` states then equally likely, changes on
different edges are independent, and `0 ≤ p_e ≤ (r - 1) / r` (the endpoints are included for
compactness, p.586). So (equations (2), (3))
`P[χ̂ | T, p] = (1 / r) ∏_{e unchanged} (1 - p_e) ∏_{e changed} p_e / (r - 1)` and
`P[χ | T, p] = ∑_{χ̂ extends χ} P[χ̂ | T, p]`. The value does not depend on the root (stationarity
and reversibility, p.586), so the same formula serves unrooted and rooted trees. Under *no common
mechanism* each character has its own parameter vector over the whole box, and characters are
independent, so the likelihood of `χ₁, …, χ_k` is `∏ᵢ P[χᵢ | T, pᵢ]` (equation (40)).

Recorded: Theorem 1 (`max_p P[χ | T, p] = r ^ (-(l(χ, T) + 1))` for one character, for unrooted
and rooted trees); equation (42) (the joint maximum is `r ^ (-(l(X, T) + k))`, `l(X, T)` the
total length); Theorem 5 (over any finite family of candidate trees, the maximum-likelihood trees
under no common mechanism are exactly the maximum-parsimony trees; the family generalizes the
source's implicit universe); and Theorem 6 (at every root vertex, leaves included, the
maximum-likelihood and maximum-parsimony estimates of the root state agree).

Theorem 1 concerns a single character: the paper notes that it "applies only to a single
character, and not to a set of characters"; with one common parameter vector for `k` characters
the product is only bounded by `r ^ (-(l(X, T) + k))` (equation (14)), and equality need not be
attained. The printed equation (44) fails when the root is a leaf `ρ` with `χ(ρ) ≠ α` (left side
`0`); Theorem 6 still holds there, since both estimates are `{χ(ρ)}`.

The trees are recorded here with their own carrier (`UnrootedPhyloTree`, `RootedPhyloTree`):
the shared phylogenetic-tree predicate with the degree condition is not yet in the repository.
The parsimony module `CSLibExt.Bioinformatics.Phylogenetics.Parsimony` concerns rooted strictly
binary trees and is not the general setting of this paper.

Sources: C. Tuffley and M. Steel, "Links between maximum likelihood and maximum parsimony under a
simple model of site substitution", Bulletin of Mathematical Biology 59 (1997) 581–607,
doi:10.1007/BF02459467, Definitions 1–2, equations (1)–(3), (13), (14), (38), (40), (42), (43),
Theorems 1, 5 and 6.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.NoCommonMechanismParsimonyWanted

/-- An **unrooted phylogenetic tree** on the taxa `X`: a finite tree whose leaves (degree-one
vertices) are exactly the labelled vertices, distinct taxa getting distinct leaves, and whose
other vertices have degree at least three. -/
structure UnrootedPhyloTree (X : Type) : Type 1 where
  /-- The vertex type. -/
  V : Type
  /-- The vertex type is finite. -/
  [fintype : Fintype V]
  /-- The tree. -/
  G : SimpleGraph V
  /-- Adjacency is decidable (so that degrees are defined). -/
  [decRel : DecidableRel G.Adj]
  /-- `G` is a tree. -/
  isTree : G.IsTree
  /-- The leaf of each taxon. -/
  label : X → V
  /-- Distinct taxa have distinct leaves. -/
  label_injective : Function.Injective label
  /-- The leaves are exactly the labelled vertices. -/
  degree_eq_one_iff : ∀ v, G.degree v = 1 ↔ v ∈ Set.range label
  /-- Every unlabelled vertex has degree at least three. -/
  three_le_degree : ∀ v ∉ Set.range label, 3 ≤ G.degree v

attribute [instance] UnrootedPhyloTree.fintype UnrootedPhyloTree.decRel

/-- A **rooted phylogenetic tree** on the taxa `X`: a finite tree with a root vertex, whose
labelled vertices are leaves (distinct taxa getting distinct leaves), whose other leaves can only
be the root, whose unlabelled vertices other than the root have degree at least three, and whose
root, if unlabelled, has degree at least two. The root may be a leaf. -/
structure RootedPhyloTree (X : Type) : Type 1 where
  /-- The vertex type. -/
  V : Type
  /-- The vertex type is finite. -/
  [fintype : Fintype V]
  /-- The tree. -/
  G : SimpleGraph V
  /-- Adjacency is decidable (so that degrees are defined). -/
  [decRel : DecidableRel G.Adj]
  /-- `G` is a tree. -/
  isTree : G.IsTree
  /-- The leaf of each taxon. -/
  label : X → V
  /-- The root. -/
  root : V
  /-- Distinct taxa have distinct leaves. -/
  label_injective : Function.Injective label
  /-- Labelled vertices are leaves. -/
  degree_label : ∀ x, G.degree (label x) = 1
  /-- Every unlabelled vertex other than the root has degree at least three. -/
  three_le_degree : ∀ v ∉ Set.range label, v ≠ root → 3 ≤ G.degree v
  /-- An unlabelled root has degree at least two. -/
  two_le_degree_root : root ∉ Set.range label → 2 ≤ G.degree root

attribute [instance] RootedPhyloTree.fintype RootedPhyloTree.decRel

section Model

variable {X S V : Type} [Fintype S] [Fintype V] (G : SimpleGraph V) (ℓ : X → V)

/-- The state function `σ` **extends** the character `χ`: it agrees with `χ` at every leaf. -/
def IsExtension (χ : X → S) (σ : V → S) : Prop :=
  ∀ x, σ (ℓ x) = χ x

/-- The edge `e` **changes** under the state function `σ`: its endpoints get different states. -/
def Changed (σ : V → S) : Sym2 V → Prop :=
  Sym2.lift ⟨fun u v => σ u ≠ σ v, fun _ _ => propext ne_comm⟩

open Classical in
/-- The **changing number** `ch(σ)`: the number of edges whose endpoints get different states. -/
noncomputable def changeNumber (σ : V → S) : ℕ :=
  (G.edgeFinset.filter (Changed σ)).card

open Classical in
/-- The **length** `l(χ, T)` of a character: the least changing number of an extension. -/
noncomputable def charLength (χ : X → S) : ℕ :=
  sInf {c | ∃ σ : V → S, IsExtension ℓ χ σ ∧ changeNumber G σ = c}

open Classical in
/-- The parameter vector `p` lies in the closed box: `0 ≤ p e ≤ (r - 1) / r` on every edge. -/
def InBox (p : Sym2 V → ℝ) : Prop :=
  ∀ e ∈ G.edgeSet, 0 ≤ p e ∧ p e ≤ ((Fintype.card S : ℝ) - 1) / Fintype.card S

open Classical in
/-- The probability of the extension `σ` in the fully symmetric model (equation (2)):
`(1 / r) ∏_{e unchanged} (1 - p e) ∏_{e changed} p e / (r - 1)`. -/
noncomputable def extProb (p : Sym2 V → ℝ) (σ : V → S) : ℝ :=
  (Fintype.card S : ℝ)⁻¹ * ∏ e ∈ G.edgeFinset,
    if Changed σ e then p e / ((Fintype.card S : ℝ) - 1) else 1 - p e

open Classical in
/-- The probability of the character `χ` (equation (3)): the sum over its extensions. -/
noncomputable def charProb (p : Sym2 V → ℝ) (χ : X → S) : ℝ :=
  ∑ σ ∈ Finset.univ.filter (IsExtension ℓ χ), extProb G p σ

open Classical in
/-- The likelihood of the root state `α` at the vertex `ρ` (equation (43)):
`P[χ | χ̂(ρ) = α, T, p] = r ∑_{χ̂ extends χ, χ̂(ρ) = α} P[χ̂ | T, p]`. -/
noncomputable def rootStateLik (ρ : V) (p : Sym2 V → ℝ) (χ : X → S) (α : S) : ℝ :=
  Fintype.card S * ∑ σ ∈ Finset.univ.filter (fun σ => IsExtension ℓ χ σ ∧ σ ρ = α),
    extProb G p σ

open Classical in
/-- The **maximum-likelihood root-state estimate** at `ρ`: the states whose likelihood,
maximized over the parameter box, is largest. -/
noncomputable def mlRootStates (ρ : V) (χ : X → S) : Set S :=
  {α | ∀ β, sSup {L | ∃ p, InBox (S := S) G p ∧ L = rootStateLik G ℓ ρ p χ β} ≤
    sSup {L | ∃ p, InBox (S := S) G p ∧ L = rootStateLik G ℓ ρ p χ α}}

open Classical in
/-- The **maximum-parsimony root-state estimate** at `ρ`: the states taken at `ρ` by some
minimal extension. -/
def mpRootStates (ρ : V) (χ : X → S) : Set S :=
  {α | ∃ σ : V → S, IsExtension ℓ χ σ ∧ changeNumber G σ = charLength G ℓ χ ∧ σ ρ = α}

end Model

variable {X S : Type} [Fintype S]

open Classical in
/-- The set of joint likelihoods of `k` characters on `T` under no common mechanism: one
parameter vector per character, each in the box (equation (40)). -/
def ncmLikelihoods {k : ℕ} (T : UnrootedPhyloTree X) (χ : Fin k → X → S) : Set ℝ :=
  {L | ∃ p : Fin k → Sym2 T.V → ℝ, (∀ i, InBox (S := S) T.G (p i)) ∧
    L = ∏ i, charProb T.G T.label (p i) (χ i)}

open Classical in
/-- The total length (parsimony score) `l(X, T) = ∑ᵢ l(χᵢ, T)` (equation (38)). -/
noncomputable def totalLength {k : ℕ} (T : UnrootedPhyloTree X) (χ : Fin k → X → S) : ℕ :=
  ∑ i, charLength T.G T.label (χ i)

/-- **Theorem 1, unrooted** (Tuffley and Steel 1997, equation (13)): for an `r`-state character
`χ` (`r ≥ 2`) on an unrooted phylogenetic tree `T`, the maximum of `P[χ | T, p]` over the
parameter box is `r ^ (-(l(χ, T) + 1))`.

Source: Tuffley and Steel (1997), Theorem 1. -/
public theorem_wanted isGreatest_charProb_unrooted (hS : 2 ≤ Fintype.card S)
    (T : UnrootedPhyloTree X) (χ : X → S) :
    IsGreatest {P | ∃ p, InBox (S := S) T.G p ∧ P = charProb T.G T.label p χ}
      (((Fintype.card S : ℝ) ^ (charLength T.G T.label χ + 1))⁻¹)

/-- **Theorem 1, rooted** (Tuffley and Steel 1997, equation (13)): the same maximum
`r ^ (-(l(χ, T) + 1))` for a rooted phylogenetic tree, whose root may have degree two.

Source: Tuffley and Steel (1997), Theorem 1. -/
public theorem_wanted isGreatest_charProb_rooted (hS : 2 ≤ Fintype.card S)
    (T : RootedPhyloTree X) (χ : X → S) :
    IsGreatest {P | ∃ p, InBox (S := S) T.G p ∧ P = charProb T.G T.label p χ}
      (((Fintype.card S : ℝ) ^ (charLength T.G T.label χ + 1))⁻¹)

/-- **The joint maximum under no common mechanism** (Tuffley and Steel 1997, equation (42)): for
`k` characters on an unrooted phylogenetic tree `T`, the largest joint likelihood with one
parameter vector per character is `r ^ (-(l(X, T) + k))`.

Source: Tuffley and Steel (1997), equation (42). -/
public theorem_wanted isGreatest_ncmLikelihoods (hS : 2 ≤ Fintype.card S) {k : ℕ}
    (T : UnrootedPhyloTree X) (χ : Fin k → X → S) :
    IsGreatest (ncmLikelihoods T χ) (((Fintype.card S : ℝ) ^ (totalLength T χ + k))⁻¹)

/-- **Theorem 5** (Tuffley and Steel 1997): for any finite family `F` of candidate unrooted
phylogenetic trees and characters `χ₁, …, χ_k`, a tree of the family maximizes the likelihood
under no common mechanism exactly when it minimizes the parsimony score: maximum likelihood and
maximum parsimony choose the same tree or trees.

Source: Tuffley and Steel (1997), Theorem 5. -/
public theorem_wanted ncm_ml_iff_mp (hS : 2 ≤ Fintype.card S) {m k : ℕ}
    (F : Fin m → UnrootedPhyloTree X) (χ : Fin k → X → S) (j : Fin m) :
    (∀ j', sSup (ncmLikelihoods (F j') χ) ≤ sSup (ncmLikelihoods (F j) χ)) ↔
      ∀ j', totalLength (F j) χ ≤ totalLength (F j') χ

/-- **Theorem 6** (Tuffley and Steel 1997): under the fully symmetric model, at every root of a
rooted phylogenetic tree (a leaf included), the maximum-likelihood and maximum-parsimony
estimates of the root state agree.

Source: Tuffley and Steel (1997), Theorem 6. -/
public theorem_wanted mlRootStates_eq_mpRootStates (hS : 2 ≤ Fintype.card S)
    (T : RootedPhyloTree X) (χ : X → S) :
    mlRootStates T.G T.label T.root χ = mpRootStates T.G T.label T.root χ

end WantedExt.Biology.ComputationalBiology.NoCommonMechanismParsimonyWanted
