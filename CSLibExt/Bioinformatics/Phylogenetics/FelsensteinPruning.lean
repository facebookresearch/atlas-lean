/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Ring

/-!
# Phylogenetic likelihood: Felsenstein's pruning algorithm

A rooted binary phylogeny with leaf labels `L` is a `Tree L S R`: every internal node carries
the transition weights `P a b` (from state `a` at the node to state `b` at the child) on its
left and right child edges, with character states `S` and weights in a commutative semiring `R`
(probabilities in `ℝ` or `ℚ`; for a Markov substitution model `P = exp (t Q)` for the branch
length `t`). The data at one site are leaf weights `obs : L → S → R`: the indicator of the
observed base, or a partial likelihood for an ambiguity code.

Following Felsenstein (1981), the likelihood of the site given root state `s`, `bruteLik obs t s`,
is the sum over all assignments of states to the non-root nodes of the tree (a `Labeling t`
stores the states of the two children of every internal node, so with the root state it fixes a
state at every node) of the product, over all edges, of the transition weights, times the leaf
weights at the leaves. Felsenstein's **pruning algorithm** `prune` computes the same quantity
bottom-up: a leaf contributes `obs l s`, and an internal node multiplies, over its two children,
the sum over the child's state `a` of `P s a` times the child's partial likelihood at `a`.

## Main results

* `prune_eq_bruteLik`: **pruning computes the likelihood conditioned on the root state**.
* `likelihood_eq_sum_prune`: with root distribution `π`, the site likelihood is
  `∑ s, π s * prune obs t s`.
* `card_labeling`: the brute-force sum has `|S| ^ (2 · #internal nodes)` terms.
* `pruneTab_get`: the tabulated algorithm on `Fin n` states computes `prune`.
* `sum_prod_siteWeight_eq_prod_likelihood`: for independent sites, the likelihood of an
  alignment (the sum over all per-site root states and labelings of the product of per-site
  weights) is the product of the per-site likelihoods.

## Cost model

The cost is the number of semiring operations. `pruneTab` computes the whole vector of partial
likelihoods of each subtree once (the child vectors are evaluated before the parent's), and
does `O(n²)` operations per internal node for `n` states: `O(#internal nodes · |S|²)` in total
(plus `O(|S|)` per leaf). The brute-force sum `bruteLik` ranges over `|S| ^ (#nodes - 1)`
labelings, exponential in the size of the tree. The untabulated `prune` is a specification: it
recomputes the children's values for each parent state, so evaluating it directly takes time
exponential in the depth.

## References

* J. Felsenstein, *Evolutionary trees from DNA sequences: a maximum likelihood approach*,
  J. Mol. Evol. 17 (1981), 368–376.
* J. Felsenstein, *Inferring Phylogenies*, Sinauer, 2004, chapters 13 and 16.
* C. Semple and M. Steel, *Phylogenetics*, Oxford University Press, 2003, chapter 8.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Phylogenetics.FelsensteinPruning

universe u v w

/-- A rooted binary tree with leaf labels `L`; an internal node `node P l Q r` carries the
transition weights `P` and `Q` (from the node's state to the child's state) on the edges to its
left child `l` and right child `r`. -/
inductive Tree (L : Type u) (S : Type v) (R : Type w) where
  /-- A leaf with label `l`. -/
  | leaf : L → Tree L S R
  /-- An internal node with transition weights `P` to the left child and `Q` to the right one. -/
  | node : (S → S → R) → Tree L S R → (S → S → R) → Tree L S R → Tree L S R

variable {L : Type u} {S : Type v} {R : Type w}

namespace Tree

/-- The number of internal nodes. -/
def numInternal : Tree L S R → ℕ
  | leaf _ => 0
  | node _ l _ r => numInternal l + numInternal r + 1

/-- The number of leaves. -/
def numLeaves : Tree L S R → ℕ
  | leaf _ => 1
  | node _ l _ r => numLeaves l + numLeaves r

end Tree

open Tree

/-- A labeling of the non-root nodes of a tree by states: at every internal node, the states of
its two children and labelings of the two subtrees. -/
def Labeling : Tree L S R → Type v
  | leaf _ => PUnit
  | node _ l _ r => (S × Labeling l) × (S × Labeling r)

/-- A labeling of a leaf carries no data. -/
instance (l : L) : Unique (Labeling (leaf l : Tree L S R)) :=
  inferInstanceAs (Unique PUnit)

/-- Labelings of a finite state space form a finite type. -/
instance instFintypeLabeling [Fintype S] : (t : Tree L S R) → Fintype (Labeling t)
  | leaf _ => inferInstanceAs (Fintype PUnit)
  | node _ l _ r =>
    letI := instFintypeLabeling l
    letI := instFintypeLabeling r
    inferInstanceAs (Fintype ((S × Labeling l) × (S × Labeling r)))

/-- There are `|S| ^ (2 · #internal nodes)` labelings (one state for each non-root node), so the
brute-force sum `bruteLik` has exponentially many terms. -/
theorem card_labeling [Fintype S] :
    ∀ t : Tree L S R, Fintype.card (Labeling t) = Fintype.card S ^ (2 * t.numInternal)
  | leaf _ => rfl
  | node P l Q r => by
      change Fintype.card ((S × Labeling l) × (S × Labeling r)) = _
      simp only [Fintype.card_prod, card_labeling l, card_labeling r, numInternal]
      ring

section Likelihood

variable [CommSemiring R] (obs : L → S → R)

/-- The weight of a labeling given root state `s`: the product over all edges of the transition
weight from the parent's state to the child's state, times the leaf weight `obs l` at the state
of every leaf `l`. -/
def weight : (t : Tree L S R) → S → Labeling t → R
  | leaf l, s, _ => obs l s
  | node P l Q r, s, z =>
    (P s z.1.1 * weight l z.1.1 z.1.2) * (Q s z.2.1 * weight r z.2.1 z.2.2)

variable [Fintype S]

/-- The likelihood of the leaf data conditioned on root state `s`, by brute force: the sum of
the weights of all labelings of the non-root nodes. -/
def bruteLik (t : Tree L S R) (s : S) : R :=
  ∑ x : Labeling t, weight obs t s x

/-- The site likelihood with root distribution `π`: `∑ s, π s * bruteLik obs t s`. -/
def likelihood (t : Tree L S R) (π : S → R) : R :=
  ∑ s, π s * bruteLik obs t s

/-- Felsenstein's pruning recursion: the partial likelihood of the subtree `t` given state `s`
at its root. -/
def prune : Tree L S R → S → R
  | leaf l, s => obs l s
  | node P l Q r, s => (∑ a, P s a * prune l a) * (∑ b, Q s b * prune r b)

/-- At a leaf, the brute-force likelihood is the leaf weight. -/
theorem bruteLik_leaf (l : L) (s : S) : bruteLik obs (leaf l) s = obs l s := by
  simp [bruteLik, weight]

/-- The brute-force likelihood factors over the two subtrees of the root (the distributive law
behind pruning). -/
theorem bruteLik_node (P Q : S → S → R) (l r : Tree L S R) (s : S) :
    bruteLik obs (node P l Q r) s =
      (∑ a, P s a * bruteLik obs l a) * (∑ b, Q s b * bruteLik obs r b) := by
  change ∑ z : (S × Labeling l) × (S × Labeling r),
    (P s z.1.1 * weight obs l z.1.1 z.1.2) * (Q s z.2.1 * weight obs r z.2.1 z.2.2) = _
  have hl : ∑ a, P s a * bruteLik obs l a = ∑ p : S × Labeling l, P s p.1 * weight obs l p.1 p.2 :=
    by simp [bruteLik, Fintype.sum_prod_type, Finset.mul_sum]
  have hr : ∑ b, Q s b * bruteLik obs r b = ∑ p : S × Labeling r, Q s p.1 * weight obs r p.1 p.2 :=
    by simp [bruteLik, Fintype.sum_prod_type, Finset.mul_sum]
  rw [hl, hr, Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- **Felsenstein's pruning algorithm computes the likelihood conditioned on the root state.** -/
theorem prune_eq_bruteLik : ∀ (t : Tree L S R) (s : S), prune obs t s = bruteLik obs t s
  | leaf l, s => (bruteLik_leaf obs l s).symm
  | node P l Q r, s => by
      rw [bruteLik_node, prune]
      simp only [prune_eq_bruteLik l, prune_eq_bruteLik r]

/-- **The site likelihood by pruning**: `likelihood obs t π = ∑ s, π s * prune obs t s`. -/
theorem likelihood_eq_sum_prune (t : Tree L S R) (π : S → R) :
    likelihood obs t π = ∑ s, π s * prune obs t s := by
  simp only [likelihood, prune_eq_bruteLik]

end Likelihood

/-! ## The tabulated algorithm -/

section Tabulated

variable {n : ℕ} [CommSemiring R] (obs : L → Fin n → R)

/-- Felsenstein's pruning algorithm, tabulated on the states `Fin n`: the vector of partial
likelihoods of each subtree is computed once, with `O(n²)` operations per internal node. -/
def pruneTab : Tree L (Fin n) R → Vector R n
  | leaf l => Vector.ofFn (obs l)
  | node P l Q r =>
    let u := pruneTab l
    let v := pruneTab r
    Vector.ofFn fun s => (∑ a, P s a * u[a]) * (∑ b, Q s b * v[b])

/-- The tabulated algorithm computes the pruning recursion. -/
theorem pruneTab_get : ∀ (t : Tree L (Fin n) R) (s : Fin n),
    (pruneTab obs t)[s] = prune obs t s
  | leaf l, s => by simp [pruneTab, prune]
  | node P l Q r, s => by
      simp [pruneTab, prune, pruneTab_get l, pruneTab_get r]

/-- The site likelihood from the tabulated partial likelihoods at the root. -/
theorem likelihood_eq_sum_pruneTab (t : Tree L (Fin n) R) (π : Fin n → R) :
    likelihood obs t π = ∑ s, π s * (pruneTab obs t)[s] := by
  simp only [likelihood_eq_sum_prune, pruneTab_get]

end Tabulated

/-! ## Independent sites -/

section Sites

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R] [Fintype S]

/-- **Independent sites**: for an alignment whose sites `k : ι` evolve independently along the
same tree with leaf data `obs k`, the joint likelihood (the sum over all choices of a root state
and a labeling at every site of the product of the per-site weights) is the product of the
per-site likelihoods. -/
theorem sum_prod_siteWeight_eq_prod_likelihood (obs : ι → L → S → R) (t : Tree L S R)
    (π : S → R) :
    ∑ σ : ι → S × Labeling t, ∏ k, π (σ k).1 * weight (obs k) t (σ k).1 (σ k).2 =
      ∏ k, likelihood (obs k) t π := by
  simp only [likelihood, bruteLik, Finset.mul_sum, ← Fintype.sum_prod_type']
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

end Sites

end Cslib.Bioinformatics.Phylogenetics.FelsensteinPruning
