/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LCA reconciliation minimizes duplication, loss and deep-coalescence costs

Wu and Zhang (2011): gene trees and species trees are rooted binary trees; the species tree is
uniquely leaf-labeled and every leaf of the gene tree `G` carries the label of a leaf of the species
tree `S`. Write `v ≤ u` when `u` lies on the path from the root to `v`. A reconciliation is a map
`f : V(G) → V(S)` that is leaf-preserving (a gene leaf goes to the species leaf with its label) and
order-preserving (`u ≤ v` implies `f(u) ≤ f(v)`). The LCA reconciliation `M` sends a gene leaf to
its species leaf and an internal vertex `u` with children `u₁, u₂` to `lca(M(u₁), M(u₂))`. For an
internal vertex `u`, `f` has a duplication at `u` (`δ_f(u) = 1`) iff (D-i) `f(u) = f(u_i)` for a
child `u_i`, or (D-ii) the paths `P(f(u), f(u₁))` and `P(f(u), f(u₂))` share an edge. The costs are

* `gd(f) = ∑_u δ_f(u)` (gene duplications),
* `gl(f) = ∑_u l_f(u)`, `l_f(u) = d(f(u), f(u₁)) + d(f(u), f(u₂)) + 2 (δ_f(u) - 1)` for internal
  `u` and `0` for leaves (gene losses; computed in `ℤ`),
* `dc(f) = ∑_e τ_f(e)` over the edges `e` of `S`, where `τ_f(e) = k` if exactly `k + 1 ≥ 2` edges
  `(u, v)` of `G` have `e` on the path `P(f(u), f(v))`, and `0` otherwise (deep coalescence).

Theorem 2: if `f' ≠ f` are reconciliations with `f'(v) ≤ f(v)` for every `v`, then
`gd(f') ≤ gd(f)`, `gl(f') < gl(f)` and `dc(f') < dc(f)`. Corollary 4: the LCA reconciliation has
the minimum duplication cost and is the unique reconciliation with the optimal loss cost and the
unique one with the optimal deep-coalescence cost; hence it minimizes duplication plus loss.
Theorem 2 is proved in `Domains.Biology.ComputationalBiology.LCAReconciliationCostsLtOfLe`.

A rooted tree is given by a parent map with a root from which every vertex descends; it is binary
when every vertex has zero or two children. An edge is named by its lower endpoint. The species
leaves serve as the labels. The definitions of a reconciliation, duplication and the three costs
follow the source; nothing about the LCA reconciliation's optimality is assumed. These definitions,
and that of a rooted binary tree, are defined in
`Domains.Biology.ComputationalBiology.LCAReconciliationCostsLtOfLe`.

Overlap: `WantedExt/Complexity/NPComplete/GeneDuplicationSpeciesTreeWanted.lean` defines LCA
mappings and duplications for the NP species-tree problem; the optimality of the LCA map is not
stated there.

Sources: T. Wu and L. Zhang, "Structural properties of the reconciliation space and their
applications in enumerating nearly-optimal reconciliations between a gene tree and a species tree",
BMC Bioinformatics 12 (Suppl 9) (2011) S7, doi:10.1186/1471-2105-12-S9-S7, definitions (1)–(3),
Theorem 2 and Corollary 4.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Lattice.Nat
public import Domains.Biology.ComputationalBiology.LCAReconciliationCostsLtOfLe

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.LCAReconciliationWanted

namespace RootedBinTree

variable {V : Type*} [Fintype V] (T : RootedBinTree V)

end RootedBinTree

variable {G S : Type*} [Fintype G] [Fintype S]

/-- `M` is the **LCA reconciliation**: `M` sends each gene leaf to its species leaf, and each
internal gene vertex `u` to the least common ancestor of the images of its children (a common
ancestor-or-self of them lying below every other common ancestor-or-self). -/
def IsLCAReconciliation (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (M : G → S) : Prop :=
  (∀ x, TG.IsLeaf x → M x = lab x) ∧ ∀ u, ¬ TG.IsLeaf u →
    (∀ c ∈ TG.children u, TS.Le (M c) (M u)) ∧
      ∀ s, (∀ c ∈ TG.children u, TS.Le (M c) s) → TS.Le (M u) s

/-- **Optimality of the LCA reconciliation** (Wu and Zhang 2011, Corollary 4): for rooted binary
trees `TG`, `TS` with gene leaf labels `lab` mapping gene leaves to species leaves, the LCA
reconciliation `M` and every reconciliation `f`: `gd(M) ≤ gd(f)`; `gl(M) ≤ gl(f)`, with equality
only if `f = M`; `dc(M) ≤ dc(f)`, with equality only if `f = M`; and hence
`gd(M) + gl(M) ≤ gd(f) + gl(f)`.

Source: Wu and Zhang (2011), Corollary 4. -/
public theorem_wanted lca_optimal (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (hlab : ∀ x, TG.IsLeaf x → TS.IsLeaf (lab x)) (M : G → S)
    (hM : IsLCAReconciliation TG TS lab M) (f : G → S) (hf : IsReconciliation TG TS lab f) :
    gd TG TS M ≤ gd TG TS f ∧
      (gl TG TS M ≤ gl TG TS f ∧ (gl TG TS f = gl TG TS M → f = M)) ∧
      (dc TG TS M ≤ dc TG TS f ∧ (dc TG TS f = dc TG TS M → f = M)) ∧
      gd TG TS M + gl TG TS M ≤ gd TG TS f + gl TG TS f

end WantedExt.Biology.ComputationalBiology.LCAReconciliationWanted
