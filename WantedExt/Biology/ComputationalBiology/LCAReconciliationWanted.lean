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

A rooted tree is given by a parent map with a root from which every vertex descends; it is binary
when every vertex has zero or two children. An edge is named by its lower endpoint. The species
leaves serve as the labels. The definitions of a reconciliation, duplication and the three costs
follow the source; nothing about the LCA reconciliation's optimality is assumed.

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

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.LCAReconciliationWanted

open Classical in
/-- A **rooted binary tree** on the finite vertex type `V`: a parent map, with `none` exactly at the
root, from which every vertex descends by iterating the parent map, and in which every vertex has
zero or two children. -/
structure RootedBinTree (V : Type*) [Fintype V] where
  /-- The parent of each vertex (`none` at the root). -/
  parent : V → Option V
  /-- The root. -/
  root : V
  /-- The root has no parent. -/
  parent_root : parent root = none
  /-- Every other vertex has a parent. -/
  parent_isSome : ∀ v, v ≠ root → (parent v).isSome
  /-- Every vertex reaches the root by iterating the parent map. -/
  reach_root : ∀ v, ∃ k, Nat.iterate (fun o => Option.bind o parent) k (some v) = some root
  /-- Every vertex has zero or two children. -/
  binary : ∀ u, (Finset.univ.filter fun c => parent c = some u).card = 0 ∨
    (Finset.univ.filter fun c => parent c = some u).card = 2

namespace RootedBinTree

variable {V : Type*} [Fintype V] (T : RootedBinTree V)

/-- The `k`-th ancestor of `v` (`some v` for `k = 0`; `none` above the root). -/
def ancestor (k : ℕ) (v : V) : Option V :=
  Nat.iterate (fun o => Option.bind o T.parent) k (some v)

/-- `T.Le v u`: `u` lies on the path from the root to `v` (`v ≤ u` in the source's notation), i.e.
`u` is an ancestor of `v` or `u = v`. -/
def Le (v u : V) : Prop :=
  ∃ k, T.ancestor k v = some u

open Classical in
/-- The children of `u`. -/
noncomputable def children (u : V) : Finset V :=
  Finset.univ.filter fun c => T.parent c = some u

/-- `x` is a leaf: it has no children. -/
def IsLeaf (x : V) : Prop :=
  T.children x = ∅

/-- The number of edges `d(u, v)` on the path from `v` up to its ancestor-or-self `u`. -/
noncomputable def dist (u v : V) : ℕ :=
  sInf {k | T.ancestor k v = some u}

open Classical in
/-- The edges of the path `P(u, v)` from `u` down to `v`, each named by its lower endpoint: the
vertices `c` with `v ≤ c`, `c ≤ u` and `c ≠ u`. -/
noncomputable def pathEdges (u v : V) : Finset V :=
  Finset.univ.filter fun c => T.Le v c ∧ T.Le c u ∧ c ≠ u

end RootedBinTree

variable {G S : Type*} [Fintype G] [Fintype S]

/-- `f` is a **reconciliation** of the gene tree `TG` (leaf labels `lab`, gene leaves to species
leaves) with the species tree `TS`: leaf-preserving and order-preserving. -/
def IsReconciliation (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S) (f : G → S) :
    Prop :=
  (∀ x, TG.IsLeaf x → f x = lab x) ∧ ∀ v u, TG.Le v u → TS.Le (f v) (f u)

/-- `M` is the **LCA reconciliation**: `M` sends each gene leaf to its species leaf, and each
internal gene vertex `u` to the least common ancestor of the images of its children (a common
ancestor-or-self of them lying below every other common ancestor-or-self). -/
def IsLCAReconciliation (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (M : G → S) : Prop :=
  (∀ x, TG.IsLeaf x → M x = lab x) ∧ ∀ u, ¬ TG.IsLeaf u →
    (∀ c ∈ TG.children u, TS.Le (M c) (M u)) ∧
      ∀ s, (∀ c ∈ TG.children u, TS.Le (M c) s) → TS.Le (M u) s

open Classical in
/-- `f` has a **duplication** at `u` (`δ_f(u) = 1`): `u` is internal and (D-i) `f(u) = f(c)` for a
child `c`, or (D-ii) the paths from `f(u)` to the images of two distinct children share an edge. -/
def IsDup (TG : RootedBinTree G) (TS : RootedBinTree S) (f : G → S) (u : G) : Prop :=
  ¬ TG.IsLeaf u ∧ ((∃ c ∈ TG.children u, f u = f c) ∨
    ∃ c₁ ∈ TG.children u, ∃ c₂ ∈ TG.children u, c₁ ≠ c₂ ∧
      (TS.pathEdges (f u) (f c₁) ∩ TS.pathEdges (f u) (f c₂)).Nonempty)

open Classical in
/-- The duplication indicator `δ_f(u) ∈ {0, 1}`. -/
noncomputable def δ (TG : RootedBinTree G) (TS : RootedBinTree S) (f : G → S) (u : G) : ℤ :=
  if IsDup TG TS f u then 1 else 0

/-- The **gene-duplication cost** `gd(f) = ∑_u δ_f(u)`. -/
noncomputable def gd (TG : RootedBinTree G) (TS : RootedBinTree S) (f : G → S) : ℤ :=
  ∑ u, δ TG TS f u

open Classical in
/-- The **loss count** at `u`: `∑_{c child of u} d(f(u), f(c)) + 2 (δ_f(u) - 1)` for internal `u`
and `0` for leaves. -/
noncomputable def lossAt (TG : RootedBinTree G) (TS : RootedBinTree S) (f : G → S) (u : G) : ℤ :=
  if TG.IsLeaf u then 0
  else (∑ c ∈ TG.children u, (TS.dist (f u) (f c) : ℤ)) + 2 * (δ TG TS f u - 1)

/-- The **gene-loss cost** `gl(f) = ∑_u l_f(u)`. -/
noncomputable def gl (TG : RootedBinTree G) (TS : RootedBinTree S) (f : G → S) : ℤ :=
  ∑ u, lossAt TG TS f u

open Classical in
/-- `τ_f(e)`: one less than the number of gene edges `(parent c, c)` whose image path contains the
species edge `e`, when that number is at least `2`, and `0` otherwise. -/
noncomputable def extraLineages (TG : RootedBinTree G) (TS : RootedBinTree S) (f : G → S)
    (e : S) : ℕ :=
  (Finset.univ.filter fun c : G => ∃ u, TG.parent c = some u ∧
    e ∈ TS.pathEdges (f u) (f c)).card - 1

open Classical in
/-- The **deep-coalescence cost** `dc(f) = ∑_e τ_f(e)` over the edges `e` of the species tree (the
non-root vertices). -/
noncomputable def dc (TG : RootedBinTree G) (TS : RootedBinTree S) (f : G → S) : ℕ :=
  ∑ e ∈ Finset.univ.filter (· ≠ TS.root), extraLineages TG TS f e

/-- **Monotonicity of the costs** (Wu and Zhang 2011, Theorem 2): for rooted binary trees `TG`, `TS`
with gene leaf labels `lab` mapping gene leaves to species leaves, and two distinct
reconciliations `f' ≠ f` with `f'(v) ≤ f(v)` for every gene vertex `v` (`f(v)` an
ancestor-or-self of `f'(v)`), `gd(f') ≤ gd(f)`, `gl(f') < gl(f)` and `dc(f') < dc(f)`.

Source: Wu and Zhang (2011), Theorem 2. -/
public theorem_wanted costs_lt_of_le (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (hlab : ∀ x, TG.IsLeaf x → TS.IsLeaf (lab x)) (f f' : G → S)
    (hf : IsReconciliation TG TS lab f) (hf' : IsReconciliation TG TS lab f')
    (hle : ∀ v, TS.Le (f' v) (f v)) (hne : f' ≠ f) :
    gd TG TS f' ≤ gd TG TS f ∧ gl TG TS f' < gl TG TS f ∧ dc TG TS f' < dc TG TS f

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
