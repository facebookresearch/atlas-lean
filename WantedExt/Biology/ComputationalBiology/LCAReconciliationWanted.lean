/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LCA reconciliation minimizes duplication and loss costs

For a gene tree `G` and a species tree `S` (rooted, binary, uniquely
leaf-labeled on the `S` side), a reconciliation is a leaf-preserving,
order-preserving vertex map `V(G) → V(S)`. The LCA reconciliation `M` sends
each leaf to its labeled species leaf and each internal vertex to the last
common ancestor of its children's images. It has minimum gene-duplication
cost, is the unique loss-optimal and deep-coalescence-optimal reconciliation,
and hence minimizes duplication plus loss.

Orientation: `le a b` means `a` is an ancestor-or-self of `b` (the root is
minimal). A map `f` is order-preserving when `le u v` implies
`le (f u) (f v)`; `M` is minimal when `le (M v) (f v)` for every `v`.

Overlap: `WantedExt/Complexity/NPComplete/GeneDuplicationSpeciesTreeWanted.lean`
defines LCA mappings and duplications for the NP species-tree problem; the
optimality of the LCA map is not stated there.

Sources: T. Wu and L. Zhang, "Structural properties of the reconciliation space
and their applications in enumerating nearly-optimal reconciliations between a
gene tree and a species tree", BMC Bioinformatics 12(Suppl 9):S7, 2011,
doi:10.1186/1471-2105-12-S9-S7, Corollary 4 (from Theorem 2); P. Gorecki and
J. Tiuryn, "DLS-trees: A model of evolutionary scenarios", Theor. Comput. Sci.
359(1-3):378-399, 2006, doi:10.1016/j.tcs.2006.05.019.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.LCAReconciliationWanted

open Classical

variable {G S : Type*} [Fintype G] [Fintype S] [DecidableEq G] [DecidableEq S]

/-- Finite rooted-tree data: ancestor-or-self order, root, leaf test, and
children (`none` exactly on leaves). -/
structure TreeData (V : Type*) [Fintype V] where
  le : V → V → Prop
  root : V
  isLeaf : V → Prop
  children : V → Option (V × V)

/-- A reconciliation is leaf-preserving and order-preserving. -/
def IsReconciliation (TG : TreeData G) (TS : TreeData S) (leafLabel : G → S)
    (f : G → S) : Prop :=
  (∀ x, TG.isLeaf x → f x = leafLabel x) ∧
    ∀ u v, TG.le u v → TS.le (f u) (f v)

/-- `s` is the last common ancestor of `a` and `b`: above both, and below
every other common ancestor-or-self. -/
def IsLca (sle : S → S → Prop) (s a b : S) : Prop :=
  sle s a ∧ sle s b ∧ ∀ t, sle t a → sle t b → sle t s

/-- Common-edge predicate for (D-ii): the down-paths from `a` to `b₁` and
`b₂` share a vertex strictly below `a`. -/
def shareEdge (sle : S → S → Prop) (a b₁ b₂ : S) : Prop :=
  ∃ w, w ≠ a ∧ sle a w ∧ sle w b₁ ∧ sle w b₂

/-- Duplication at `u`: (D-i) the image coincides with a child's image, or
(D-ii) the down-paths share an edge. Leaves never duplicate. -/
def IsDup (TG : TreeData G) (share : S → S → S → Prop) (f : G → S)
    (u : G) : Prop :=
  match TG.children u with
  | none => False
  | some (u₁, u₂) => f u = f u₁ ∨ f u = f u₂ ∨ share (f u) (f u₁) (f u₂)

/-- Gene-duplication cost: number of duplicating vertices. -/
noncomputable def dupCost (TG : TreeData G) (share : S → S → S → Prop) (f : G → S) :
    ℕ :=
  Finset.card (Finset.univ.filter (fun u => IsDup TG share f u))

/-- Edge-count distance: vertices on the down-path from `a` to `b`, minus one. -/
noncomputable def dist (sle : S → S → Prop) (a b : S) : ℕ :=
  Finset.card (Finset.univ.filter (fun w => sle a w ∧ sle w b)) - 1

/-- Loss segment at `u`: down-path lengths to the children's images plus the
duplication adjustment `2 * (δ - 1)`; zero on leaves. -/
def segLen (TG : TreeData G) (dist : S → S → ℕ) (δ : G → ℕ) (f : G → S)
    (u : G) : ℕ :=
  match TG.children u with
  | none => 0
  | some (u₁, u₂) =>
    dist (f u) (f u₁) + dist (f u) (f u₂) + 2 * (δ u - 1)

/-- Gene-loss cost: total loss-segment length over all vertices. -/
noncomputable def lossCost (TG : TreeData G) (dist : S → S → ℕ) (δ : G → ℕ)
    (f : G → S) : ℕ :=
  Finset.sum Finset.univ fun u => segLen TG dist δ f u

/-- **LCA reconciliation has minimum duplication cost** (Wu-Zhang 2011,
Corollary 4(a)): hypotheses are binary rooted trees with ancestor-or-self
orders (`hle_refl`, `hle_trans`), leaves exactly the childless vertices
(`hbin`), the species root above everything (`hroot`), the LCA map `M`
characterized by leaf agreement (`hMleaf`), the LCA recursion (`hMnode`),
and pointwise minimality (`hMmin`); `f` is any reconciliation. Conclusion:
`dupCost M ≤ dupCost f`.

Source: Wu-Zhang (2011), Corollary 4(a) via Theorem 2. -/
theorem_wanted lca_dupCost_min (TG : TreeData G) (TS : TreeData S)
    (leafLabel : G → S) (lcaS : S → S → S)
    (hle_refl_G : ∀ u : G, TG.le u u)
    (hle_trans_G : ∀ u v w : G, TG.le u v → TG.le v w → TG.le u w)
    (hle_refl_S : ∀ s : S, TS.le s s)
    (hle_trans_S : ∀ a b c : S, TS.le a b → TS.le b c → TS.le a c)
    (hbin_G : ∀ u : G, (TG.isLeaf u ∧ TG.children u = none) ∨
      ∃ u₁ u₂, TG.children u = some (u₁, u₂))
    (hroot : ∀ s : S, TS.le TS.root s)
    (M f : G → S)
    (hMleaf : ∀ x, TG.isLeaf x → M x = leafLabel x)
    (hMnode : ∀ u u₁ u₂, TG.children u = some (u₁, u₂) →
      IsLca TS.le (M u) (M u₁) (M u₂))
    (hMmin : ∀ v, TS.le (M v) (f v))
    (hf : IsReconciliation TG TS leafLabel f) :
    dupCost TG (shareEdge TS.le) M ≤ dupCost TG (shareEdge TS.le) f

/-- **LCA reconciliation minimizes duplication plus loss** (Wu-Zhang 2011,
consequence of Corollary 4): same tree, LCA-map, and reconciliation
hypotheses as `lca_dupCost_min`, with `δ` the duplication indicator.
Conclusion: `dupCost M + lossCost M ≤ dupCost f + lossCost f`.

Source: Wu-Zhang (2011), Corollary 4. -/
theorem_wanted lca_dupLoss_min (TG : TreeData G) (TS : TreeData S)
    (leafLabel : G → S) (lcaS : S → S → S)
    (δ : G → ℕ)
    (hle_refl_G : ∀ u : G, TG.le u u)
    (hle_trans_G : ∀ u v w : G, TG.le u v → TG.le v w → TG.le u w)
    (hle_refl_S : ∀ s : S, TS.le s s)
    (hle_trans_S : ∀ a b c : S, TS.le a b → TS.le b c → TS.le a c)
    (hbin_G : ∀ u : G, (TG.isLeaf u ∧ TG.children u = none) ∨
      ∃ u₁ u₂, TG.children u = some (u₁, u₂))
    (hroot : ∀ s : S, TS.le TS.root s)
    (M f : G → S)
    (hMleaf : ∀ x, TG.isLeaf x → M x = leafLabel x)
    (hMnode : ∀ u u₁ u₂, TG.children u = some (u₁, u₂) →
      IsLca TS.le (M u) (M u₁) (M u₂))
    (hMmin : ∀ v, TS.le (M v) (f v))
    (hf : IsReconciliation TG TS leafLabel f) :
    dupCost TG (shareEdge TS.le) M +
      lossCost TG (dist TS.le) δ M ≤
      dupCost TG (shareEdge TS.le) f + lossCost TG (dist TS.le) δ f

/-- **LCA reconciliation is the unique loss-optimal reconciliation**
(Wu-Zhang 2011, Corollary 4(b)): same tree, LCA-map, and reconciliation
hypotheses as `lca_dupCost_min`, with `δ` the duplication indicator and
`hloss_step` the strict single-step lemma (a strict pointwise improvement
strictly decreases loss). Conclusion: `lossCost M ≤ lossCost f`, with
equality only for `f = M`.

Source: Wu-Zhang (2011), Corollary 4(b). -/
theorem_wanted lca_lossCost_unique (TG : TreeData G) (TS : TreeData S)
    (leafLabel : G → S) (lcaS : S → S → S)
    (δ : G → ℕ)
    (hle_refl_G : ∀ u : G, TG.le u u)
    (hle_trans_G : ∀ u v w : G, TG.le u v → TG.le v w → TG.le u w)
    (hle_refl_S : ∀ s : S, TS.le s s)
    (hle_trans_S : ∀ a b c : S, TS.le a b → TS.le b c → TS.le a c)
    (hbin_G : ∀ u : G, (TG.isLeaf u ∧ TG.children u = none) ∨
      ∃ u₁ u₂, TG.children u = some (u₁, u₂))
    (hroot : ∀ s : S, TS.le TS.root s)
    (M f : G → S)
    (hMleaf : ∀ x, TG.isLeaf x → M x = leafLabel x)
    (hMnode : ∀ u u₁ u₂, TG.children u = some (u₁, u₂) →
      IsLca TS.le (M u) (M u₁) (M u₂))
    (hMmin : ∀ v, TS.le (M v) (f v))
    (hf : IsReconciliation TG TS leafLabel f)
    (hloss_step : ∀ g₁ g₂ : G → S, IsReconciliation TG TS leafLabel g₁ →
      IsReconciliation TG TS leafLabel g₂ →
      (∀ v, TS.le (g₁ v) (g₂ v)) →
      (∃ v, TS.le (g₁ v) (g₂ v) ∧ g₁ v ≠ g₂ v) →
      lossCost TG (dist TS.le) δ g₁ < lossCost TG (dist TS.le) δ g₂) :
    lossCost TG (dist TS.le) δ M ≤ lossCost TG (dist TS.le) δ f ∧
      (lossCost TG (dist TS.le) δ f = lossCost TG (dist TS.le) δ M →
        f = M)

/-- **LCA reconciliation is the unique deep-coalescence-optimal
reconciliation** (Wu-Zhang 2011, Corollary 4): same tree, LCA-map, and
reconciliation hypotheses as `lca_dupCost_min`. `deep` is the
deep-coalescence cost (total excess gene lineages over species branches),
with `hdeep_mono` (pointwise-smaller maps cost no more) and `hdeep_step`
(a strict pointwise improvement strictly decreases cost). Conclusion:
`deep M ≤ deep f`, with equality only for `f = M`.

Source: Wu-Zhang (2011), Corollary 4. -/
theorem_wanted lca_deepCost_unique (TG : TreeData G) (TS : TreeData S)
    (leafLabel : G → S) (lcaS : S → S → S)
    (deep : (G → S) → ℕ)
    (hle_refl_G : ∀ u : G, TG.le u u)
    (hle_trans_G : ∀ u v w : G, TG.le u v → TG.le v w → TG.le u w)
    (hle_refl_S : ∀ s : S, TS.le s s)
    (hle_trans_S : ∀ a b c : S, TS.le a b → TS.le b c → TS.le a c)
    (hbin_G : ∀ u : G, (TG.isLeaf u ∧ TG.children u = none) ∨
      ∃ u₁ u₂, TG.children u = some (u₁, u₂))
    (hroot : ∀ s : S, TS.le TS.root s)
    (M f : G → S)
    (hMleaf : ∀ x, TG.isLeaf x → M x = leafLabel x)
    (hMnode : ∀ u u₁ u₂, TG.children u = some (u₁, u₂) →
      IsLca TS.le (M u) (M u₁) (M u₂))
    (hMmin : ∀ v, TS.le (M v) (f v))
    (hf : IsReconciliation TG TS leafLabel f)
    (hdeep_mono : ∀ g₁ g₂ : G → S, IsReconciliation TG TS leafLabel g₁ →
      IsReconciliation TG TS leafLabel g₂ →
      (∀ v, TS.le (g₁ v) (g₂ v)) → deep g₁ ≤ deep g₂)
    (hdeep_step : ∀ g₁ g₂ : G → S, IsReconciliation TG TS leafLabel g₁ →
      IsReconciliation TG TS leafLabel g₂ →
      (∀ v, TS.le (g₁ v) (g₂ v)) →
      (∃ v, TS.le (g₁ v) (g₂ v) ∧ g₁ v ≠ g₂ v) →
      deep g₁ < deep g₂) :
    deep M ≤ deep f ∧ (deep f = deep M → f = M)

end WantedExt.Biology.ComputationalBiology.LCAReconciliationWanted
