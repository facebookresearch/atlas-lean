/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Order.Lattice.Nat

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Domains.Biology.ComputationalBiology.LCAReconciliationCostsLtOfLe

/-!
# Optimality of LCA reconciliation

This module defines the LCA reconciliation (`IsLCAReconciliation`) and proves its optimality (Wu and
Zhang 2011, Corollary 4). Rooted binary trees, reconciliations and their duplication, loss and
deep-coalescence costs come from
`Domains.Biology.ComputationalBiology.LCAReconciliationCostsLtOfLe`.

Source: T. Wu and L. Zhang, "Structural properties of the reconciliation space and their
applications in enumerating nearly-optimal reconciliations between a gene tree and a species tree",
BMC Bioinformatics 12 (Suppl 9) (2011) S7, doi:10.1186/1471-2105-12-S9-S7, definitions (1)–(3),
Theorem 2 and Corollary 4.
-/

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

private theorem ancestor_zero {V : Type*} [Fintype V] (T : RootedBinTree V) (v : V) :
    T.ancestor 0 v = some v := rfl

private theorem ancestor_succ {V : Type*} [Fintype V] (T : RootedBinTree V) (k : ℕ) (v : V) :
    T.ancestor (k + 1) v = (T.ancestor k v).bind T.parent := by
  exact Function.iterate_succ_apply' _ _ _

private theorem iterate_none {V : Type*} [Fintype V] (T : RootedBinTree V) (k : ℕ) :
    Nat.iterate (fun o => Option.bind o T.parent) k none = none := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, Option.bind_none]

private theorem ancestor_add {V : Type*} [Fintype V] (T : RootedBinTree V)
    (k l : ℕ) (v : V) :
    T.ancestor (k + l) v =
      Nat.iterate (fun o => Option.bind o T.parent) l (T.ancestor k v) := by
  rw [RootedBinTree.ancestor, Nat.add_comm, Function.iterate_add_apply]
  rfl

private theorem ancestor_root_succ {V : Type*} [Fintype V] (T : RootedBinTree V) (k : ℕ) :
    T.ancestor (k + 1) T.root = none := by
  rw [Nat.add_comm, ancestor_add]
  change Nat.iterate (fun o => Option.bind o T.parent) k (T.parent T.root) = none
  rw [T.parent_root, iterate_none]

private theorem root_time_unique {V : Type*} [Fintype V] (T : RootedBinTree V)
    (v : V) (k l : ℕ) (hk : T.ancestor k v = some T.root)
    (hl : T.ancestor l v = some T.root) : k = l := by
  by_contra h
  have bad : ∀ a b, T.ancestor a v = some T.root →
      T.ancestor b v = some T.root → a < b → False := by
    intro a b ha hb hab
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hab
    have hb' : T.ancestor (a + (d + 1)) v = some T.root := by
      simpa only [Nat.add_assoc] using hd ▸ hb
    rw [ancestor_add, ha] at hb'
    change T.ancestor (d + 1) T.root = some T.root at hb'
    rw [ancestor_root_succ] at hb'
    cases hb'
  rcases lt_or_gt_of_ne h with h | h
  · exact bad k l hk hl h
  · exact bad l k hl hk h

open Classical in
private noncomputable def depth {V : Type*} [Fintype V] (T : RootedBinTree V) (v : V) : ℕ :=
  Nat.find (T.reach_root v)

private theorem ancestor_depth {V : Type*} [Fintype V] (T : RootedBinTree V) (v : V) :
    T.ancestor (depth T v) v = some T.root := by
  classical
  exact Nat.find_spec (T.reach_root v)

private theorem depth_of_ancestor {V : Type*} [Fintype V] (T : RootedBinTree V)
    (v u : V) (k : ℕ) (h : T.ancestor k v = some u) :
    depth T v = k + depth T u := by
  apply root_time_unique T v
  · exact ancestor_depth T v
  · rw [ancestor_add, h]
    exact ancestor_depth T u

private theorem le_refl {V : Type*} [Fintype V] (T : RootedBinTree V) (v : V) : T.Le v v :=
  ⟨0, rfl⟩

private theorem le_trans {V : Type*} [Fintype V] (T : RootedBinTree V)
    {v u w : V} (hvu : T.Le v u) (huw : T.Le u w) : T.Le v w := by
  obtain ⟨k, hk⟩ := hvu
  obtain ⟨l, hl⟩ := huw
  exact ⟨k + l, by rw [ancestor_add, hk]; exact hl⟩

private theorem le_depth {V : Type*} [Fintype V] (T : RootedBinTree V)
    {v u : V} (h : T.Le v u) : depth T u ≤ depth T v := by
  obtain ⟨k, hk⟩ := h
  rw [depth_of_ancestor T v u k hk]
  omega

private theorem eq_of_le_depth {V : Type*} [Fintype V] (T : RootedBinTree V)
    {v u : V} (h : T.Le v u) (hd : depth T v = depth T u) : v = u := by
  obtain ⟨k, hk⟩ := h
  have hdepth := depth_of_ancestor T v u k hk
  have : k = 0 := by omega
  simpa only [this, ancestor_zero, Option.some.injEq] using hk

private theorem le_antisymm {V : Type*} [Fintype V] (T : RootedBinTree V)
    {v u : V} (hvu : T.Le v u) (huv : T.Le u v) : v = u := by
  exact eq_of_le_depth T hvu (Nat.le_antisymm (le_depth T huv) (le_depth T hvu))

private theorem ancestors_comparable {V : Type*} [Fintype V] (T : RootedBinTree V)
    {v u w : V} (hvu : T.Le v u) (hvw : T.Le v w) : T.Le u w ∨ T.Le w u := by
  obtain ⟨k, hk⟩ := hvu
  obtain ⟨l, hl⟩ := hvw
  rcases le_total k l with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    left
    refine ⟨d, ?_⟩
    rw [ancestor_add, hk] at hl
    exact hl
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    right
    refine ⟨d, ?_⟩
    rw [ancestor_add, hl] at hk
    exact hk

private theorem child_le {V : Type*} [Fintype V] (T : RootedBinTree V)
    {v u : V} (h : v ∈ T.children u) : T.Le v u := by
  classical
  exact ⟨1, (Finset.mem_filter.mp h).2⟩

private theorem depth_child {V : Type*} [Fintype V] (T : RootedBinTree V)
    {v u : V} (h : v ∈ T.children u) : depth T v = depth T u + 1 := by
  classical
  simpa only [Nat.add_comm] using depth_of_ancestor T v u 1 (Finset.mem_filter.mp h).2

private theorem child_internal {V : Type*} [Fintype V] (T : RootedBinTree V)
    {v u : V} (h : v ∈ T.children u) : ¬ T.IsLeaf u := by
  intro hl
  rw [RootedBinTree.IsLeaf] at hl
  rw [hl] at h
  exact Finset.notMem_empty v h

private noncomputable def rank {V : Type*} [Fintype V] (T : RootedBinTree V) (v : V) : ℕ :=
  (∑ u, depth T u) - depth T v

private theorem rank_child {V : Type*} [Fintype V] (T : RootedBinTree V)
    {v u : V} (h : v ∈ T.children u) : rank T v < rank T u := by
  have hd : depth T v ≤ ∑ u, depth T u :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  have hc := depth_child T h
  unfold rank
  omega

private theorem descendants_induction {V : Type*} [Fintype V] (T : RootedBinTree V)
    (P : V → Prop) (step : ∀ u, (∀ c ∈ T.children u, P c) → P u) (u : V) : P u := by
  induction h : rank T u using Nat.strong_induction_on generalizing u with
  | ind n ih =>
    apply step u
    intro c hc
    exact ih (rank T c) (h ▸ rank_child T hc) c rfl

private theorem lca_le {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S) (M f : G → S)
    (hM : IsLCAReconciliation TG TS lab M) (hf : IsReconciliation TG TS lab f) :
    ∀ u, TS.Le (M u) (f u) := by
  apply descendants_induction TG
  intro u ih
  by_cases hu : TG.IsLeaf u
  · rw [hM.1 u hu, hf.1 u hu]
    exact le_refl TS (lab u)
  · apply (hM.2 u hu).2
    intro c hc
    exact le_trans TS (ih c hc) (hf.2 c u (child_le TG hc))

private theorem monotone_of_children {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (f : G → S)
    (hedge : ∀ u c, c ∈ TG.children u → TS.Le (f c) (f u)) :
    ∀ v u, TG.Le v u → TS.Le (f v) (f u) := by
  intro v u ⟨k, hk⟩
  induction k generalizing u with
  | zero =>
    have : v = u := Option.some.inj hk
    subst u
    exact le_refl TS (f v)
  | succ k ih =>
    rw [ancestor_succ] at hk
    cases ht : TG.ancestor k v with
    | none =>
      simp only [ht, Option.bind_none] at hk
      cases hk
    | some t =>
      have hp : TG.parent t = some u := by simpa only [ht, Option.bind_some] using hk
      have hc : t ∈ TG.children u := by
        classical
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
      exact le_trans TS (ih t ht) (hedge u t hc)

private theorem lca_reconciliation {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S) (M : G → S)
    (hM : IsLCAReconciliation TG TS lab M) : IsReconciliation TG TS lab M := by
  refine ⟨hM.1, monotone_of_children TG TS M ?_⟩
  intro u c hc
  exact (hM.2 u (child_internal TG hc)).1 c hc

/-- **Optimality of the LCA reconciliation** (Wu and Zhang 2011, Corollary 4): for rooted binary
trees `TG`, `TS` with gene leaf labels `lab` mapping gene leaves to species leaves, the LCA
reconciliation `M` and every reconciliation `f`: `gd(M) ≤ gd(f)`; `gl(M) ≤ gl(f)`, with equality
only if `f = M`; `dc(M) ≤ dc(f)`, with equality only if `f = M`; and hence
`gd(M) + gl(M) ≤ gd(f) + gl(f)`.

Source: Wu and Zhang (2011), Corollary 4. -/
public theorem lca_optimal (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (hlab : ∀ x, TG.IsLeaf x → TS.IsLeaf (lab x)) (M : G → S)
    (hM : IsLCAReconciliation TG TS lab M) (f : G → S) (hf : IsReconciliation TG TS lab f) :
    gd TG TS M ≤ gd TG TS f ∧
      (gl TG TS M ≤ gl TG TS f ∧ (gl TG TS f = gl TG TS M → f = M)) ∧
      (dc TG TS M ≤ dc TG TS f ∧ (dc TG TS f = dc TG TS M → f = M)) ∧
      gd TG TS M + gl TG TS M ≤ gd TG TS f + gl TG TS f
    := by
  have hle := lca_le TG TS lab M f hM hf
  by_cases hfM : f = M
  · subst hfM
    exact ⟨le_rfl, ⟨le_rfl, fun _ => rfl⟩, ⟨le_rfl, fun _ => rfl⟩, le_rfl⟩
  · obtain ⟨hgd, hgl, hdc⟩ := costs_lt_of_le TG TS lab hlab f M hf
      (lca_reconciliation TG TS lab M hM) hle (Ne.symm hfM)
    exact ⟨hgd, ⟨hgl.le, fun h => absurd h hgl.ne'⟩, ⟨hdc.le, fun h => absurd h hdc.ne'⟩,
      add_le_add hgd hgl.le⟩

end WantedExt.Biology.ComputationalBiology.LCAReconciliationWanted
