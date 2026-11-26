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
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Lattice.Nat

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Domains.Biology.ComputationalBiology.LCAReconciliationCostsLtOfLe

/-!
# Optimality of LCA reconciliation

This module defines rooted binary trees, reconciliations and their duplication, loss and
deep-coalescence costs, and proves optimality of the LCA reconciliation.

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

open Classical in
private theorem children_eq_pair {V : Type*} [Fintype V] (T : RootedBinTree V)
    {u a b : V} (ha : a ∈ T.children u) (hb : b ∈ T.children u) (hab : a ≠ b) :
    T.children u = {a, b} := by
  classical
  have hcard : (T.children u).card = 2 := by
    rcases T.binary u with h | h
    · have hempty : T.children u = ∅ := Finset.card_eq_zero.mp h
      rw [hempty] at ha
      exact (Finset.notMem_empty a ha).elim
    · exact h
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact ha
    · have : c = b := Finset.mem_singleton.mp hc
      exact this ▸ hb
  · simp only [Finset.card_pair hab, hcard, Nat.le_refl]

private theorem lca_dup_child {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S) (M : G → S)
    (hM : IsLCAReconciliation TG TS lab M) (u : G) (hd : IsDup TG TS M u) :
    ∃ c ∈ TG.children u, M u = M c := by
  classical
  rcases hd.2 with h | ⟨a, ha, b, hb, hab, e, he⟩
  · exact h
  · have hpair := children_eq_pair TG ha hb hab
    have hea := (Finset.mem_filter.mp (Finset.mem_inter.mp he).1).2
    have heb := (Finset.mem_filter.mp (Finset.mem_inter.mp he).2).2
    have hle : TS.Le (M u) e := (hM.2 u hd.1).2 e (by
      intro c hc
      rw [hpair] at hc
      have hchoice : c = a ∨ c = b := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hc
      rcases hchoice with rfl | rfl
      · exact hea.1
      · exact heb.1)
    exact (hea.2.2 (le_antisymm TS hea.2.1 hle)).elim

private theorem dup_of_common_below {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (f : G → S)
    (u : G) (a : S) (hu : ¬ TG.IsLeaf u) (ha : TS.Le a (f u)) (hne : a ≠ f u)
    (hc : ∀ c ∈ TG.children u, TS.Le (f c) (f u))
    (hcomp : ∀ c ∈ TG.children u, TS.Le (f c) a ∨ TS.Le a (f c)) : IsDup TG TS f u := by
  classical
  refine ⟨hu, ?_⟩
  by_cases heq : ∃ c ∈ TG.children u, f u = f c
  · exact Or.inl heq
  · right
    have hcard : (TG.children u).card = 2 := by
      rcases TG.binary u with h | h
      · exact (hu (Finset.card_eq_zero.mp h)).elim
      · exact h
    obtain ⟨c₁, c₂, hnech, hpair⟩ := Finset.card_eq_two.mp hcard
    have h₁ : c₁ ∈ TG.children u := by simp [hpair]
    have h₂ : c₂ ∈ TG.children u := by simp [hpair]
    have h₁ne : f c₁ ≠ f u := by intro h; exact heq ⟨c₁, h₁, h.symm⟩
    have h₂ne : f c₂ ≠ f u := by intro h; exact heq ⟨c₂, h₂, h.symm⟩
    refine ⟨c₁, h₁, c₂, h₂, hnech, ?_⟩
    have make : ∀ e, TS.Le (f c₁) e → TS.Le (f c₂) e →
        TS.Le e (f u) → e ≠ f u →
        (TS.pathEdges (f u) (f c₁) ∩ TS.pathEdges (f u) (f c₂)).Nonempty := by
      intro e he₁ he₂ he hene
      exact ⟨e, Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, he₁, he, hene⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, he₂, he, hene⟩⟩⟩
    rcases hcomp c₁ h₁ with h₁a | ha₁
    · rcases hcomp c₂ h₂ with h₂a | ha₂
      · exact make a h₁a h₂a ha hne
      · exact make (f c₂) (le_trans TS h₁a ha₂) (le_refl TS _) (hc c₂ h₂) h₂ne
    · rcases hcomp c₂ h₂ with h₂a | ha₂
      · exact make (f c₁) (le_refl TS _) (le_trans TS h₂a ha₁) (hc c₁ h₁) h₁ne
      · rcases ancestors_comparable TS ha₁ ha₂ with h₁₂ | h₂₁
        · exact make (f c₂) h₁₂ (le_refl TS _) (hc c₂ h₂) h₂ne
        · exact make (f c₁) (le_refl TS _) h₂₁ (hc c₁ h₁) h₁ne

private theorem duplication_mono {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S) (M f : G → S)
    (hM : IsLCAReconciliation TG TS lab M) (hf : IsReconciliation TG TS lab f)
    (u : G) (hd : IsDup TG TS M u) : IsDup TG TS f u := by
  obtain ⟨c, hc, heq⟩ := lca_dup_child TG TS lab M hM u hd
  have hle := lca_le TG TS lab M f hM hf
  by_cases hu : M u = f u
  · refine ⟨hd.1, Or.inl ⟨c, hc, ?_⟩⟩
    have hcf : TS.Le (f u) (f c) := by rw [← hu, heq]; exact hle c
    exact le_antisymm TS hcf (hf.2 c u (child_le TG hc))
  · apply dup_of_common_below TG TS f u (M u) hd.1 (hle u) hu
    · intro d hd
      exact hf.2 d u (child_le TG hd)
    · intro d hdc
      exact ancestors_comparable TS (hle d) ((hM.2 u hd.1).1 d hdc)

private theorem gd_mono {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S) (M f : G → S)
    (hM : IsLCAReconciliation TG TS lab M) (hf : IsReconciliation TG TS lab f) :
    gd TG TS M ≤ gd TG TS f := by
  classical
  apply Finset.sum_le_sum
  intro u _
  unfold dupIndicator
  by_cases hd : IsDup TG TS M u
  · simp only [hd, duplication_mono TG TS lab M f hM hf u hd, ↓reduceIte, Int.le_refl]
  · rw [ite_eq_right hd]
    split_ifs <;> omega

private theorem dist_depth {V : Type*} [Fintype V] (T : RootedBinTree V)
    {v u : V} (h : T.Le v u) : depth T v = T.dist u v + depth T u := by
  obtain ⟨k, hk⟩ := h
  exact depth_of_ancestor T v u (T.dist u v)
    (Nat.sInf_mem (s := {k | T.ancestor k v = some u}) ⟨k, hk⟩)

private theorem sum_children {V : Type*} [Fintype V] (T : RootedBinTree V)
    (g : V → V → ℤ) : (∑ u, ∑ c ∈ T.children u, g u c) =
      ∑ c, match T.parent c with | none => 0 | some u => g u c := by
  classical
  simp only [RootedBinTree.children, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  cases hp : T.parent c with
  | none => simp
  | some p => simp

private theorem sum_children_child {V : Type*} [Fintype V] (T : RootedBinTree V)
    (w : V → ℤ) : (∑ u, ∑ c ∈ T.children u, w c) = (∑ c, w c) - w T.root := by
  classical
  rw [sum_children]
  have hpoint : ∀ c, (match T.parent c with | none => (0 : ℤ) | some _ => w c) =
      w c - if c = T.root then w c else 0 := by
    intro c
    by_cases hc : c = T.root
    · subst c
      simp only [T.parent_root, ↓reduceIte, sub_self]
    · have hs := T.parent_isSome c hc
      cases hp : T.parent c with
      | none => simp only [hp, Option.isSome_none, Bool.false_eq_true] at hs
      | some p => simp only [ite_eq_right hc, sub_zero]
  simp only [hpoint, Finset.sum_sub_distrib]
  simp

private theorem sum_children_parent {V : Type*} [Fintype V] (T : RootedBinTree V)
    (w : V → ℤ) (hw : ∀ u, T.IsLeaf u → w u = 0) :
    (∑ u, ∑ _ ∈ T.children u, w u) = 2 * ∑ u, w u := by
  classical
  have hpoint : ∀ u, (∑ _ ∈ T.children u, w u) = 2 * w u := by
    intro u
    by_cases hu : T.IsLeaf u
    · have hwzero := hw u hu
      change T.children u = ∅ at hu
      rw [hu, Finset.sum_empty, hwzero]
      simp
    · have hcard : (T.children u).card = 2 := by
        rcases T.binary u with h | h
        · exact (hu (Finset.card_eq_zero.mp h)).elim
        · exact h
      simp only [Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_ofNat]
  simp only [hpoint, Finset.mul_sum]

private theorem balance {V : Type*} [Fintype V] (T : RootedBinTree V)
    (w : V → ℤ) (hw : ∀ u, T.IsLeaf u → w u = 0) :
    (∑ u, ∑ c ∈ T.children u, (w u - w c)) = (∑ u, w u) + w T.root := by
  simp only [Finset.sum_sub_distrib]
  rw [sum_children_parent T w hw, sum_children_child]
  omega

private noncomputable def depthGap {G S : Type*} [Fintype G] [Fintype S]
    (TS : RootedBinTree S) (M f : G → S) (u : G) : ℤ :=
  (depth TS (M u) : ℤ) - depth TS (f u)

private theorem depthGap_nonneg {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S) (M f : G → S)
    (hM : IsLCAReconciliation TG TS lab M) (hf : IsReconciliation TG TS lab f) (u : G) :
    0 ≤ depthGap TS M f u := by
  have h := le_depth TS (lca_le TG TS lab M f hM hf u)
  unfold depthGap
  omega

private theorem depthGap_leaf {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S) (M f : G → S)
    (hM : IsLCAReconciliation TG TS lab M) (hf : IsReconciliation TG TS lab f)
    (u : G) (hu : TG.IsLeaf u) : depthGap TS M f u = 0 := by
  unfold depthGap
  rw [hM.1 u hu, hf.1 u hu, sub_self]

private theorem gl_difference {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S) (M f : G → S)
    (hM : IsLCAReconciliation TG TS lab M) (hf : IsReconciliation TG TS lab f) :
    gl TG TS f - gl TG TS M = (∑ u, depthGap TS M f u) + depthGap TS M f TG.root +
      2 * (gd TG TS f - gd TG TS M) := by
  classical
  have hMr := lca_reconciliation TG TS lab M hM
  have hpoint : ∀ u, lossAt TG TS f u - lossAt TG TS M u =
      (∑ c ∈ TG.children u, (depthGap TS M f u - depthGap TS M f c)) +
        2 * (dupIndicator TG TS f u - dupIndicator TG TS M u) := by
    intro u
    by_cases hu : TG.IsLeaf u
    · have hdup : ¬ IsDup TG TS f u ∧ ¬ IsDup TG TS M u :=
        ⟨fun h => h.1 hu, fun h => h.1 hu⟩
      have hempty : TG.children u = ∅ := hu
      simp only [lossAt, hu, ↓reduceIte, dupIndicator, hdup.1, hdup.2,
        hempty, Finset.sum_empty]
      omega
    · have hdist : ∀ c ∈ TG.children u,
          (TS.dist (f u) (f c) : ℤ) - TS.dist (M u) (M c) =
            depthGap TS M f u - depthGap TS M f c := by
        intro c hc
        have h₁ := dist_depth TS (hf.2 c u (child_le TG hc))
        have h₂ := dist_depth TS (hMr.2 c u (child_le TG hc))
        unfold depthGap
        omega
      simp only [lossAt, hu, ↓reduceIte]
      have hsum := Finset.sum_congr rfl hdist
      rw [Finset.sum_sub_distrib] at hsum
      omega
  unfold gl gd
  rw [← Finset.sum_sub_distrib]
  simp only [hpoint, Finset.sum_add_distrib]
  rw [balance TG (depthGap TS M f) (depthGap_leaf TG TS lab M f hM hf)]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]

private theorem gl_mono_unique {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (_hlab : ∀ x, TG.IsLeaf x → TS.IsLeaf (lab x)) (M f : G → S)
    (hM : IsLCAReconciliation TG TS lab M) (hf : IsReconciliation TG TS lab f) :
    gl TG TS M ≤ gl TG TS f ∧ (gl TG TS f = gl TG TS M → f = M) := by
  have hgd := gd_mono TG TS lab M f hM hf
  have hdiff := gl_difference TG TS lab M f hM hf
  have hn := depthGap_nonneg TG TS lab M f hM hf
  have hsum : 0 ≤ ∑ u, depthGap TS M f u := Finset.sum_nonneg (fun u _ => hn u)
  constructor
  · have hr := hn TG.root
    omega
  · intro heq
    have hr := hn TG.root
    have hz : ∑ u, depthGap TS M f u = 0 := by omega
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => hn u)).mp hz
    funext u
    have hu := hzero u (Finset.mem_univ u)
    have hdepth : depth TS (M u) = depth TS (f u) := by unfold depthGap at hu; omega
    exact (eq_of_le_depth TS (lca_le TG TS lab M f hM hf u) hdepth).symm

open Classical in
private noncomputable def below {G S : Type*} [Fintype G] [Fintype S]
    (TS : RootedBinTree S) (f : G → S) (e : S) (u : G) : ℤ :=
  if TS.Le (f u) e then 1 else 0

private noncomputable def belowGap {G S : Type*} [Fintype G] [Fintype S]
    (TS : RootedBinTree S) (M f : G → S) (e : S) (u : G) : ℤ :=
  below TS M e u - below TS f e u

private theorem belowGap_nonneg {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S) (M f : G → S)
    (hM : IsLCAReconciliation TG TS lab M) (hf : IsReconciliation TG TS lab f)
    (e : S) (u : G) : 0 ≤ belowGap TS M f e u := by
  classical
  have hle := lca_le TG TS lab M f hM hf u
  have himp : TS.Le (f u) e → TS.Le (M u) e := le_trans TS hle
  unfold belowGap below
  split_ifs <;> simp_all

private theorem belowGap_leaf {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S) (M f : G → S)
    (hM : IsLCAReconciliation TG TS lab M) (hf : IsReconciliation TG TS lab f)
    (e : S) (u : G) (hu : TG.IsLeaf u) : belowGap TS M f e u = 0 := by
  unfold belowGap below
  rw [hM.1 u hu, hf.1 u hu, sub_self]

private theorem path_iff {S : Type*} [Fintype S] (TS : RootedBinTree S)
    {a b e : S} (h : TS.Le b a) : e ∈ TS.pathEdges a b ↔ TS.Le b e ∧ ¬ TS.Le a e := by
  classical
  constructor
  · intro he
    have hp := (Finset.mem_filter.mp he).2
    exact ⟨hp.1, fun ha => hp.2.2 (le_antisymm TS hp.2.1 ha)⟩
  · rintro ⟨he, hne⟩
    rcases ancestors_comparable TS he h with hea | hae
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, hea, fun h => hne (h ▸ le_refl TS a)⟩
    · exact (hne hae).elim

open Classical in
private noncomputable def lineages {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (f : G → S) (e : S) : ℕ :=
  (Finset.univ.filter fun c : G => ∃ u, TG.parent c = some u ∧
    e ∈ TS.pathEdges (f u) (f c)).card

private theorem lineages_sum {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S) (f : G → S)
    (hf : IsReconciliation TG TS lab f) (e : S) :
    (lineages TG TS f e : ℤ) = ∑ u, ∑ c ∈ TG.children u,
      (below TS f e c - below TS f e u) := by
  classical
  simp only [lineages, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  rw [sum_children]
  apply Finset.sum_congr rfl
  intro c _
  cases hp : TG.parent c with
  | none => simp
  | some u =>
    have hc : c ∈ TG.children u := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
    have hle := hf.2 c u (child_le TG hc)
    have hpred : (∃ p, some u = some p ∧ e ∈ TS.pathEdges (f p) (f c)) ↔
        e ∈ TS.pathEdges (f u) (f c) := by simp
    simp only [hpred, path_iff TS hle]
    have himp : TS.Le (f u) e → TS.Le (f c) e := le_trans TS hle
    unfold below
    split_ifs <;> simp_all

private theorem lineages_difference {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S) (M f : G → S)
    (hM : IsLCAReconciliation TG TS lab M) (hf : IsReconciliation TG TS lab f) (e : S) :
    (lineages TG TS f e : ℤ) - lineages TG TS M e =
      (∑ u, belowGap TS M f e u) + belowGap TS M f e TG.root := by
  rw [lineages_sum TG TS lab f hf, lineages_sum TG TS lab M (lca_reconciliation TG TS lab M hM)]
  rw [← Finset.sum_sub_distrib]
  have hpoint : ∀ u, (∑ c ∈ TG.children u, (below TS f e c - below TS f e u)) -
      (∑ c ∈ TG.children u, (below TS M e c - below TS M e u)) =
        ∑ c ∈ TG.children u, (belowGap TS M f e u - belowGap TS M f e c) := by
    intro u
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    unfold belowGap
    omega
  simp only [hpoint]
  exact balance TG (belowGap TS M f e) (belowGap_leaf TG TS lab M f hM hf e)

private theorem extra_mono {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S) (M f : G → S)
    (hM : IsLCAReconciliation TG TS lab M) (hf : IsReconciliation TG TS lab f) (e : S) :
    extraLineages TG TS M e ≤ extraLineages TG TS f e := by
  have h := lineages_difference TG TS lab M f hM hf e
  have hn := belowGap_nonneg TG TS lab M f hM hf e
  have hs : 0 ≤ ∑ u, belowGap TS M f e u := Finset.sum_nonneg (fun u _ => hn u)
  have hr := hn TG.root
  change lineages TG TS M e - 1 ≤ lineages TG TS f e - 1
  omega

private theorem crossing_exists {V : Type*} [Fintype V] (T : RootedBinTree V)
    (P : V → Prop) {v u : V} (h : T.Le v u) (hv : P v) (hu : ¬ P u) :
    ∃ c p, T.parent c = some p ∧ P c ∧ ¬ P p := by
  obtain ⟨k, hk⟩ := h
  induction k generalizing u with
  | zero =>
    have heq : v = u := Option.some.inj hk
    exact (hu (heq ▸ hv)).elim
  | succ k ih =>
    rw [ancestor_succ] at hk
    cases ht : T.ancestor k v with
    | none => simp only [ht, Option.bind_none] at hk; cases hk
    | some t =>
      have hp : T.parent t = some u := by simpa only [ht, Option.bind_some] using hk
      by_cases hpt : P t
      · exact ⟨t, u, hp, hpt, hu⟩
      · exact ih hpt ht

private theorem positive_lineages {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S) (M : G → S)
    (hM : IsLCAReconciliation TG TS lab M) (e : S) (u : G)
    (hu : TS.Le (M u) e) (hr : ¬ TS.Le (M TG.root) e) : 0 < lineages TG TS M e := by
  classical
  have hroot : TG.Le u TG.root := TG.reach_root u
  obtain ⟨c, p, hp, hc, hnp⟩ := crossing_exists TG (fun v => TS.Le (M v) e) hroot hu hr
  have hchild : c ∈ TG.children p := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
  apply Finset.card_pos.mpr
  refine ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, hp, ?_⟩⟩
  exact (path_iff TS ((lca_reconciliation TG TS lab M hM).2 c p (child_le TG hchild))).mpr ⟨hc, hnp⟩

private theorem extra_strict {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S) (M f : G → S)
    (hM : IsLCAReconciliation TG TS lab M) (hf : IsReconciliation TG TS lab f)
    (e : S) (u : G) (hu : TS.Le (M u) e) (hfu : ¬ TS.Le (f u) e) :
    extraLineages TG TS M e < extraLineages TG TS f e := by
  classical
  have hdiff := lineages_difference TG TS lab M f hM hf e
  have hn := belowGap_nonneg TG TS lab M f hM hf e
  have hs : 0 ≤ ∑ v, belowGap TS M f e v := Finset.sum_nonneg (fun v _ => hn v)
  have huGap : belowGap TS M f e u = 1 := by
    simp only [belowGap, below, hu, hfu, ↓reduceIte, sub_zero]
  have hsum : 1 ≤ ∑ v, belowGap TS M f e v := by
    rw [← huGap]
    exact Finset.single_le_sum (fun v _ => hn v) (Finset.mem_univ u)
  change lineages TG TS M e - 1 < lineages TG TS f e - 1
  by_cases hroot : TS.Le (M TG.root) e
  · have hfroot : ¬ TS.Le (f TG.root) e := by
      intro hfr
      exact hfu (le_trans TS (hf.2 u TG.root (TG.reach_root u)) hfr)
    have hrootGap : belowGap TS M f e TG.root = 1 := by
      simp only [belowGap, below, hroot, hfroot, ↓reduceIte, sub_zero]
    omega
  · have hk := positive_lineages TG TS lab M hM e u hu hroot
    have hr := hn TG.root
    omega

private theorem dc_mono_unique {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S) (M f : G → S)
    (hM : IsLCAReconciliation TG TS lab M) (hf : IsReconciliation TG TS lab f) :
    dc TG TS M ≤ dc TG TS f ∧ (dc TG TS f = dc TG TS M → f = M) := by
  classical
  have hmono := extra_mono TG TS lab M f hM hf
  constructor
  · exact Finset.sum_le_sum (fun e _ => hmono e)
  · intro heq
    by_contra hne
    obtain ⟨u, hu⟩ : ∃ u, f u ≠ M u := by
      by_contra h
      apply hne
      funext u
      by_contra hu
      exact h ⟨u, hu⟩
    have hle := lca_le TG TS lab M f hM hf u
    have hnot : ¬ TS.Le (f u) (M u) := by
      intro h
      exact hu (le_antisymm TS h hle)
    have hnonroot : M u ≠ TS.root := by
      intro h
      exact hnot (h ▸ TS.reach_root (f u))
    have hstrict := extra_strict TG TS lab M f hM hf (M u) u (le_refl TS _) hnot
    have hcost : dc TG TS M < dc TG TS f :=
      Finset.sum_lt_sum (fun e _ => hmono e)
        ⟨M u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnonroot⟩, hstrict⟩
    omega

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
  have hgd := gd_mono TG TS lab M f hM hf
  have hgl := gl_mono_unique TG TS lab hlab M f hM hf
  have hdc := dc_mono_unique TG TS lab M f hM hf
  exact ⟨hgd, hgl, hdc, add_le_add hgd hgl.1⟩

end WantedExt.Biology.ComputationalBiology.LCAReconciliationWanted
