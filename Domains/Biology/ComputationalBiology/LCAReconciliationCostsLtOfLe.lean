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
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Function.Iterate

/-!
# Monotonicity of reconciliation costs

Rooted binary trees, reconciliations, their duplication, loss, and deep-coalescence costs,
and monotonicity of these costs under pointwise movement toward ancestors.

Source: T. Wu and L. Zhang, "Structural properties of the reconciliation space and their
applications in enumerating nearly-optimal reconciliations between a gene tree and a species tree",
BMC Bioinformatics 12 (Suppl 9) (2011) S7, doi:10.1186/1471-2105-12-S9-S7, definitions (1)–(3),
Theorem 2 and Corollary 4.
-/

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

/-- The `k`-th ancestor of `v` (`some v` for `k = 0`; `none` above the root). -/
def ancestor {V : Type*} [Fintype V] (T : RootedBinTree V) (k : ℕ) (v : V) : Option V :=
  Nat.iterate (fun o => Option.bind o T.parent) k (some v)

/-- `T.Le v u`: `u` lies on the path from the root to `v` (`v ≤ u` in the source's notation), i.e.
`u` is an ancestor of `v` or `u = v`. -/
def Le {V : Type*} [Fintype V] (T : RootedBinTree V) (v u : V) : Prop :=
  ∃ k, T.ancestor k v = some u

open Classical in
/-- The children of `u`. -/
noncomputable def children {V : Type*} [Fintype V] (T : RootedBinTree V) (u : V) : Finset V :=
  Finset.univ.filter fun c => T.parent c = some u

/-- `x` is a leaf: it has no children. -/
def IsLeaf {V : Type*} [Fintype V] (T : RootedBinTree V) (x : V) : Prop :=
  T.children x = ∅

/-- The number of edges `d(u, v)` on the path from `v` up to its ancestor-or-self `u`. -/
noncomputable def dist {V : Type*} [Fintype V] (T : RootedBinTree V) (u v : V) : ℕ :=
  sInf {k | T.ancestor k v = some u}

open Classical in
/-- The edges of the path `P(u, v)` from `u` down to `v`, each named by its lower endpoint: the
vertices `c` with `v ≤ c`, `c ≤ u` and `c ≠ u`. -/
noncomputable def pathEdges {V : Type*} [Fintype V] (T : RootedBinTree V) (u v : V) : Finset V :=
  Finset.univ.filter fun c => T.Le v c ∧ T.Le c u ∧ c ≠ u

end RootedBinTree

/-- `f` is a **reconciliation** of the gene tree `TG` (leaf labels `lab`, gene leaves to species
leaves) with the species tree `TS`: leaf-preserving and order-preserving. -/
def IsReconciliation {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S) (f : G → S) :
    Prop :=
  (∀ x, TG.IsLeaf x → f x = lab x) ∧ ∀ v u, TG.Le v u → TS.Le (f v) (f u)

open Classical in
/-- `f` has a **duplication** at `u` (`δ_f(u) = 1`): `u` is internal and (D-i) `f(u) = f(c)` for a
child `c`, or (D-ii) the paths from `f(u)` to the images of two distinct children share an edge. -/
def IsDup {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (f : G → S) (u : G) : Prop :=
  ¬ TG.IsLeaf u ∧ ((∃ c ∈ TG.children u, f u = f c) ∨
    ∃ c₁ ∈ TG.children u, ∃ c₂ ∈ TG.children u, c₁ ≠ c₂ ∧
      (TS.pathEdges (f u) (f c₁) ∩ TS.pathEdges (f u) (f c₂)).Nonempty)

open Classical in
/-- The duplication indicator `δ_f(u) ∈ {0, 1}`: `1` if `f` has a duplication at `u`, else `0`. -/
noncomputable def dupIndicator {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (f : G → S)
    (u : G) : ℤ :=
  if IsDup TG TS f u then 1 else 0

/-- The **gene-duplication cost** `gd(f) = ∑_u δ_f(u)`. -/
noncomputable def gd {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (f : G → S) : ℤ :=
  ∑ u, dupIndicator TG TS f u

open Classical in
/-- The **loss count** at `u`: `∑_{c child of u} d(f(u), f(c)) + 2 (δ_f(u) - 1)` for internal `u`
and `0` for leaves. -/
noncomputable def lossAt {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (f : G → S) (u : G) : ℤ :=
  if TG.IsLeaf u then 0
  else (∑ c ∈ TG.children u, (TS.dist (f u) (f c) : ℤ)) + 2 * (dupIndicator TG TS f u - 1)

/-- The **gene-loss cost** `gl(f) = ∑_u l_f(u)`. -/
noncomputable def gl {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (f : G → S) : ℤ :=
  ∑ u, lossAt TG TS f u

open Classical in
/-- `τ_f(e)`: one less than the number of gene edges `(parent c, c)` whose image path contains the
species edge `e`, when that number is at least `2`, and `0` otherwise. -/
noncomputable def extraLineages {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (f : G → S)
    (e : S) : ℕ :=
  (Finset.univ.filter fun c : G => ∃ u, TG.parent c = some u ∧
    e ∈ TS.pathEdges (f u) (f c)).card - 1

open Classical in
/-- The **deep-coalescence cost** `dc(f) = ∑_e τ_f(e)` over the edges `e` of the species tree (the
non-root vertices). -/
noncomputable def dc {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (f : G → S) : ℕ :=
  ∑ e ∈ Finset.univ.filter (· ≠ TS.root), extraLineages TG TS f e

private theorem iterate_none {V : Type*} [Fintype V] (T : RootedBinTree V) (k : ℕ) :
    Nat.iterate (fun o => Option.bind o T.parent) k none = none :=
  Function.iterate_fixed rfl k

private theorem ancestor_root_succ {V : Type*} [Fintype V] (T : RootedBinTree V) (k : ℕ) :
    T.ancestor (k + 1) T.root = none := by
  simpa only [RootedBinTree.ancestor, Function.iterate_succ_apply, Option.bind_some,
    T.parent_root] using iterate_none T k

private theorem ancestor_add {V : Type*} [Fintype V] (T : RootedBinTree V)
    (m n : ℕ) (v : V) :
    T.ancestor (m + n) v = Nat.iterate (fun o => Option.bind o T.parent) m
      (T.ancestor n v) :=
  Function.iterate_add_apply _ m n _

private theorem ancestor_cycle {V : Type*} [Fintype V] (T : RootedBinTree V)
    (v : V) (k : ℕ) (h : T.ancestor k v = some v) : k = 0 := by
  obtain ⟨n, hn⟩ := T.reach_root v
  change T.ancestor n v = some T.root at hn
  have he : T.ancestor k T.root = some T.root := by
    calc
      T.ancestor k T.root = T.ancestor (k + n) v := by rw [ancestor_add, hn]; rfl
      _ = T.ancestor (n + k) v := by rw [Nat.add_comm]
      _ = some T.root := by rw [ancestor_add, h]; exact hn
  cases k with
  | zero => rfl
  | succ k => rw [ancestor_root_succ] at he; cases he

private theorem ancestor_unique {V : Type*} [Fintype V] (T : RootedBinTree V)
    (v u : V) (m n : ℕ) (hm : T.ancestor m v = some u)
    (hn : T.ancestor n v = some u) : m = n := by
  have aux (a b : ℕ) (ha : T.ancestor a v = some u)
      (hb : T.ancestor b v = some u) (hab : a ≤ b) : a = b := by
    have hc : T.ancestor (b - a) u = some u := by
      have he := ancestor_add T (b - a) a v
      rw [Nat.sub_add_cancel hab, ha, hb] at he
      exact he.symm
    have hz := ancestor_cycle T u (b - a) hc
    omega
  rcases le_total m n with h | h
  · exact aux m n hm hn h
  · exact (aux n m hn hm h).symm

private theorem le_refl {V : Type*} [Fintype V] (T : RootedBinTree V) (v : V) :
    T.Le v v :=
  ⟨0, rfl⟩

private theorem le_trans {V : Type*} [Fintype V] (T : RootedBinTree V)
    {a b c : V} (hab : T.Le a b) (hbc : T.Le b c) : T.Le a c := by
  obtain ⟨m, hm⟩ := hab
  obtain ⟨n, hn⟩ := hbc
  refine ⟨n + m, ?_⟩
  rw [ancestor_add, hm]
  exact hn

private theorem le_antisymm {V : Type*} [Fintype V] (T : RootedBinTree V)
    {a b : V} (hab : T.Le a b) (hba : T.Le b a) : a = b := by
  obtain ⟨m, hm⟩ := hab
  obtain ⟨n, hn⟩ := hba
  have hc : T.ancestor (n + m) a = some a := by rw [ancestor_add, hm]; exact hn
  have hz := ancestor_cycle T a (n + m) hc
  have hm0 : m = 0 := by omega
  simpa only [hm0, RootedBinTree.ancestor, Function.iterate_zero_apply,
    Option.some.injEq] using hm

private theorem le_comparable {V : Type*} [Fintype V] (T : RootedBinTree V)
    {a b c : V} (hab : T.Le a b) (hac : T.Le a c) : T.Le b c ∨ T.Le c b := by
  obtain ⟨m, hm⟩ := hab
  obtain ⟨n, hn⟩ := hac
  rcases le_total m n with h | h
  · left
    refine ⟨n - m, ?_⟩
    have he := ancestor_add T (n - m) m a
    rw [Nat.sub_add_cancel h, hm, hn] at he
    exact he.symm
  · right
    refine ⟨m - n, ?_⟩
    have he := ancestor_add T (m - n) n a
    rw [Nat.sub_add_cancel h, hn, hm] at he
    exact he.symm

private theorem dist_eq {V : Type*} [Fintype V] (T : RootedBinTree V)
    {u v : V} {k : ℕ} (h : T.ancestor k v = some u) : T.dist u v = k := by
  have hm : T.ancestor (T.dist u v) v = some u :=
    Nat.sInf_mem (s := {n | T.ancestor n v = some u}) ⟨k, h⟩
  exact ancestor_unique T v u _ k hm h

private theorem dist_spec {V : Type*} [Fintype V] (T : RootedBinTree V)
    {v u : V} (h : T.Le v u) : T.ancestor (T.dist u v) v = some u :=
  Nat.sInf_mem (s := {n | T.ancestor n v = some u}) h

private theorem dist_add {V : Type*} [Fintype V] (T : RootedBinTree V)
    {a b c : V} (hab : T.Le a b) (hbc : T.Le b c) :
    T.dist c a = T.dist c b + T.dist b a := by
  apply dist_eq T
  rw [ancestor_add, dist_spec T hab]
  exact dist_spec T hbc

private theorem parent_le {V : Type*} [Fintype V] (T : RootedBinTree V)
    {v u : V} (h : T.parent v = some u) : T.Le v u :=
  ⟨1, h⟩

private theorem parent_ne {V : Type*} [Fintype V] (T : RootedBinTree V)
    {v u : V} (h : T.parent v = some u) : v ≠ u := by
  intro he
  have hc : T.ancestor 1 v = some v := by simpa [RootedBinTree.ancestor, he] using h
  have := ancestor_cycle T v 1 hc
  omega

private theorem le_parent {V : Type*} [Fintype V] (T : RootedBinTree V)
    {v p u : V} (hp : T.parent v = some p) (h : T.Le v u) (hne : v ≠ u) :
    T.Le p u := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero => exact False.elim (hne (Option.some.inj hk))
  | succ k =>
    refine ⟨k, ?_⟩
    simpa only [RootedBinTree.ancestor, Function.iterate_succ_apply,
      Option.bind_some, hp] using hk

private theorem children_mem {V : Type*} [Fintype V] (T : RootedBinTree V)
    (u c : V) : c ∈ T.children u ↔ T.parent c = some u := by
  classical
  simp [RootedBinTree.children]

private theorem children_card {V : Type*} [Fintype V] (T : RootedBinTree V)
    {u : V} (h : ¬ T.IsLeaf u) : (T.children u).card = 2 := by
  rcases T.binary u with he | he
  · exact False.elim (h (Finset.card_eq_zero.mp he))
  · exact he

private theorem path_mem {V : Type*} [Fintype V] (T : RootedBinTree V)
    (u v e : V) : e ∈ T.pathEdges u v ↔ T.Le v e ∧ T.Le e u ∧ e ≠ u := by
  classical
  simp [RootedBinTree.pathEdges]

open Classical in
private theorem path_parent_top {V : Type*} [Fintype V] (T : RootedBinTree V)
    {p s v : V} (hp : T.parent s = some p) (hv : T.Le v s) :
    T.pathEdges p v = insert s (T.pathEdges s v) := by
  classical
  ext e
  simp only [Finset.mem_insert, path_mem]
  constructor
  · rintro ⟨hve, hep, hne⟩
    by_cases hes : e = s
    · exact Or.inl hes
    · right
      refine ⟨hve, ?_, hes⟩
      rcases le_comparable T hv hve with hse | hes'
      · have hpe := le_parent T hp hse (Ne.symm hes)
        exact False.elim (hne (le_antisymm T hep hpe))
      · exact hes'
  · rintro (rfl | ⟨hve, hes, hne⟩)
    · exact ⟨hv, parent_le T hp, parent_ne T hp⟩
    · refine ⟨hve, le_trans T hes (parent_le T hp), ?_⟩
      intro he
      have hps : T.Le p s := he ▸ hes
      exact parent_ne T hp (le_antisymm T (parent_le T hp) hps)

open Classical in
private theorem path_parent_bottom {V : Type*} [Fintype V] (T : RootedBinTree V)
    {a p s : V} (hp : T.parent s = some p) (ha : T.Le p a) :
    T.pathEdges a s = insert s (T.pathEdges a p) := by
  classical
  ext e
  simp only [Finset.mem_insert, path_mem]
  constructor
  · rintro ⟨hse, hea, hne⟩
    by_cases hes : e = s
    · exact Or.inl hes
    · exact Or.inr ⟨le_parent T hp hse (Ne.symm hes), hea, hne⟩
  · rintro (rfl | ⟨hpe, hea, hne⟩)
    · refine ⟨le_refl T _, le_trans T (parent_le T hp) ha, ?_⟩
      intro he
      exact parent_ne T hp (le_antisymm T (parent_le T hp) (he ▸ ha))
    · exact ⟨le_trans T (parent_le T hp) hpe, hea, hne⟩

private theorem dist_parent_top {V : Type*} [Fintype V] (T : RootedBinTree V)
    {p s v : V} (hp : T.parent s = some p) (hv : T.Le v s) :
    T.dist p v = T.dist s v + 1 := by
  rw [dist_add T hv (parent_le T hp),
    dist_eq T (u := p) (v := s) (k := 1) (by simpa [RootedBinTree.ancestor] using hp)]
  omega

private theorem dist_parent_bottom {V : Type*} [Fintype V] (T : RootedBinTree V)
    {a p s : V} (hp : T.parent s = some p) (ha : T.Le p a) :
    T.dist a s = T.dist a p + 1 := by
  rw [dist_add T (parent_le T hp) ha,
    dist_eq T (u := p) (v := s) (k := 1) (by simpa [RootedBinTree.ancestor] using hp)]

private theorem move_dup {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (f g : G → S) (u : G) (p : S) (hp : TS.parent (f u) = some p)
    (hf : IsReconciliation TG TS lab f) (hg : IsReconciliation TG TS lab g)
    (hgu : g u = p) (ho : ∀ v, v ≠ u → g v = f v) (hi : ¬ TG.IsLeaf u)
    (v : G) (hd : IsDup TG TS f v) : IsDup TG TS g v := by
  classical
  by_cases hv : v = u
  · subst v
    obtain ⟨c₁, c₂, hc, he⟩ := Finset.card_eq_two.mp (children_card TG hi)
    have hc₁ : c₁ ∈ TG.children u := he ▸ Finset.mem_insert_self _ _
    have hc₂ : c₂ ∈ TG.children u := he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hmem (c : G) (h : c ∈ TG.children u) : f u ∈ TS.pathEdges (g u) (g c) := by
      have hcu := (children_mem TG u c).mp h
      rw [ho c (parent_ne TG hcu), hgu, path_parent_top TS hp (hf.2 c u (parent_le TG hcu))]
      exact Finset.mem_insert_self _ _
    exact ⟨hi, Or.inr ⟨c₁, hc₁, c₂, hc₂, hc,
      f u, Finset.mem_inter.mpr ⟨hmem c₁ hc₁, hmem c₂ hc₂⟩⟩⟩
  · have hgv := ho v hv
    by_cases huc : u ∈ TG.children v
    · have hpa : TS.Le p (f v) := by
        simpa only [hgu, hgv] using hg.2 u v (parent_le TG ((children_mem TG v u).mp huc))
      by_cases hpe : p = f v
      · exact ⟨hd.1, Or.inl ⟨u, huc, by rw [hgv, hgu, hpe]⟩⟩
      · refine ⟨hd.1, ?_⟩
        rcases hd.2 with ⟨c, hc, he⟩ | ⟨c₁, hc₁, c₂, hc₂, hne, e, he⟩
        · by_cases hcu : c = u
          · subst c
            have hback : TS.Le p (f u) := he ▸ hpa
            exact False.elim (parent_ne TS hp (le_antisymm TS (parent_le TS hp) hback))
          · exact Or.inl ⟨c, hc, by rw [hgv, ho c hcu]; exact he⟩
        · have he₁ := (path_mem TS (f v) (f c₁) e).mp (Finset.mem_inter.mp he).1
          have he₂ := (path_mem TS (f v) (f c₂) e).mp (Finset.mem_inter.mp he).2
          by_cases heu : e = f u
          · have hpath (c : G) (hec : TS.Le (f c) e) :
                p ∈ TS.pathEdges (g v) (g c) := by
              apply (path_mem TS _ _ _).mpr
              refine ⟨?_, by simpa only [hgv] using hpa, by simpa only [hgv] using hpe⟩
              by_cases hcu : c = u
              · simpa only [hcu, hgu] using le_refl TS p
              · rw [ho c hcu]
                exact le_trans TS (heu ▸ hec) (parent_le TS hp)
            exact Or.inr ⟨c₁, hc₁, c₂, hc₂, hne, p,
              Finset.mem_inter.mpr ⟨hpath c₁ he₁.1, hpath c₂ he₂.1⟩⟩
          · have hpath (c : G) (hec : TS.Le (f c) e) (hea : TS.Le e (f v))
                (hne : e ≠ f v) : e ∈ TS.pathEdges (g v) (g c) := by
              apply (path_mem TS _ _ _).mpr
              refine ⟨?_, by simpa only [hgv] using hea, by simpa only [hgv] using hne⟩
              by_cases hcu : c = u
              · rw [hcu, hgu]
                exact le_parent TS hp (hcu ▸ hec) (Ne.symm heu)
              · simpa only [ho c hcu] using hec
            exact Or.inr ⟨c₁, hc₁, c₂, hc₂, hne, e,
              Finset.mem_inter.mpr ⟨hpath c₁ he₁.1 he₁.2.1 he₁.2.2,
                hpath c₂ he₂.1 he₂.2.1 he₂.2.2⟩⟩
    · have hsame (c : G) (hc : c ∈ TG.children v) : g c = f c :=
        ho c (fun he => huc (he ▸ hc))
      refine ⟨hd.1, ?_⟩
      rcases hd.2 with ⟨c, hc, he⟩ | ⟨c₁, hc₁, c₂, hc₂, hne, he⟩
      · exact Or.inl ⟨c, hc, by rw [hgv, hsame c hc]; exact he⟩
      · exact Or.inr ⟨c₁, hc₁, c₂, hc₂, hne, by
          simpa only [hgv, hsame c₁ hc₁, hsame c₂ hc₂] using he⟩

private theorem move_indicator {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (f g : G → S) (u : G) (p : S) (hp : TS.parent (f u) = some p)
    (hf : IsReconciliation TG TS lab f) (hg : IsReconciliation TG TS lab g)
    (hgu : g u = p) (ho : ∀ v, v ≠ u → g v = f v) (hi : ¬ TG.IsLeaf u)
    (v : G) : dupIndicator TG TS f v ≤ dupIndicator TG TS g v := by
  classical
  unfold dupIndicator
  by_cases hd : IsDup TG TS f v
  · rw [ite_eq_left hd, ite_eq_left (move_dup TG TS lab f g u p hp hf hg hgu ho hi v hd)]
  · rw [ite_eq_right hd]
    split <;> omega

private theorem move_gd {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (f g : G → S) (u : G) (p : S) (hp : TS.parent (f u) = some p)
    (hf : IsReconciliation TG TS lab f) (hg : IsReconciliation TG TS lab g)
    (hgu : g u = p) (ho : ∀ v, v ≠ u → g v = f v) (hi : ¬ TG.IsLeaf u) :
    gd TG TS f ≤ gd TG TS g :=
  Finset.sum_le_sum fun v _ => move_indicator TG TS lab f g u p hp hf hg hgu ho hi v

open Classical in
private theorem move_dist_sum {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (f g : G → S) (u : G) (p : S) (hp : TS.parent (f u) = some p)
    (hf : IsReconciliation TG TS lab f) (hg : IsReconciliation TG TS lab g)
    (hgu : g u = p) (ho : ∀ v, v ≠ u → g v = f v) (hi : ¬ TG.IsLeaf u)
    (v : G) :
    (∑ c ∈ TG.children v, (TS.dist (g v) (g c) : ℤ)) =
      (∑ c ∈ TG.children v, (TS.dist (f v) (f c) : ℤ)) +
        (if v = u then 2 else 0) - (if TG.parent u = some v then 1 else 0) := by
  classical
  by_cases hv : v = u
  · subst v
    have hnu : TG.parent u ≠ some u := fun h => parent_ne TG h rfl
    simp only [ite_true, hnu, ite_false, sub_zero]
    calc
      _ = ∑ c ∈ TG.children u, ((TS.dist (f u) (f c) : ℤ) + 1) := by
        apply Finset.sum_congr rfl
        intro c hc
        have hcu := (children_mem TG u c).mp hc
        rw [hgu, ho c (parent_ne TG hcu),
          dist_parent_top TS hp (hf.2 c u (parent_le TG hcu)), Int.natCast_add, Int.natCast_one]
      _ = _ := by rw [Finset.sum_add_distrib]; simp [children_card TG hi]
  · have hgv := ho v hv
    by_cases hpar : TG.parent u = some v
    · have huc := (children_mem TG v u).mpr hpar
      have hpa : TS.Le p (f v) := by
        simpa only [hgu, hgv] using hg.2 u v (parent_le TG hpar)
      have hs :
          (∑ c ∈ TG.children v, ((TS.dist (g v) (g c) : ℤ) +
            (if c = u then 1 else 0))) =
          ∑ c ∈ TG.children v, (TS.dist (f v) (f c) : ℤ) := by
        apply Finset.sum_congr rfl
        intro c hc
        by_cases hcu : c = u
        · subst c
          rw [hgv, hgu, dist_parent_bottom TS hp hpa, Int.natCast_add, Int.natCast_one]
          simp
        · simp [hcu, hgv, ho c hcu]
      simp only [Finset.sum_add_distrib] at hs
      simp [huc] at hs
      simp only [hv, hpar, ite_false, ite_true, add_zero]
      omega
    · simp only [hv, hpar, ite_false, add_zero, sub_zero]
      apply Finset.sum_congr rfl
      intro c hc
      have hcu : c ≠ u := fun he => hpar (he ▸ (children_mem TG v c).mp hc)
      rw [hgv, ho c hcu]

open Classical in
private theorem move_lossAt {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (f g : G → S) (u : G) (p : S) (hp : TS.parent (f u) = some p)
    (hf : IsReconciliation TG TS lab f) (hg : IsReconciliation TG TS lab g)
    (hgu : g u = p) (ho : ∀ v, v ≠ u → g v = f v) (hi : ¬ TG.IsLeaf u)
    (v : G) : lossAt TG TS f v + (if v = u then 2 else 0) -
      (if TG.parent u = some v then 1 else 0) ≤ lossAt TG TS g v := by
  classical
  by_cases hl : TG.IsLeaf v
  · have hnu : v ≠ u := fun he => hi (he ▸ hl)
    have hnp : TG.parent u ≠ some v := by
      intro he
      have hm := (children_mem TG v u).mpr he
      rw [hl] at hm
      simp at hm
    simp [lossAt, hl, hnu, hnp]
  · have hd := move_indicator TG TS lab f g u p hp hf hg hgu ho hi v
    have hs := move_dist_sum TG TS lab f g u p hp hf hg hgu ho hi v
    simp only [lossAt, hl, ite_false]
    omega

private theorem move_gl {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (f g : G → S) (u : G) (p : S) (hp : TS.parent (f u) = some p)
    (hf : IsReconciliation TG TS lab f) (hg : IsReconciliation TG TS lab g)
    (hgu : g u = p) (ho : ∀ v, v ≠ u → g v = f v) (hi : ¬ TG.IsLeaf u) :
    gl TG TS f < gl TG TS g := by
  classical
  have hs := Finset.sum_le_sum (s := Finset.univ) fun v _ =>
    move_lossAt TG TS lab f g u p hp hf hg hgu ho hi v
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hs
  have he : (∑ v : G, if v = u then (2 : ℤ) else 0) = 2 := by simp
  have hpcount : (∑ v : G, if TG.parent u = some v then (1 : ℤ) else 0) ≤ 1 := by
    cases TG.parent u with
    | none => simp
    | some a => simp
  rw [he] at hs
  change gl TG TS f + 2 - _ ≤ gl TG TS g at hs
  omega
open Classical in
private noncomputable def crossings {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (f : G → S) (e : S) : Finset G :=
  Finset.univ.filter fun c => ∃ v, TG.parent c = some v ∧ e ∈ TS.pathEdges (f v) (f c)

private theorem crossings_mem {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (f : G → S) (e : S) (c : G) :
    c ∈ crossings TG TS f e ↔ ∃ v, TG.parent c = some v ∧
      e ∈ TS.pathEdges (f v) (f c) := by
  classical
  simp [crossings]

private theorem move_edge_mem {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (f g : G → S) (u : G) (p : S) (hp : TS.parent (f u) = some p)
    (hf : IsReconciliation TG TS lab f) (hg : IsReconciliation TG TS lab g)
    (hgu : g u = p) (ho : ∀ v, v ≠ u → g v = f v)
    (c v : G) (hcv : TG.parent c = some v) (e : S) (he : e ≠ f u) :
    e ∈ TS.pathEdges (g v) (g c) ↔ e ∈ TS.pathEdges (f v) (f c) := by
  classical
  by_cases hv : v = u
  · subst v
    rw [ho c (parent_ne TG hcv), hgu,
      path_parent_top TS hp (hf.2 c u (parent_le TG hcv))]
    simp [he]
  · by_cases hc : c = u
    · subst c
      have hpa : TS.Le p (f v) := by
        simpa only [hgu, ho v hv] using hg.2 u v (parent_le TG hcv)
      rw [ho v hv, hgu, path_parent_bottom TS hp hpa]
      simp [he]
    · rw [ho v hv, ho c hc]

private theorem move_crossings_other {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (f g : G → S) (u : G) (p : S) (hp : TS.parent (f u) = some p)
    (hf : IsReconciliation TG TS lab f) (hg : IsReconciliation TG TS lab g)
    (hgu : g u = p) (ho : ∀ v, v ≠ u → g v = f v)
    (e : S) (he : e ≠ f u) : crossings TG TS g e = crossings TG TS f e := by
  classical
  ext c
  simp only [crossings_mem]
  constructor
  · rintro ⟨v, hv, hpath⟩
    exact ⟨v, hv, (move_edge_mem TG TS lab f g u p hp hf hg hgu ho c v hv e he).mp hpath⟩
  · rintro ⟨v, hv, hpath⟩
    exact ⟨v, hv, (move_edge_mem TG TS lab f g u p hp hf hg hgu ho c v hv e he).mpr hpath⟩

open Classical in
private theorem move_crossings {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (f g : G → S) (u : G) (p : S) (hp : TS.parent (f u) = some p)
    (hf : IsReconciliation TG TS lab f) (hgu : g u = p)
    (ho : ∀ v, v ≠ u → g v = f v) :
    crossings TG TS g (f u) = (crossings TG TS f (f u)).erase u ∪ TG.children u := by
  classical
  ext c
  simp only [Finset.mem_union, Finset.mem_erase]
  by_cases hc : c = u
  · subst c
    have hself : u ∉ TG.children u := fun h => parent_ne TG ((children_mem TG u u).mp h) rfl
    have hnew : u ∉ crossings TG TS g (f u) := by
      rintro h
      obtain ⟨v, _, hm⟩ := (crossings_mem TG TS g (f u) u).mp h
      have hb := (path_mem TS _ _ _).mp hm
      have hback : TS.Le p (f u) := hgu ▸ hb.1
      exact parent_ne TS hp (le_antisymm TS (parent_le TS hp) hback)
    simp [hself, hnew]
  · by_cases hchild : c ∈ TG.children u
    · have hcv := (children_mem TG u c).mp hchild
      have hnew : c ∈ crossings TG TS g (f u) := by
        apply (crossings_mem TG TS g (f u) c).mpr
        refine ⟨u, hcv, ?_⟩
        rw [hgu, ho c hc, path_parent_top TS hp (hf.2 c u (parent_le TG hcv))]
        exact Finset.mem_insert_self _ _
      simp [hchild, hnew]
    · have hsame : c ∈ crossings TG TS g (f u) ↔ c ∈ crossings TG TS f (f u) := by
        simp only [crossings_mem]
        have hv (v : G) (hv : TG.parent c = some v) : v ≠ u := by
          intro he
          exact hchild ((children_mem TG u c).mpr (he ▸ hv))
        constructor
        · rintro ⟨v, hv', hm⟩
          exact ⟨v, hv', by simpa only [ho v (hv v hv'), ho c hc] using hm⟩
        · rintro ⟨v, hv', hm⟩
          exact ⟨v, hv', by simpa only [ho v (hv v hv'), ho c hc] using hm⟩
      simpa [hc, hchild] using hsame

private theorem move_extra_strict {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (f g : G → S) (u : G) (p : S) (hp : TS.parent (f u) = some p)
    (hf : IsReconciliation TG TS lab f) (hgu : g u = p)
    (ho : ∀ v, v ≠ u → g v = f v) (hi : ¬ TG.IsLeaf u) :
    extraLineages TG TS f (f u) < extraLineages TG TS g (f u) := by
  classical
  have hd : Disjoint ((crossings TG TS f (f u)).erase u) (TG.children u) := by
    apply Finset.disjoint_left.mpr
    intro c hc hchild
    obtain ⟨v, hv, hm⟩ := (crossings_mem TG TS f (f u) c).mp (Finset.mem_erase.mp hc).2
    have hvu : v = u := Option.some.inj (hv.symm.trans ((children_mem TG u c).mp hchild))
    have hb := (path_mem TS _ _ _).mp hm
    exact hb.2.2 (congrArg f hvu).symm
  have he : (crossings TG TS g (f u)).card =
      ((crossings TG TS f (f u)).erase u).card + 2 := by
    rw [move_crossings TG TS lab f g u p hp hf hgu ho,
      Finset.card_union_of_disjoint hd, children_card TG hi]
  change (crossings TG TS f (f u)).card - 1 < (crossings TG TS g (f u)).card - 1
  by_cases hu : u ∈ crossings TG TS f (f u)
  · rw [Finset.card_erase_of_mem hu] at he
    have hpos := Finset.card_pos.mpr ⟨u, hu⟩
    omega
  · rw [Finset.erase_eq_of_notMem hu] at he
    omega

private theorem move_dc {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (f g : G → S) (u : G) (p : S) (hp : TS.parent (f u) = some p)
    (hf : IsReconciliation TG TS lab f) (hg : IsReconciliation TG TS lab g)
    (hgu : g u = p) (ho : ∀ v, v ≠ u → g v = f v) (hi : ¬ TG.IsLeaf u) :
    dc TG TS f < dc TG TS g := by
  classical
  have he := move_extra_strict TG TS lab f g u p hp hf hgu ho hi
  have hroot : f u ≠ TS.root := by
    intro hr
    rw [hr, TS.parent_root] at hp
    cases hp
  apply Finset.sum_lt_sum
  · intro e _
    by_cases hes : e = f u
    · exact (hes ▸ he).le
    · change (crossings TG TS f e).card - 1 ≤ (crossings TG TS g e).card - 1
      rw [move_crossings_other TG TS lab f g u p hp hf hg hgu ho e hes]
  · exact ⟨f u, by simp [hroot], he⟩
private theorem root_le {V : Type*} [Fintype V] (T : RootedBinTree V) (v : V) :
    T.Le v T.root :=
  T.reach_root v

private theorem strict_parent {V : Type*} [Fintype V] (T : RootedBinTree V)
    {a b : V} (hle : T.Le a b) (hne : a ≠ b) :
    ∃ p, T.parent a = some p ∧ T.Le p b := by
  obtain ⟨k, hk⟩ := hle
  cases k with
  | zero => exact False.elim (hne (Option.some.inj hk))
  | succ k =>
    cases hp : T.parent a with
    | none =>
      have he : T.ancestor (k + 1) a = none := by
        simpa only [RootedBinTree.ancestor, Function.iterate_succ_apply,
          Option.bind_some, hp] using iterate_none T k
      rw [he] at hk
      cases hk
    | some p => exact ⟨p, rfl, le_parent T hp ⟨k + 1, hk⟩ hne⟩

private theorem changed_vertex {G S : Type*} [Fintype G] (TG : RootedBinTree G)
    (f f' : G → S) (hne : f' ≠ f) :
    ∃ u, f' u ≠ f u ∧ ∀ v, TG.parent u = some v → f' v = f v := by
  classical
  obtain ⟨w, hw⟩ : ∃ w, f' w ≠ f w := by
    by_contra h
    apply hne
    funext v
    by_contra hv
    exact h ⟨v, hv⟩
  have hex : ∃ n, ∃ u, f' u ≠ f u ∧ TG.dist TG.root u = n :=
    ⟨TG.dist TG.root w, w, hw, rfl⟩
  obtain ⟨u, hu, hn⟩ := Nat.find_spec hex
  refine ⟨u, hu, fun v hv => ?_⟩
  by_contra he
  have hmin := Nat.find_min' hex ⟨v, he, rfl⟩
  have hd := dist_parent_bottom TG hv (root_le TG v)
  omega

private theorem reconciliation_of_edges {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab f : G → S)
    (hl : ∀ v, TG.IsLeaf v → f v = lab v)
    (he : ∀ v u, TG.parent v = some u → TS.Le (f v) (f u)) :
    IsReconciliation TG TS lab f := by
  refine ⟨hl, ?_⟩
  intro v u ⟨k, hk⟩
  induction k generalizing v with
  | zero =>
    have hvu : v = u := Option.some.inj hk
    simpa only [hvu] using le_refl TS (f u)
  | succ k ih =>
    cases hp : TG.parent v with
    | none =>
      have hn : TG.ancestor (k + 1) v = none := by
        simpa only [RootedBinTree.ancestor, Function.iterate_succ_apply,
          Option.bind_some, hp] using iterate_none TG k
      rw [hn] at hk
      cases hk
    | some p =>
      have hpk : TG.ancestor k p = some u := by
        simpa only [RootedBinTree.ancestor, Function.iterate_succ_apply,
          Option.bind_some, hp] using hk
      exact le_trans TS (he v p hp) (ih p hpk)

open Classical in
private theorem raised_reconciliation {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S) (f f' : G → S)
    (hf : IsReconciliation TG TS lab f) (hf' : IsReconciliation TG TS lab f')
    (u : G) (p : S) (hp : TS.parent (f' u) = some p) (hpa : TS.Le p (f u))
    (hi : ¬ TG.IsLeaf u) (htop : ∀ v, TG.parent u = some v → f' v = f v) :
    IsReconciliation TG TS lab (Function.update f' u p) := by
  classical
  apply reconciliation_of_edges TG TS lab
  · intro v hv
    have hnu : v ≠ u := fun he => hi (he ▸ hv)
    simpa only [Function.update_of_ne hnu] using hf'.1 v hv
  · intro c v hcv
    by_cases hv : v = u
    · subst v
      rw [Function.update_self, Function.update_of_ne (parent_ne TG hcv)]
      exact le_trans TS (hf'.2 c u (parent_le TG hcv)) (parent_le TS hp)
    · by_cases hc : c = u
      · subst c
        rw [Function.update_self, Function.update_of_ne hv, htop v hcv]
        exact le_trans TS hpa (hf.2 u v (parent_le TG hcv))
      · simpa only [Function.update_of_ne hv, Function.update_of_ne hc] using
          hf'.2 c v (parent_le TG hcv)

/-- **Monotonicity of the costs** (Wu and Zhang 2011, Theorem 2): for rooted binary trees `TG`, `TS`
with gene leaf labels `lab` mapping gene leaves to species leaves, and two distinct
reconciliations `f' ≠ f` with `f'(v) ≤ f(v)` for every gene vertex `v` (`f(v)` an
ancestor-or-self of `f'(v)`), `gd(f') ≤ gd(f)`, `gl(f') < gl(f)` and `dc(f') < dc(f)`.

Source: Wu and Zhang (2011), Theorem 2. -/
public theorem costs_lt_of_le {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (hlab : ∀ x, TG.IsLeaf x → TS.IsLeaf (lab x)) (f f' : G → S)
    (hf : IsReconciliation TG TS lab f) (hf' : IsReconciliation TG TS lab f')
    (hle : ∀ v, TS.Le (f' v) (f v)) (hne : f' ≠ f) :
    gd TG TS f' ≤ gd TG TS f ∧ gl TG TS f' < gl TG TS f ∧ dc TG TS f' < dc TG TS f
    := by
  classical
  have _ := hlab
  let height (g : G → S) : ℕ := ∑ v, TS.dist TS.root (g v)
  have aux : ∀ n, ∀ f' : G → S, height f' = n →
      IsReconciliation TG TS lab f' → (∀ v, TS.Le (f' v) (f v)) → f' ≠ f →
      gd TG TS f' ≤ gd TG TS f ∧ gl TG TS f' < gl TG TS f ∧ dc TG TS f' < dc TG TS f := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro f' hn hf' hle hne
      obtain ⟨u, hu, htop⟩ := changed_vertex TG f f' hne
      obtain ⟨p, hp, hpa⟩ := strict_parent TS (hle u) hu
      have hi : ¬ TG.IsLeaf u := fun h => hu ((hf'.1 u h).trans (hf.1 u h).symm)
      let g := Function.update f' u p
      have hgu : g u = p := Function.update_self ..
      have ho (v : G) (hv : v ≠ u) : g v = f' v := Function.update_of_ne hv ..
      have hg : IsReconciliation TG TS lab g :=
        raised_reconciliation TG TS lab f f' hf hf' u p hp hpa hi htop
      have hleg (v : G) : TS.Le (g v) (f v) := by
        by_cases hv : v = u
        · simpa only [hv, hgu] using hpa
        · simpa only [ho v hv] using hle v
      have hheight : height g < n := by
        rw [← hn]
        apply Finset.sum_lt_sum
        · intro v _
          by_cases hv : v = u
          · subst v
            rw [hgu, dist_parent_bottom TS hp (root_le TS p)]
            omega
          · rw [ho v hv]
        · refine ⟨u, Finset.mem_univ u, ?_⟩
          rw [hgu, dist_parent_bottom TS hp (root_le TS p)]
          omega
      have hgd := move_gd TG TS lab f' g u p hp hf' hg hgu ho hi
      have hgl := move_gl TG TS lab f' g u p hp hf' hg hgu ho hi
      have hdc := move_dc TG TS lab f' g u p hp hf' hg hgu ho hi
      by_cases he : g = f
      · simpa only [he] using And.intro hgd (And.intro hgl hdc)
      · obtain ⟨hgd', hgl', hdc'⟩ := ih (height g) hheight g rfl hg hleg he
        exact ⟨_root_.le_trans hgd hgd', lt_trans hgl hgl', lt_trans hdc hdc'⟩
  exact aux (height f') f' rfl hf' hle hne

end WantedExt.Biology.ComputationalBiology.LCAReconciliationWanted
