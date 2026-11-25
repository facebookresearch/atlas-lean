/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.CliqueWidth
public import MathlibExt.Combinatorics.SimpleGraph.RankWidth
import Mathlib.FieldTheory.Finiteness
import Mathlib.Logic.Equiv.Fintype

/-!
# Clique-width from a rank-decomposition

A graph of rank-width at most `k` has clique-width at most `2 ^ (k + 1) - 1`.
At each branch of a rank-decomposition we label the vertices by their cut-matrix rows.
-/

@[expose] public section

namespace SimpleGraph.HasRankWidthAtMost

variable {V : Type*} {k : ℕ}

section Tree

attribute [local instance] RankDecomposition.fintype

variable (D : RankDecomposition V)

/-- Tree nodes on the oriented side of an edge, before restriction to labelled leaves. -/
private def branch (i j : D.ι) : Set D.ι :=
  {x | (D.T.deleteEdges {s(i, j)}).Reachable i x}

private theorem branch_disjoint {i j : D.ι} (h : D.T.Adj i j) :
    Disjoint (branch D i j) (branch D j i) := by
  apply Set.disjoint_left.mpr
  intro x hi hj
  rw [branch, Sym2.eq_swap] at hj
  exact (isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp D.isTree.isAcyclic h))
    (hi.trans hj.symm)

private theorem mem_other_branch {i x : D.ι} (hne : x ≠ i) :
    ∃ a, D.T.Adj i a ∧ x ∈ branch D a i := by
  obtain ⟨p, hp, _⟩ := D.isTree.existsUnique_path i x
  obtain ⟨a, ha, q, rfl⟩ := p.exists_eq_cons_of_ne hne.symm
  refine ⟨a, ha, reachable_deleteEdges_iff_exists_walk.mpr ⟨q, ?_⟩⟩
  have ht := hp.isTrail.edges_nodup
  rw [Sym2.eq_swap]
  rw [Walk.edges_cons] at ht
  exact (List.nodup_cons.mp ht).1

private theorem branch_subset {i a b : D.ι} (ha : D.T.Adj i a) (hab : a ≠ b) :
    branch D a i ⊆ branch D i b := by
  classical
  intro x hx
  obtain ⟨p, hp⟩ := reachable_deleteEdges_iff_exists_walk.mp hx
  have hi : i ∉ p.support := by
    intro hi
    have hreach : i ∈ branch D a i := reachable_deleteEdges_iff_exists_walk.mpr
      ⟨p.takeUntil i hi, fun he => hp (p.edges_takeUntil_subset_edges hi he)⟩
    exact Set.disjoint_left.mp (branch_disjoint D ha.symm) hreach Reachable.rfl
  apply reachable_deleteEdges_iff_exists_walk.mpr
  refine ⟨.cons ha p, ?_⟩
  simp only [Walk.edges_cons, List.mem_cons, not_or]
  exact ⟨by simp [hab.symm, ha.ne], fun he => hi (p.fst_mem_support_of_mem_edges he)⟩

private theorem branch_lt {i a b : D.ι} (ha : D.T.Adj i a) (hab : a ≠ b) :
    (branch D a i).ncard < (branch D i b).ncard := by
  refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
  refine Set.ssubset_iff_subset_ne.mpr ⟨branch_subset D ha hab, ?_⟩
  intro heq
  have hi : i ∈ branch D a i := heq ▸ Reachable.rfl
  exact Set.disjoint_left.mp (branch_disjoint D ha.symm) hi Reachable.rfl

private theorem child_disjoint {i a b : D.ι} (ha : D.T.Adj i a) (hb : D.T.Adj i b)
    (hne : a ≠ b) : Disjoint (D.side a i) (D.side b i) :=
  Set.disjoint_left.mpr fun _ hx hy => Set.disjoint_left.mp (branch_disjoint D hb)
    (branch_subset D ha hne hx) hy

/-- Root the induction at an edge. Below it, a node is a leaf or has two children. -/
private theorem tree_induction [Fintype V] [Nonempty V] {G : SimpleGraph V}
    (hw : D.HasWidthAtMost G k) (P : Set V → Prop) (single : ∀ x, P {x})
    (merge : ∀ A B, Disjoint A B → G.cutRank A ≤ k → G.cutRank B ≤ k →
      P A → P B → P (A ∪ B)) : P Set.univ := by
  classical
  let rec aux (i j : D.ι) (hij : D.T.Adj i j) : P (D.side i j) := by
    rcases D.degree_one_or_three i with hi | hi
    · obtain ⟨x, hx⟩ : i ∈ Set.range D.leaf := D.range_leaf.symm ▸ hi
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hi
      have hj : j = a := by simpa [ha] using (show j ∈ D.T.neighborSet i from hij)
      subst a
      suffices D.side i j = {x} from this ▸ single x
      ext y
      constructor
      · intro hy
        by_contra hne
        have hn : D.leaf y ≠ i := fun h => hne (D.leaf.injective (h.trans hx.symm))
        obtain ⟨b, hb, hy'⟩ := mem_other_branch D hn
        have : b = j := by simpa [ha] using (show b ∈ D.T.neighborSet i from hb)
        subst b
        exact Set.disjoint_left.mp (branch_disjoint D hij) hy hy'
      · rintro rfl
        change (D.T.deleteEdges {s(i, j)}).Reachable i _
        rw [hx]
    · let N := D.T.neighborSet i
      have hj : j ∈ N := hij
      have htwo : (N \ {j}).ncard = 2 := by rw [Set.ncard_sdiff_singleton_of_mem hj, hi]
      obtain ⟨a, b, hab, hpair⟩ := Set.ncard_eq_two.mp htwo
      have hm (v : D.ι) : D.T.Adj i v ∧ v ≠ j ↔ v = a ∨ v = b := by
        simpa [N] using Set.ext_iff.mp hpair v
      obtain ⟨ha, haj⟩ := (hm a).mpr (Or.inl rfl)
      obtain ⟨hb, hbj⟩ := (hm b).mpr (Or.inr rfl)
      have hsplit : D.side i j = D.side a i ∪ D.side b i := by
        ext x
        constructor
        · intro hx
          have hxi : D.leaf x ≠ i := by
            intro he
            have : i ∈ Set.range D.leaf := ⟨x, he⟩
            rw [D.range_leaf] at this
            exact (by decide : (3 : ℕ) ≠ 1) (hi.symm.trans this)
          obtain ⟨v, hv, hxv⟩ := mem_other_branch D hxi
          have hvj : v ≠ j := by
            rintro rfl
            exact Set.disjoint_left.mp (branch_disjoint D hij) hx hxv
          rcases (hm v).mp ⟨hv, hvj⟩ with rfl | rfl
          · exact Or.inl hxv
          · exact Or.inr hxv
        · rintro (hx | hx)
          · exact branch_subset D ha haj hx
          · exact branch_subset D hb hbj hx
      rw [hsplit]
      exact merge _ _ (child_disjoint D ha hb hab) (hw _ _ ha.symm) (hw _ _ hb.symm)
        (aux a i ha.symm) (aux b i hb.symm)
  termination_by (branch D i j).ncard
  decreasing_by
    · exact branch_lt D ha haj
    · exact branch_lt D hb hbj
  let x : V := Classical.arbitrary V
  let i := D.leaf x
  have hi : (D.T.neighborSet i).ncard = 1 := by
    have hm : i ∈ Set.range D.leaf := ⟨x, rfl⟩
    rwa [D.range_leaf] at hm
  obtain ⟨j, hj⟩ := Set.ncard_eq_one.mp hi
  have hij : D.T.Adj i j := (show j ∈ D.T.neighborSet i from hj ▸ Set.mem_singleton j)
  have cover : D.side i j ∪ D.side j i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases he : D.leaf y = i
    · exact Or.inl (show D.leaf y ∈ branch D i j from he ▸ Reachable.rfl)
    · obtain ⟨a, ha, hy⟩ := mem_other_branch D he
      have : a = j := by simpa [hj] using (show a ∈ D.T.neighborSet i from ha)
      exact Or.inr (this ▸ hy)
  rw [← cover]
  have hd : Disjoint (D.side i j) (D.side j i) :=
    Set.disjoint_left.mpr fun _ hx hy => Set.disjoint_left.mp (branch_disjoint D hij) hx hy
  exact merge _ _ hd (hw _ _ hij) (hw _ _ hij.symm) (aux i j hij) (aux j i hij.symm)

end Tree

section Expressions

variable {G : SimpleGraph V} {l m : V → Fin k}

private theorem permute (p : Equiv.Perm (Fin k)) (h : CWExpressible k V G l) :
    CWExpressible k V G (p ∘ l) := by
  induction h with
  | vertex W i => exact .vertex W (p i)
  | union _ _ ih₁ ih₂ =>
    convert CWExpressible.union ih₁ ih₂ using 1
    funext x
    cases x <;> rfl
  | join i j hij _ ih =>
    simpa [Function.comp_def] using CWExpressible.join (p i) (p j) (p.injective.ne hij) ih
  | relabel i j _ ih =>
    convert CWExpressible.relabel (p i) (p j) ih using 1
    funext x
    simp only [Function.comp_apply, apply_ite, Equiv.apply_eq_iff_eq]
    split <;> simp_all
  | iso e _ ih => exact .iso e ih

private theorem collapse (r : Fin k → Fin k) (hr : ∀ i, r (r i) = r i)
    (h : CWExpressible k V G l) : CWExpressible k V G (r ∘ l) := by
  have aux (s : Finset (Fin k)) :
      CWExpressible k V G (fun x => if l x ∈ s then r (l x) else l x) := by
    induction s using Finset.induction_on with
    | empty => simpa using h
    | insert i s hi ih =>
      convert CWExpressible.relabel i (r i) ih using 1
      funext x
      by_cases hx : l x ∈ s <;> by_cases he : l x = i <;>
        simp [hx, he, hi, apply_ite]
      grind
  simpa [Function.comp_def] using aux Finset.univ

/-- Coarsening the partition into label classes is possible within the same palette. -/
private theorem coarsen (h : CWExpressible k V G l) (hm : ∀ x y, l x = l y → m x = m y) :
    CWExpressible k V G m := by
  classical
  -- Collapse each new class onto one old label, then permute the representatives.
  let rep (i : Set.range m) : V := i.property.choose
  have hrep (i : Set.range m) : m (rep i) = i := i.property.choose_spec
  have hinj : Function.Injective (fun i => l (rep i)) := by
    intro i j hij
    exact Subtype.ext ((hrep i).symm.trans ((hm _ _ hij).trans (hrep j)))
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair _ (fun i : Set.range m => i.val) hinj
    Subtype.val_injective
  let r (i : Fin k) := if hi : i ∈ Set.range l then l (rep ⟨m hi.choose, hi.choose, rfl⟩) else i
  have hr (x : V) : r (l x) = l (rep ⟨m x, x, rfl⟩) := by
    have hx : l x ∈ Set.range l := ⟨x, rfl⟩
    simp only [r, dite_eq_left hx]
    congr 2
    exact Subtype.ext (hm _ _ hx.choose_spec)
  have hid (i) : r (r i) = r i := by
    by_cases hi : i ∈ Set.range l
    · obtain ⟨x, rfl⟩ := hi
      rw [hr, hr]
      congr 2
      exact Subtype.ext (hrep _)
    · rw [show r i = i from dite_eq_right hi]
      exact (dite_eq_right hi : r i = i)
  convert permute p (collapse r hid h) using 1
  funext x
  exact ((congrArg p (hr x)).trans (hp ⟨m x, x, rfl⟩)).symm

/-- Add a finite family of joins, one for each selected pair of distinct labels. -/
private theorem join_pairs (h : CWExpressible k V G l) (s : Finset (Fin k × Fin k))
    (hs : ∀ p ∈ s, p.1 ≠ p.2) :
    CWExpressible k V (G ⊔ fromRel (fun x y => (l x, l y) ∈ s)) l := by
  induction s using Finset.induction_on with
  | empty =>
    convert h using 1
    ext
    simp
  | insert p s hp ih =>
    have hn := hs p (Finset.mem_insert_self p s)
    have h' := CWExpressible.join p.1 p.2 hn (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))
    convert h' using 1
    ext x y
    simp only [sup_adj, fromRel_adj, Finset.mem_insert, Prod.ext_iff]
    tauto

end Expressions

/-- Neighbours outside the current side of the cut. -/
private def profile (G : SimpleGraph V) (S : Set V) (x : V) : Set V :=
  {z | z ∉ S ∧ G.Adj x z}

/-- Reserve the shared label for the zero row. All other rows fit in a private palette. -/
private theorem encode_rows [Fintype V] (G : SimpleGraph V) (S : Set V) (hw : G.cutRank S ≤ k) :
    ∃ c : S → Option (Fin (2 ^ k - 1)),
      (∀ x y, c x = c y ↔ profile G S x = profile G S y) ∧
      (∀ x, c x = none ↔ profile G S x = ∅) := by
  classical
  let M := (G.adjMatrix (ZMod 2)).submatrix (fun x : S => x.val) (fun z : ↥Sᶜ => z.val)
  let L := Submodule.span (ZMod 2) (Set.range M.row)
  let row (x : S) : L := ⟨M.row x, Submodule.subset_span ⟨x, rfl⟩⟩
  have entry (x : S) (z : ↥Sᶜ) : (row x).val z = if G.Adj x z then 1 else 0 := rfl
  have hrow (x y : S) : row x = row y ↔ profile G S x = profile G S y := by
    constructor
    · intro h
      ext z
      by_cases hz : z ∈ S
      · simp [profile, hz]
      · have he := congrArg (fun r : L => r.val ⟨z, hz⟩) h
        change (row x).val _ = (row y).val _ at he
        rw [entry, entry] at he
        by_cases hx : G.Adj x z <;> by_cases hy : G.Adj y z <;> simp_all [profile]
    · intro h
      apply Subtype.ext
      funext z
      have he := Set.ext_iff.mp h z.val
      have hz : z.val ∉ S := z.property
      have hadj : G.Adj x z ↔ G.Adj y z := by simpa [profile, hz] using he
      rw [entry, entry, hadj]
  have hzero (x : S) : row x = 0 ↔ profile G S x = ∅ := by
    constructor
    · intro h
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨hz, hx⟩
      have he := congrArg (fun r : L => r.val ⟨z, hz⟩) h
      change (row x).val _ = 0 at he
      simp [entry, hx] at he
    · intro h
      apply Subtype.ext
      funext z
      have hn : ¬G.Adj x z := fun ha =>
        (Set.eq_empty_iff_forall_notMem.mp h z) ⟨z.property, ha⟩
      simp [entry, hn]
  have hc : Fintype.card L ≤ 2 ^ k := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, ← M.rank_eq_finrank_span_row]
    exact Nat.pow_le_pow_right (by decide) hw
  obtain ⟨e⟩ : Nonempty ({r : L // r ≠ 0} ↪ Fin (2 ^ k - 1)) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_subtype_compl (fun r : L => r = 0)]
    simpa using Nat.sub_le_sub_right hc 1
  let code (r : L) := if hr : r = 0 then none else some (e ⟨r, hr⟩)
  have hinj : Function.Injective code := by
    intro r s h
    by_cases hr : r = 0 <;> by_cases hs : s = 0 <;> simp_all [code]
  refine ⟨code ∘ row, fun x y => hinj.eq_iff.trans (hrow x y), fun x => ?_⟩
  simpa [Function.comp_def, code] using hzero x

private abbrev palette (k : ℕ) := Fin (2 ^ (k + 1) - 1)

/-- Two sets of nonzero row labels and one shared zero label fit in the target palette. -/
private theorem child_labels [Fintype V] (G : SimpleGraph V) (A B : Set V)
    (ha : G.cutRank A ≤ k) (hb : G.cutRank B ≤ k) :
    ∃ (l : A → palette k) (m : B → palette k),
      (∀ x y, l x = l y ↔ profile G A x = profile G A y) ∧
      (∀ x y, m x = m y ↔ profile G B x = profile G B y) ∧
      (∀ x y, l x = m y → profile G A x = ∅ ∧ profile G B y = ∅) := by
  classical
  obtain ⟨a, ha₁, ha₀⟩ := encode_rows G A ha
  obtain ⟨b, hb₁, hb₀⟩ := encode_rows G B hb
  let I := Fin (2 ^ k - 1)
  let e : Option (I ⊕ I) ≃ palette k := Fintype.equivFinOfCardEq (by
    have := Nat.two_pow_pos k
    simp [I, pow_succ]
    omega)
  refine ⟨fun x => e ((a x).map Sum.inl), fun y => e ((b y).map Sum.inr), ?_, ?_, ?_⟩
  · intro x y
    rw [← ha₁, e.injective.eq_iff]
    cases a x <;> cases a y <;> simp
  · intro x y
    rw [← hb₁, e.injective.eq_iff]
    cases b x <;> cases b y <;> simp
  · intro x y h
    rw [e.injective.eq_iff] at h
    rw [← ha₀, ← hb₀]
    revert h
    cases a x <;> cases b y <;> simp

/-- Build the edges across a split by joining precisely the label pairs seen on crossing edges. -/
private theorem join_cut {G : SimpleGraph V} {A B : Set V} (hd : Disjoint A B)
    {l : A → Fin k} {m : B → Fin k}
    (hl : ∀ x y, l x = l y → profile G A x = profile G A y)
    (hm : ∀ x y, m x = m y → profile G B x = profile G B y)
    (hz : ∀ x y, l x = m y → profile G A x = ∅ ∧ profile G B y = ∅)
    (el : CWExpressible k A (G.induce A) l) (er : CWExpressible k B (G.induce B) m) :
    CWExpressible k (A ⊕ B) (G.comap (Sum.elim Subtype.val Subtype.val)) (Sum.elim l m) := by
  classical
  have left (a : A) (b : B) : (b : V) ∈ profile G A a ↔ G.Adj a b :=
    ⟨And.right, fun h => ⟨fun hb => Set.disjoint_left.mp hd hb b.property, h⟩⟩
  have right (b : B) (a : A) : (a : V) ∈ profile G B b ↔ G.Adj a b :=
    ⟨fun h => h.2.symm, fun h => ⟨Set.disjoint_left.mp hd a.property, h.symm⟩⟩
  let pairs := Finset.univ.filter fun p : Fin k × Fin k =>
    ∃ (a : A) (b : B), l a = p.1 ∧ m b = p.2 ∧ G.Adj a b
  have mem (i j : Fin k) : (i, j) ∈ pairs ↔
      ∃ (a : A) (b : B), l a = i ∧ m b = j ∧ G.Adj a b := by simp [pairs]
  have active {a : A} {b : B} (h : G.Adj a b) : profile G A a ≠ ∅ ∧ profile G B b ≠ ∅ :=
    ⟨Set.nonempty_iff_ne_empty.mp ⟨_, (left a b).mpr h⟩,
      Set.nonempty_iff_ne_empty.mp ⟨_, (right b a).mpr h⟩⟩
  have diff : ∀ p ∈ pairs, p.1 ≠ p.2 := by
    rintro ⟨i, j⟩ hp he
    obtain ⟨a, b, ha, hb, h⟩ := (mem _ _).mp hp
    exact (active h).1 (hz a b (ha.trans (he.trans hb.symm))).1
  let val : A ⊕ B → V := Sum.elim Subtype.val Subtype.val
  let lab := Sum.elim l m
  have sound (x y : A ⊕ B) (hp : (lab x, lab y) ∈ pairs) : G.Adj (val x) (val y) := by
    obtain ⟨a, b, ha, hb, h⟩ := (mem _ _).mp hp
    cases x with
    | inr x => exact False.elim ((active h).1 (hz a x ha).1)
    | inl x =>
      cases y with
      | inl y => exact False.elim ((active h).2 (hz y b hb.symm).2)
      | inr y =>
        have hx : G.Adj x b := (left x b).mp (hl a x ha ▸ (left a b).mpr h)
        exact (right y x).mp (hm b y hb ▸ (right b x).mpr hx)
  have joined := join_pairs (CWExpressible.union el er) pairs diff
  convert joined using 1
  ext x y
  change G.Adj (val x) (val y) ↔ ((G.induce A ⊕g G.induce B).Adj x y ∨
    x ≠ y ∧ ((lab x, lab y) ∈ pairs ∨ (lab y, lab x) ∈ pairs))
  constructor
  · intro h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact Or.inl h
      | inr y => exact Or.inr ⟨by simp, Or.inl ((mem _ _).mpr ⟨x, y, rfl, rfl, h⟩)⟩
    | inr x =>
      cases y with
      | inr y => exact Or.inl h
      | inl y => exact Or.inr ⟨by simp, Or.inr ((mem _ _).mpr ⟨y, x, rfl, rfl, h.symm⟩)⟩
  · rintro (h | ⟨_, h | h⟩)
    · cases x <;> cases y <;> first | exact h | simp at h
    · exact sound _ _ h
    · exact (sound _ _ h).symm

private theorem restrict_profile (G : SimpleGraph V) {S T : Set V} (h : S ⊆ T) (x : V) :
    profile G T x = profile G S x \ T := by
  ext z
  exact ⟨fun ⟨hz, ha⟩ => ⟨⟨fun hs => hz (h hs), ha⟩, hz⟩, fun ⟨⟨_, ha⟩, hz⟩ => ⟨hz, ha⟩⟩

universe u

private theorem transport {U W : Type u} (e : U ≃ W) {H : SimpleGraph W} {l : W → Fin k}
    (h : CWExpressible k U (H.comap e) (l ∘ e)) : CWExpressible k W H l := by
  have h' := CWExpressible.iso e h
  change CWExpressible k W ((H.comap e).map e) ((l ∘ e) ∘ e.symm) at h'
  simpa [map_comap_eq e.surjective, Function.comp_assoc] using h'

/-- At each subtree, any prescribed labelling that depends only on the cut rows is possible. -/
private def Builds (G : SimpleGraph V) (k : ℕ) (S : Set V) : Prop :=
  ∀ l : S → palette k, (∀ x y : S, profile G S x = profile G S y → l x = l y) →
    CWExpressible (2 ^ (k + 1) - 1) S (G.induce S) l

private theorem merge_builds [Fintype V] {G : SimpleGraph V} {A B : Set V}
    (hd : Disjoint A B) (ha : G.cutRank A ≤ k) (hb : G.cutRank B ≤ k)
    (buildA : Builds G k A) (buildB : Builds G k B) : Builds G k (A ∪ B) := by
  classical
  intro label hlabel
  obtain ⟨l, m, hl, hm, hz⟩ := child_labels G A B ha hb
  have h := join_cut hd (fun x y => (hl x y).mp) (fun x y => (hm x y).mp) hz
    (buildA l fun x y => (hl x y).mpr) (buildB m fun x y => (hm x y).mpr)
  let e := (Equiv.Set.union hd).symm
  have hv (x : A ⊕ B) : (e x).val = Sum.elim Subtype.val Subtype.val x := by cases x <;> rfl
  have heq : (G.induce (A ∪ B)).comap e = G.comap (Sum.elim Subtype.val Subtype.val) := by
    ext x y
    change G.Adj (e x).val (e y).val ↔ _
    rw [hv, hv]
    rfl
  apply transport e
  rw [heq]
  apply coarsen h
  intro x y hxy
  apply hlabel
  have left (a : A) : profile G (A ∪ B) (e (.inl a)) = profile G A a \ (A ∪ B) :=
    restrict_profile G Set.subset_union_left _
  have right (b : B) : profile G (A ∪ B) (e (.inr b)) = profile G B b \ (A ∪ B) :=
    restrict_profile G Set.subset_union_right _
  cases x with
  | inl x =>
    cases y with
    | inl y => rw [left, left, (hl x y).mp hxy]
    | inr y => rw [left, right, (hz x y hxy).1, (hz x y hxy).2]
  | inr x =>
    cases y with
    | inl y => rw [right, left, (hz y x hxy.symm).1, (hz y x hxy.symm).2]
    | inr y => rw [right, right, (hm x y).mp hxy]

private theorem single_vertex [Unique V] (G : SimpleGraph V) {n : ℕ} (l : V → Fin n) :
    CWExpressible n V G l := by
  convert CWExpressible.vertex V (l default) using 1
  · ext x y
    simp [Subsingleton.elim x y]
  · funext x
    rw [Subsingleton.elim x default]

variable [Fintype V]

/-- **Clique-width is bounded by an exponential in rank-width (Oum–Seymour).** If a finite graph
has rank-width at most `k`, it has clique-width at most `2 ^ (k + 1) - 1`; this is the inequality
`cw(G) ≤ 2 ^ (rw(G) + 1) - 1` of Oum and Seymour, *Approximating clique-width and branch-width*,
J. Combin. Theory Ser. B 96 (2006), Proposition 6.3 (also Oum, arXiv:1601.03800v2,
Theorem 2.1). With the previous statement, a class of graphs has bounded rank-width if and only
if it has bounded clique-width. -/
theorem hasCliqueWidthAtMost {G : SimpleGraph V} {k : ℕ}
    (h : G.HasRankWidthAtMost k) : G.HasCliqueWidthAtMost (2 ^ (k + 1) - 1) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl he => exact Or.inl he
  | inr hn =>
    let zeroLabel : palette k := ⟨0, by have := Nat.two_pow_pos k; rw [pow_succ]; omega⟩
    refine Or.inr ⟨fun _ => zeroLabel, ?_⟩
    rcases h with hsmall | ⟨D, hw⟩
    · have := Fintype.card_le_one_iff_subsingleton.mp hsmall
      let _ : Unique V := ⟨⟨Classical.choice hn⟩, fun _ => Subsingleton.elim _ _⟩
      exact single_vertex _ _
    · have build := tree_induction D hw (Builds G k)
        (fun x l _ => single_vertex _ l) (fun _ _ => merge_builds)
      apply transport (Equiv.Set.univ V)
      exact build (fun _ => zeroLabel) (fun _ _ _ => rfl)

end SimpleGraph.HasRankWidthAtMost
