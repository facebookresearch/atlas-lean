/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Sort

/-!
# Tree metrics and Buneman's four-point condition

A dissimilarity `d` on a set of taxa is a *tree metric* when the taxa can be placed on the
vertices of a finite tree with positive edge lengths so that `d x y` is the length of the path
between them (internal "Steiner" vertices are allowed and distinct taxa may share a vertex).
Buneman (1974) characterized tree metrics by the four-point condition
`d x y + d z t ≤ max (d x z + d y t) (d x t + d y z)`.

## Main results

* `IsTreeMetric.fourPointCondition`: every tree metric satisfies the four-point condition.
* `isTreeMetric_of_fourPointCondition`: a symmetric dissimilarity on a finite set that vanishes
  on the diagonal and satisfies the four-point condition is a tree metric.
* `isTreeMetric_iff_fourPointCondition`: **Buneman's four-point theorem**, the two directions
  together.

## Proof sketch

Forward: for four vertices of a tree, either the paths `x – z` and `y – t` or the paths
`x – t` and `y – z` share a vertex (`crossing_paths`); splitting both paths there and applying
the triangle inequality of the tree path metric gives the bound.

Converse: fix a base point `r` and take the Gromov products
`g x y = (d r x + d r y - d x y) / 2`. The four-point condition makes `g` an ultrametric-like
similarity (`min (g x y) (g y z) ≤ g x z`, `g x y ≤ g x x`). Ranking its finitely many values
gives integer levels; the tree has one vertex for each taxon and level up to the taxon's own
level, two such vertices being identified when the taxa agree up to that level, each vertex is
joined to the vertex one level below, and the edge into level `k` has length
`f k - f (k - 1)` for the increasing enumeration `f` of the values of `g`. The path length
between the vertices of `x` and `y` is then `g x x + g y y - 2 g x y = d x y`.

## References

* P. Buneman, *A note on the metric properties of trees*, J. Combin. Theory Ser. B 17 (1974),
  48–50.
* C. Semple and M. Steel, *Phylogenetics*, Oxford University Press, 2003, Theorem 7.2.6.
-/

@[expose] public section

namespace MathlibExt.Biology.Phylogenetics.Buneman

/-- `d` is a **tree metric**: there are a finite tree `G` on a vertex type `V`, positive edge
lengths `w`, and a placement `ι` of the taxa on vertices such that `d x y` is the total length
of the (unique) path from `ι x` to `ι y`. -/
def IsTreeMetric {X : Type*} (d : X → X → ℝ) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : G.IsTree) (w : Sym2 V → ℝ)
    (ι : X → V), (∀ e ∈ G.edgeSet, 0 < w e) ∧
      ∀ x y (p : G.Walk (ι x) (ι y)), p.IsPath → d x y = (p.edges.map w).sum

/-- The **four-point condition**: `d x y + d z t ≤ max (d x z + d y t) (d x t + d y z)`. -/
def FourPointCondition {X : Type*} (d : X → X → ℝ) : Prop :=
  ∀ x y z t, d x y + d z t ≤ max (d x z + d y t) (d x t + d y z)

private theorem append_path {V : Type*} {G : SimpleGraph V} {u m v : V}
    {p : G.Walk u m} {q : G.Walk m v} (hp : p.IsPath) (hq : q.IsPath)
    (hi : ∀ a ∈ p.support, a ∈ q.support → a = m) : (p.append q).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.support_append]
  apply List.nodup_append.mpr
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  intro a ha b hb hab
  subst b
  have ham := hi a ha (List.mem_of_mem_tail hb)
  subst a
  have hn := hq.support_nodup
  rw [← q.cons_tail_support, List.nodup_cons] at hn
  exact hn.1 hb

private theorem first_hit {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (S : Set V) (hv : v ∈ S) :
    ∃ m ∈ S, ∃ a : G.Walk u m, a.IsPath ∧ a.support ⊆ p.support ∧
      ∀ b ∈ a.support, b ∈ S → b = m := by
  classical
  induction p with
  | nil =>
      exact ⟨_, hv, .nil, .nil, fun _ h => h, by simp⟩
  | @cons u v z hadj p ih =>
      by_cases hu : u ∈ S
      · refine ⟨u, hu, .nil, .nil, ?_, ?_⟩
        · simp
        · simp
      · obtain ⟨m, hm, a, ha, hs, hi⟩ := ih hp.of_cons hv
        refine ⟨m, hm, a.cons hadj, ha.cons ?_, ?_, ?_⟩
        · exact fun h => (SimpleGraph.Walk.cons_isPath_iff _ _).mp hp |>.2 (hs h)
        · simpa using List.cons_subset_cons u hs
        · intro b hb hS
          rcases List.mem_cons.mp hb with rfl | hb
          · exact (hu hS).elim
          · exact hi b hb hS

private theorem crossing_paths {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    {x y z t : V} (p : G.Walk x z) (q : G.Walk y t)
    (r : G.Walk x t) (s : G.Walk y z)
    (hp : p.IsPath) (hr : r.IsPath) (hs : s.IsPath) :
    (∃ m, m ∈ p.support ∧ m ∈ q.support) ∨
      ∃ m, m ∈ r.support ∧ m ∈ s.support := by
  classical
  by_cases hi : ∃ m, m ∈ p.support ∧ m ∈ q.support
  · exact Or.inl hi
  right
  obtain ⟨a, ha, _⟩ := hG.existsUnique_path y x
  obtain ⟨m, hm, b, hb, _, hbi⟩ :=
    first_hit a ha {v | v ∈ p.support} p.start_mem_support
  let c := (q.reverse.append b).bypass
  have hc : c.IsPath := SimpleGraph.Walk.bypass_isPath _
  have hci : ∀ v ∈ c.support, v ∈ p.support → v = m := by
    intro v hv hvp
    have hv' := (q.reverse.append b).support_bypass_subset_support hv
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hv' with hvq | hvb
    · have hvq' : v ∈ q.support := by simpa using hvq
      exact (hi ⟨v, hvp, hvq'⟩).elim
    · exact hbi v hvb hvp
  let px := p.takeUntil m hm
  let pz := p.dropUntil m hm
  have hxt : (px.append c.reverse).IsPath :=
    append_path (hp.takeUntil hm) hc.reverse (by
      intro v hvx hvc
      apply hci v (by simpa using hvc)
      exact p.support_takeUntil_subset_support hm hvx)
  have hyz : (b.append pz).IsPath :=
    append_path hb (hp.dropUntil hm) (by
      intro v hvb hvz
      exact hbi v hvb (p.support_dropUntil_subset_support hm hvz))
  have er : r = px.append c.reverse :=
    (hG.existsUnique_path x t).unique hr hxt
  have es : s = b.append pz :=
    (hG.existsUnique_path y z).unique hs hyz
  refine ⟨m, ?_, ?_⟩
  · rw [er]
    exact SimpleGraph.Walk.support_subset_support_append_left _ _ px.end_mem_support
  · rw [es]
    exact SimpleGraph.Walk.support_subset_support_append_left _ _ b.end_mem_support

private noncomputable def treeDist {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    (w : Sym2 V → ℝ) (u v : V) : ℝ :=
  (((hG.existsUnique_path u v).choose).edges.map w).sum

private theorem treeDist_eq {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    (w : Sym2 V → ℝ) {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    treeDist hG w u v = (p.edges.map w).sum := by
  unfold treeDist
  rw [(hG.existsUnique_path u v).choose_spec.2 p hp]

private theorem treeDist_symm {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    (w : Sym2 V → ℝ) (u v : V) : treeDist hG w u v = treeDist hG w v u := by
  obtain ⟨p, hp, _⟩ := hG.existsUnique_path u v
  rw [treeDist_eq hG w p hp, treeDist_eq hG w p.reverse hp.reverse]
  simp

private theorem treeDist_triangle {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    (w : Sym2 V → ℝ) (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e) (u m v : V) :
    treeDist hG w u v ≤ treeDist hG w u m + treeDist hG w m v := by
  classical
  obtain ⟨p, hp, _⟩ := hG.existsUnique_path u m
  obtain ⟨q, hq, _⟩ := hG.existsUnique_path m v
  rw [treeDist_eq hG w (p.append q).bypass (p.append q).bypass_isPath,
    treeDist_eq hG w p hp, treeDist_eq hG w q hq]
  have hle := ((p.append q).edges_bypass_sublist_edges.map w).sum_le_sum (by
    intro a ha
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    exact hw e ((p.append q).edges_subset_edgeSet he))
  simpa using hle

private theorem treeDist_split {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    (w : Sym2 V → ℝ) {u v m : V} (p : G.Walk u v) (hp : p.IsPath)
    (hm : m ∈ p.support) :
    treeDist hG w u v = treeDist hG w u m + treeDist hG w m v := by
  classical
  rw [treeDist_eq hG w p hp,
    treeDist_eq hG w (p.takeUntil m hm) (hp.takeUntil hm),
    treeDist_eq hG w (p.dropUntil m hm) (hp.dropUntil hm)]
  have he := congrArg (fun a => (a.edges.map w).sum) (p.take_spec hm)
  simpa only [SimpleGraph.Walk.edges_append, List.map_append, List.sum_append] using he.symm

private theorem treeDist_pairing {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    (w : Sym2 V → ℝ) (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e)
    {x y z t m : V} (p : G.Walk x z) (q : G.Walk y t)
    (hp : p.IsPath) (hq : q.IsPath) (hmp : m ∈ p.support) (hmq : m ∈ q.support) :
    treeDist hG w x y + treeDist hG w z t ≤
      treeDist hG w x z + treeDist hG w y t := by
  rw [treeDist_split hG w p hp hmp, treeDist_split hG w q hq hmq]
  have hxy := treeDist_triangle hG w hw x m y
  have hzt := treeDist_triangle hG w hw z m t
  rw [treeDist_symm hG w m y] at hxy
  rw [treeDist_symm hG w z m] at hzt
  calc
    _ ≤ (treeDist hG w x m + treeDist hG w y m) +
        (treeDist hG w m z + treeDist hG w m t) := add_le_add hxy hzt
    _ = _ := by ac_rfl

private theorem treeDist_fourPoint {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    (w : Sym2 V → ℝ) (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e) :
    FourPointCondition (treeDist hG w) := by
  intro x y z t
  obtain ⟨p, hp, _⟩ := hG.existsUnique_path x z
  obtain ⟨q, hq, _⟩ := hG.existsUnique_path y t
  obtain ⟨r, hr, _⟩ := hG.existsUnique_path x t
  obtain ⟨s, hs, _⟩ := hG.existsUnique_path y z
  rcases crossing_paths hG p q r s hp hr hs with ⟨m, hmp, hmq⟩ | ⟨m, hmr, hms⟩
  · exact (treeDist_pairing hG w hw p q hp hq hmp hmq).trans (le_max_left _ _)
  · have he := treeDist_pairing hG w hw r s hr hs hmr hms
    rw [treeDist_symm hG w t z] at he
    exact he.trans (le_max_right _ _)

/-- **Tree metrics satisfy the four-point condition** (the easy direction of Buneman's
theorem).

Source: Buneman (1974); Semple & Steel (2003), Theorem 7.2.6. -/
theorem IsTreeMetric.fourPointCondition {X : Type*} {d : X → X → ℝ} (h : IsTreeMetric d) :
    FourPointCondition d := by
  obtain ⟨V, hV, G, hG, w, ι, hw, hd⟩ := h
  have he : ∀ x y, d x y = treeDist hG w (ι x) (ι y) := by
    intro x y
    obtain ⟨p, hp, _⟩ := hG.existsUnique_path (ι x) (ι y)
    exact (hd x y p hp).trans (treeDist_eq hG w p hp).symm
  intro x y z t
  simp only [he]
  exact treeDist_fourPoint hG w (fun e he => (hw e he).le) (ι x) (ι y) (ι z) (ι t)

/-! ### The converse: realizing a four-point metric by a tree -/

private def Avoid {V : Type} (G : SimpleGraph V) (e : Sym2 V) (u v : V) : Prop :=
  ∃ p : G.Walk u v, e ∉ p.edges

private lemma avoid_refl {V : Type} {G : SimpleGraph V} {e : Sym2 V} {u : V} :
    Avoid G e u u :=
  ⟨.nil, by simp⟩

private lemma avoid_symm {V : Type} {G : SimpleGraph V} {e : Sym2 V} {u v : V}
    (h : Avoid G e u v) : Avoid G e v u := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, by simpa using hp⟩

private lemma avoid_trans {V : Type} {G : SimpleGraph V} {e : Sym2 V} {u v t : V}
    (h₁ : Avoid G e u v) (h₂ : Avoid G e v t) : Avoid G e u t := by
  obtain ⟨p, hp⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  exact ⟨p.append q, by simp [hp, hq]⟩

/-- In a forest, a path uses the edge `e` iff `e` separates its endpoints. -/
private lemma mem_edges_iff_not_avoid {V : Type} {G : SimpleGraph V} (hG : G.IsAcyclic)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) (e : Sym2 V) :
    e ∈ p.edges ↔ ¬Avoid G e u v := by
  classical
  refine ⟨fun he ⟨q, hq⟩ => hq ?_, fun h => ?_⟩
  · have : q.bypass = p :=
      congrArg Subtype.val ((hG.subsingleton_path u v).elim ⟨q.bypass, q.bypass_isPath⟩ ⟨p, hp⟩)
    exact q.edges_bypass_subset_edges (this ▸ he)
  · by_contra he
    exact h ⟨p, he⟩

/-- A finite rooted tree, presented by a parent map that decreases a height function. -/
private structure Rooted (V : Type) where
  par : V → V
  root : V
  hgt : V → ℕ
  par_root : par root = root
  hgt_par : ∀ v, v ≠ root → hgt (par v) < hgt v

/-- The graph joining every non-root vertex to its parent. -/
private def Rooted.graph {V : Type} (T : Rooted V) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => u ≠ T.root ∧ v = T.par u

/-- `c` is an ancestor of `v` (possibly `v` itself). -/
private def Rooted.Anc {V : Type} (T : Rooted V) (c v : V) : Prop :=
  ∃ j, T.par^[j] v = c

private lemma Rooted.par_ne {V : Type} (T : Rooted V) {v : V} (hv : v ≠ T.root) :
    T.par v ≠ v :=
  fun h => (T.hgt_par v hv).ne (congrArg T.hgt h)

private lemma Rooted.hgt_par_le {V : Type} (T : Rooted V) (v : V) :
    T.hgt (T.par v) ≤ T.hgt v := by
  by_cases hv : v = T.root
  · rw [hv, T.par_root]
  · exact (T.hgt_par v hv).le

private lemma Rooted.hgt_iterate_lt {V : Type} (T : Rooted V) {v : V} (hv : v ≠ T.root)
    (j : ℕ) : T.hgt (T.par^[j + 1] v) < T.hgt v := by
  induction j with
  | zero => simpa using T.hgt_par v hv
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact lt_of_le_of_lt (T.hgt_par_le _) ih

private lemma Rooted.anc_refl {V : Type} (T : Rooted V) (v : V) : T.Anc v v :=
  ⟨0, rfl⟩

private lemma Rooted.anc_of_anc_par {V : Type} (T : Rooted V) {c v : V}
    (h : T.Anc c (T.par v)) : T.Anc c v := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j + 1, by rwa [Function.iterate_succ_apply]⟩

private lemma Rooted.anc_iff {V : Type} (T : Rooted V) {c v : V} (hv : v ≠ T.root) :
    T.Anc c v ↔ c = v ∨ T.Anc c (T.par v) := by
  constructor
  · rintro ⟨j, hj⟩
    cases j with
    | zero => exact Or.inl hj.symm
    | succ j => exact Or.inr ⟨j, by rwa [Function.iterate_succ_apply] at hj⟩
  · rintro (rfl | h)
    · exact T.anc_refl c
    · exact T.anc_of_anc_par h

private lemma Rooted.eq_root_of_anc_root {V : Type} (T : Rooted V) {c : V}
    (h : T.Anc c T.root) : c = T.root := by
  obtain ⟨j, hj⟩ := h
  rw [← hj, Function.iterate_fixed T.par_root]

private lemma Rooted.not_anc_par {V : Type} (T : Rooted V) {c : V} (hc : c ≠ T.root) :
    ¬T.Anc c (T.par c) := by
  rintro ⟨j, hj⟩
  have := T.hgt_iterate_lt hc j
  rw [Function.iterate_succ_apply, hj] at this
  exact lt_irrefl _ this

private lemma Rooted.graph_adj {V : Type} (T : Rooted V) {u v : V} :
    T.graph.Adj u v ↔ (u ≠ T.root ∧ v = T.par u) ∨ (v ≠ T.root ∧ u = T.par v) := by
  rw [Rooted.graph, SimpleGraph.fromRel_adj]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rintro rfl
  rcases h with ⟨hu, h⟩ | ⟨hu, h⟩ <;> exact T.par_ne hu h.symm

private lemma Rooted.adj_par {V : Type} (T : Rooted V) {v : V} (hv : v ≠ T.root) :
    T.graph.Adj v (T.par v) :=
  T.graph_adj.mpr (Or.inl ⟨hv, rfl⟩)

private lemma Rooted.avoid_par {V : Type} (T : Rooted V) {c u : V} (hu : u ≠ T.root)
    (h : s(u, T.par u) ≠ s(c, T.par c)) : Avoid T.graph s(c, T.par c) u (T.par u) :=
  ⟨.cons (T.adj_par hu) .nil, fun h' => h (List.mem_singleton.mp h').symm⟩

private lemma Rooted.avoid_of_anc {V : Type} (T : Rooted V) {c u : V} (hc : c ≠ T.root)
    (h : T.Anc c u) : Avoid T.graph s(c, T.par c) u c := by
  obtain ⟨j, hj⟩ := h
  induction j generalizing u with
  | zero => subst hj; exact avoid_refl
  | succ j ih =>
    rw [Function.iterate_succ_apply] at hj
    have hu : u ≠ T.root := by
      rintro rfl
      rw [T.par_root, Function.iterate_fixed T.par_root] at hj
      exact hc hj.symm
    refine avoid_trans (T.avoid_par hu fun he => ?_) (ih hj)
    rcases Sym2.eq_iff.mp he with ⟨rfl, -⟩ | ⟨rfl, h2⟩
    · exact T.not_anc_par hc ⟨j, hj⟩
    · exact T.not_anc_par hc ⟨1, h2⟩

private lemma Rooted.avoid_root {V : Type} (T : Rooted V) {c u : V} (hc : c ≠ T.root)
    (h : ¬T.Anc c u) : Avoid T.graph s(c, T.par c) u T.root := by
  suffices ∀ n u, T.hgt u < n → ¬T.Anc c u → Avoid T.graph s(c, T.par c) u T.root from
    this _ u (Nat.lt_succ_self _) h
  intro n
  induction n with
  | zero => exact fun u hu => absurd hu (Nat.not_lt_zero _)
  | succ n ih =>
    intro u hu h
    by_cases hr : u = T.root
    · rw [hr]; exact avoid_refl
    · refine avoid_trans (T.avoid_par hr fun he => ?_)
        (ih _ (by have := T.hgt_par u hr; omega) fun h' => h (T.anc_of_anc_par h'))
      rcases Sym2.eq_iff.mp he with ⟨rfl, -⟩ | ⟨-, h2⟩
      · exact h (T.anc_refl _)
      · exact h ⟨1, h2⟩

/-- The edge from `c` to its parent separates `u` from `v` iff `c` is an ancestor of exactly one
of them. -/
private lemma Rooted.avoid_iff {V : Type} (T : Rooted V) {c : V} (hc : c ≠ T.root) (u v : V) :
    Avoid T.graph s(c, T.par c) u v ↔ (T.Anc c u ↔ T.Anc c v) := by
  have key : ∀ {u v : V}, Avoid T.graph s(c, T.par c) u v → T.Anc c u → T.Anc c v := by
    rintro u v ⟨p, hp⟩ hu
    by_contra hv
    obtain ⟨dd, hdd, h1, h2⟩ := p.exists_boundary_dart {x | T.Anc c x} hu hv
    have hedge : dd.edge ∈ p.edges := List.mem_map_of_mem hdd
    rcases T.graph_adj.mp dd.adj with ⟨hne, hpar⟩ | ⟨hne, hpar⟩
    · rcases (T.anc_iff hne).mp h1 with heq | h'
      · apply hp
        have h3 : dd.edge = s(c, T.par c) := by
          change s(dd.fst, dd.snd) = _
          rw [hpar, ← heq]
        exact h3 ▸ hedge
      · exact h2 (hpar ▸ h')
    · exact h2 (T.anc_of_anc_par (hpar ▸ h1))
  refine ⟨fun h => ⟨key h, key (avoid_symm h)⟩, fun h => ?_⟩
  by_cases hu : T.Anc c u
  · exact avoid_trans (T.avoid_of_anc hc hu) (avoid_symm (T.avoid_of_anc hc (h.mp hu)))
  · exact avoid_trans (T.avoid_root hc hu)
      (avoid_symm (T.avoid_root hc fun hv => hu (h.mpr hv)))

private lemma Rooted.mem_edgeSet {V : Type} (T : Rooted V) (e : Sym2 V) :
    e ∈ T.graph.edgeSet ↔ ∃ c, c ≠ T.root ∧ s(c, T.par c) = e := by
  induction e using Sym2.ind with
  | h u v =>
    rw [SimpleGraph.mem_edgeSet, T.graph_adj]
    constructor
    · rintro (⟨hu, rfl⟩ | ⟨hv, rfl⟩)
      · exact ⟨u, hu, rfl⟩
      · exact ⟨v, hv, Sym2.eq_swap⟩
    · rintro ⟨c, hc, he⟩
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨hc, rfl⟩
      · exact Or.inr ⟨hc, rfl⟩

private lemma Rooted.isTree {V : Type} (T : Rooted V) : T.graph.IsTree := by
  have hreach : ∀ n v, T.hgt v < n → T.graph.Reachable T.root v := by
    intro n
    induction n with
    | zero => exact fun v hv => absurd hv (Nat.not_lt_zero _)
    | succ n ih =>
      intro v hv
      by_cases hr : v = T.root
      · rw [hr]
      · exact (ih _ (by have := T.hgt_par v hr; omega)).trans (T.adj_par hr).reachable.symm
  refine ⟨(SimpleGraph.connected_iff_exists_forall_reachable _).mpr
    ⟨T.root, fun v => hreach _ v (Nat.lt_succ_self _)⟩, ?_⟩
  rw [SimpleGraph.isAcyclic_iff_forall_isBridge]
  intro e he
  obtain ⟨c, hc, rfl⟩ := (T.mem_edgeSet e).mp he
  rw [SimpleGraph.isBridge_iff_forall_walk_mem_edges]
  intro p
  by_contra hp
  exact T.not_anc_par hc (((T.avoid_iff hc c (T.par c)).mp ⟨p, hp⟩).mp (T.anc_refl c))

open scoped Classical in
/-- Edge lengths: the edge from `c` to its parent has length `W c`. -/
private noncomputable def Rooted.edgeWeight {V : Type} [Fintype V] (T : Rooted V) (W : V → ℝ)
    (e : Sym2 V) : ℝ :=
  ∑ c with c ≠ T.root ∧ s(c, T.par c) = e, W c

open scoped Classical in
private lemma Rooted.path_sum {V : Type} [Fintype V] (T : Rooted V) (W : V → ℝ) {u v : V}
    {p : T.graph.Walk u v} (hp : p.IsPath) :
    (p.edges.map (T.edgeWeight W)).sum =
      ∑ c with c ≠ T.root ∧ ¬(T.Anc c u ↔ T.Anc c v), W c := by
  have hmem : ∀ c, c ≠ T.root → (s(c, T.par c) ∈ p.edges ↔ ¬(T.Anc c u ↔ T.Anc c v)) :=
    fun c hc => by rw [mem_edges_iff_not_avoid T.isTree.isAcyclic hp, T.avoid_iff hc]
  have hmaps : ∀ c ∈ (Finset.univ.filter fun c => c ≠ T.root ∧ ¬(T.Anc c u ↔ T.Anc c v)),
      s(c, T.par c) ∈ p.edges.toFinset := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    exact List.mem_toFinset.mpr ((hmem c hc.1).mpr hc.2)
  rw [← List.sum_toFinset _ hp.edges_nodup, ← Finset.sum_fiberwise_of_maps_to hmaps W]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [Rooted.edgeWeight, Finset.filter_filter]
  refine Finset.sum_congr (Finset.filter_congr fun c _ => ?_) fun _ _ => rfl
  constructor
  · rintro ⟨hc, rfl⟩
    exact ⟨⟨hc, (hmem c hc).mp (List.mem_toFinset.mp he)⟩, rfl⟩
  · rintro ⟨⟨hc, -⟩, rfl⟩
    exact ⟨hc, rfl⟩

open scoped Classical in
/-- Total length of the edges on the way from `v` up to the root. -/
private noncomputable def Rooted.depth {V : Type} [Fintype V] (T : Rooted V) (W : V → ℝ)
    (v : V) : ℝ :=
  ∑ c with c ≠ T.root ∧ T.Anc c v, W c

private lemma Rooted.depth_root {V : Type} [Fintype V] (T : Rooted V) (W : V → ℝ) :
    T.depth W T.root = 0 := by
  classical
  refine Finset.sum_eq_zero fun c hc => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
  exact absurd (T.eq_root_of_anc_root hc.2) hc.1

private lemma Rooted.depth_of_ne_root {V : Type} [Fintype V] (T : Rooted V) (W : V → ℝ)
    {v : V} (hv : v ≠ T.root) : T.depth W v = W v + T.depth W (T.par v) := by
  classical
  unfold Rooted.depth
  rw [← Finset.sum_insert (by simp [T.not_anc_par hv])]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, T.anc_iff hv]
  constructor
  · rintro ⟨hc, rfl | h⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hc, h⟩
  · rintro (rfl | ⟨hc, h⟩)
    · exact ⟨hv, Or.inl rfl⟩
    · exact ⟨hc, Or.inr h⟩

open scoped Classical in
private lemma Rooted.sum_xor {V : Type} [Fintype V] (T : Rooted V) (W : V → ℝ) (u v m : V)
    (hm : ∀ c, T.Anc c u ∧ T.Anc c v ↔ T.Anc c m) :
    ∑ c with c ≠ T.root ∧ ¬(T.Anc c u ↔ T.Anc c v), W c =
      T.depth W u + T.depth W v - 2 * T.depth W m := by
  simp only [Rooted.depth, Finset.sum_filter, Finset.mul_sum]
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← hm c]
  by_cases h1 : c = T.root <;> by_cases h2 : T.Anc c u <;> by_cases h3 : T.Anc c v <;>
    simp [h1, h2, h3, two_mul]

/-- A symmetric `ℕ`-valued function with `min (lvl x y) (lvl y z) ≤ lvl x z`. -/
private structure LevelFn (X : Type) where
  lvl : X → X → ℕ
  comm : ∀ x y, lvl x y = lvl y x
  le_self : ∀ x y, lvl x y ≤ lvl x x
  min_le : ∀ x y z, min (lvl x y) (lvl y z) ≤ lvl x z

/-- `(x, k)` and `(y, k)` are identified when the branches of `x` and `y` agree up to `k`. -/
private def LevelFn.setoid {X : Type} (L : LevelFn X) :
    Setoid (Σ x : X, Fin (L.lvl x x + 1)) where
  r a b := (a.2 : ℕ) = b.2 ∧ (a.2 : ℕ) ≤ L.lvl a.1 b.1
  iseqv := {
    refl := fun a => ⟨rfl, Nat.lt_succ_iff.mp a.2.isLt⟩
    symm := fun h => ⟨h.1.symm, h.1.symm.le.trans (h.2.trans (L.comm _ _).le)⟩
    trans := fun h₁ h₂ =>
      ⟨h₁.1.trans h₂.1, (le_min h₁.2 (h₁.1.le.trans h₂.2)).trans (L.min_le _ _ _)⟩ }

/-- The vertices of the tree built from `L`. -/
private abbrev LevelFn.V {X : Type} (L : LevelFn X) : Type := Quotient L.setoid

private noncomputable instance LevelFn.fintypeV {X : Type} [Fintype X] (L : LevelFn X) :
    Fintype L.V := by
  classical
  exact Quotient.fintype _

/-- The point at level `k` on the branch of `x`. -/
private def LevelFn.pt {X : Type} (L : LevelFn X) (x : X) (k : ℕ) (hk : k ≤ L.lvl x x) : L.V :=
  Quotient.mk L.setoid ⟨x, ⟨k, Nat.lt_succ_of_le hk⟩⟩

private lemma LevelFn.pt_eq_pt {X : Type} (L : LevelFn X) {x y : X} {k j : ℕ}
    (hk : k ≤ L.lvl x x) (hj : j ≤ L.lvl y y) :
    L.pt x k hk = L.pt y j hj ↔ k = j ∧ k ≤ L.lvl x y :=
  Quotient.eq

private lemma LevelFn.pt_congr {X : Type} (L : LevelFn X) {x : X} {k k' : ℕ}
    (hk : k ≤ L.lvl x x) (hk' : k' ≤ L.lvl x x) (h : k = k') : L.pt x k hk = L.pt x k' hk' := by
  subst h
  rfl

@[elab_as_elim]
private lemma LevelFn.ind {X : Type} (L : LevelFn X) {motive : L.V → Prop}
    (h : ∀ x k hk, motive (L.pt x k hk)) (v : L.V) : motive v :=
  Quotient.ind (fun a => h a.1 a.2 (Nat.lt_succ_iff.mp a.2.isLt)) v

/-- Moving one level down towards the root. -/
private def LevelFn.par {X : Type} (L : LevelFn X) : L.V → L.V :=
  Quotient.lift (fun a => L.pt a.1 (a.2 - 1) (by have := a.2.isLt; omega))
    fun a b h => (L.pt_eq_pt _ _).mpr ⟨by rw [h.1], by have := h.2; omega⟩

/-- The level of a vertex. -/
private def LevelFn.hgt {X : Type} (L : LevelFn X) : L.V → ℕ :=
  Quotient.lift (fun a => (a.2 : ℕ)) fun _ _ h => h.1

/-- The rooted tree built from `L`, rooted at level `0`. -/
private def LevelFn.rooted {X : Type} (L : LevelFn X) (x₀ : X) : Rooted L.V where
  par := L.par
  root := L.pt x₀ 0 (Nat.zero_le _)
  hgt := L.hgt
  par_root := rfl
  hgt_par v hv := by
    induction v using L.ind with
    | h x k hk =>
      change k - 1 < k
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · exact absurd ((L.pt_eq_pt _ _).mpr ⟨rfl, Nat.zero_le _⟩) hv
      · omega

private lemma LevelFn.pt_zero {X : Type} (L : LevelFn X) (x₀ x : X) (hk : 0 ≤ L.lvl x x) :
    L.pt x 0 hk = (L.rooted x₀).root :=
  (L.pt_eq_pt hk (Nat.zero_le _)).mpr ⟨rfl, Nat.zero_le _⟩

private lemma LevelFn.pt_ne_root {X : Type} (L : LevelFn X) (x₀ x : X) {k : ℕ}
    (hk : k ≤ L.lvl x x) (h0 : k ≠ 0) : L.pt x k hk ≠ (L.rooted x₀).root :=
  fun h => h0 ((L.pt_eq_pt hk (Nat.zero_le _)).mp h).1

private lemma LevelFn.rooted_par_pt {X : Type} (L : LevelFn X) (x₀ x : X) (k : ℕ)
    (hk : k ≤ L.lvl x x) : (L.rooted x₀).par (L.pt x k hk) = L.pt x (k - 1) (by omega) :=
  rfl

private lemma LevelFn.iterate_par {X : Type} (L : LevelFn X) (x₀ x : X) (k : ℕ)
    (hk : k ≤ L.lvl x x) (j : ℕ) :
    (L.rooted x₀).par^[j] (L.pt x k hk) = L.pt x (k - j) (by omega) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, L.rooted_par_pt]
    exact L.pt_congr _ _ (by omega)

private lemma LevelFn.anc_pt_iff {X : Type} (L : LevelFn X) (x₀ : X) {x z : X} {k m : ℕ}
    (hk : k ≤ L.lvl x x) (hm : m ≤ L.lvl z z) :
    (L.rooted x₀).Anc (L.pt z m hm) (L.pt x k hk) ↔ m ≤ k ∧ m ≤ L.lvl x z := by
  constructor
  · rintro ⟨j, hj⟩
    rw [L.iterate_par, L.pt_eq_pt] at hj
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨k - m, ?_⟩
    rw [L.iterate_par, L.pt_eq_pt]
    omega

/-- The length `f k - f (k - 1)` of the edge from a vertex at level `k` to its parent. -/
private def LevelFn.weight {X : Type} (L : LevelFn X) (f : ℕ → ℝ) : L.V → ℝ :=
  Quotient.lift (fun a => f a.2 - f (a.2 - 1)) fun a b h => by
    change (a.2 : ℕ) = b.2 ∧ _ at h
    rw [h.1]

private lemma LevelFn.depth_pt {X : Type} [Fintype X] (L : LevelFn X) (x₀ : X) (f : ℕ → ℝ)
    (x : X) (k : ℕ) (hk : k ≤ L.lvl x x) :
    (L.rooted x₀).depth (L.weight f) (L.pt x k hk) = f k - f 0 := by
  induction k with
  | zero => rw [L.pt_zero x₀, Rooted.depth_root, sub_self]
  | succ k ih =>
    rw [Rooted.depth_of_ne_root _ _ (L.pt_ne_root x₀ x hk (Nat.succ_ne_zero k))]
    have hpar : (L.rooted x₀).par (L.pt x (k + 1) hk) = L.pt x k (by omega) :=
      (L.rooted_par_pt x₀ x (k + 1) hk).trans (L.pt_congr _ _ (by omega))
    rw [hpar, ih]
    change f (k + 1) - f (k + 1 - 1) + (f k - f 0) = f (k + 1) - f 0
    rw [Nat.add_sub_cancel]
    ring

/-- The tree built from `L` realizes `f (lvl x x) + f (lvl y y) - 2 f (lvl x y)` when `f` is
strictly increasing on the levels used. -/
private lemma isTreeMetric_of_levelFn {X : Type} [Finite X] [Nonempty X] (L : LevelFn X)
    (f : ℕ → ℝ) (hf : ∀ x k, k + 1 ≤ L.lvl x x → f k < f (k + 1)) :
    IsTreeMetric fun x y => f (L.lvl x x) + f (L.lvl y y) - 2 * f (L.lvl x y) := by
  classical
  have := Fintype.ofFinite X
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have hpos : ∀ c, c ≠ (L.rooted x₀).root → 0 < L.weight f c := by
    intro c
    induction c using L.ind with
    | h z k hk =>
      intro hc
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hc (L.pt_zero x₀ z hk)
      have := hf z (k - 1) (by omega)
      change 0 < f k - f (k - 1)
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)] at this
      linarith
  refine ⟨L.V, inferInstance, (L.rooted x₀).graph, (L.rooted x₀).isTree,
    (L.rooted x₀).edgeWeight (L.weight f), fun x => L.pt x (L.lvl x x) le_rfl, ?_, ?_⟩
  · intro e he
    obtain ⟨c, hc, rfl⟩ := ((L.rooted x₀).mem_edgeSet e).mp he
    refine Finset.sum_pos (fun c' hc' => hpos c' ?_) ⟨c, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc'
      exact hc'.1
    · simp [hc]
  · intro x y p hp
    have hm : ∀ c, (L.rooted x₀).Anc c (L.pt x (L.lvl x x) le_rfl) ∧
        (L.rooted x₀).Anc c (L.pt y (L.lvl y y) le_rfl) ↔
          (L.rooted x₀).Anc c (L.pt x (L.lvl x y) (L.le_self x y)) := by
      intro c
      induction c using L.ind with
      | h z m hm =>
        rw [L.anc_pt_iff, L.anc_pt_iff, L.anc_pt_iff]
        have h1 := min_le_iff.mp (L.min_le x z y)
        have h2 := min_le_iff.mp (L.min_le y x z)
        have h3 := L.comm z y
        have h4 := L.comm x y
        have h5 := L.le_self x y
        have h6 := L.le_self y x
        omega
    rw [(L.rooted x₀).path_sum _ hp, (L.rooted x₀).sum_xor _ _ _ _ hm, L.depth_pt, L.depth_pt,
      L.depth_pt]
    ring

/-- Ranking the values of `g` turns it into a `LevelFn` together with a strictly increasing
`f` such that `f (lvl x y) = g x y`. -/
private lemma exists_levelFn {X : Type} [Finite X] (g : X → X → ℝ)
    (hcomm : ∀ x y, g x y = g y x) (hle : ∀ x y, g x y ≤ g x x)
    (hmin : ∀ x y z, min (g x y) (g y z) ≤ g x z) :
    ∃ (L : LevelFn X) (f : ℕ → ℝ), (∀ x y, f (L.lvl x y) = g x y) ∧
      ∀ x k, k + 1 ≤ L.lvl x x → f k < f (k + 1) := by
  classical
  have := Fintype.ofFinite X
  let H : Finset ℝ := Finset.univ.image fun p : X × X => g p.1 p.2
  have hmem : ∀ x y, g x y ∈ H := fun x y => Finset.mem_image_of_mem _ (Finset.mem_univ (x, y))
  let σ := H.orderIsoOfFin rfl
  let lv : X → X → ℕ := fun x y => (σ.symm ⟨g x y, hmem x y⟩ : Fin H.card)
  have hlv : ∀ x y x' y', lv x y ≤ lv x' y' ↔ g x y ≤ g x' y' := by
    intro x y x' y'
    simp only [lv]
    rw [← Fin.le_iff_val_le_val, OrderIso.le_iff_le, Subtype.mk_le_mk]
  have hlt : ∀ x y, lv x y < H.card := fun x y => Fin.isLt _
  let f : ℕ → ℝ := fun k => if hk : k < H.card then H.orderEmbOfFin rfl ⟨k, hk⟩ else 0
  refine ⟨⟨lv, fun x y => le_antisymm ((hlv _ _ _ _).mpr (hcomm x y).le)
      ((hlv _ _ _ _).mpr (hcomm y x).le), fun x y => (hlv _ _ _ _).mpr (hle x y),
      fun x y z => ?_⟩, f, fun x y => ?_, fun x k hk => ?_⟩
  · rcases min_le_iff.mp (hmin x y z) with h | h
    · exact min_le_of_left_le ((hlv _ _ _ _).mpr h)
    · exact min_le_of_right_le ((hlv _ _ _ _).mpr h)
  · change f (lv x y) = g x y
    simp only [f, dite_eq_left (hlt x y)]
    rw [← Finset.coe_orderIsoOfFin_apply]
    simp [lv, σ]
  · change k + 1 ≤ lv x x at hk
    have h1 := hlt x x
    change f k < f (k + 1)
    simp only [f, dite_eq_left (show k < H.card by omega),
      dite_eq_left (show k + 1 < H.card by omega)]
    exact (H.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self k))

private lemma isTreeMetric_of_isEmpty {X : Type*} [IsEmpty X] (d : X → X → ℝ) :
    IsTreeMetric d := by
  let T : Rooted Unit := ⟨id, (), fun _ => 0, rfl, fun _ hv => absurd rfl hv⟩
  exact ⟨Unit, inferInstance, T.graph, T.isTree, fun _ => 1, isEmptyElim,
    fun _ _ => one_pos, fun x => isEmptyElim x⟩

/-- The converse direction for a finite type in `Type`, via the Gromov products at a base point
(Farris transform). -/
private lemma isTreeMetric_aux {X : Type} [Finite X] (d : X → X → ℝ) (hdiag : ∀ x, d x x = 0)
    (hsymm : ∀ x y, d x y = d y x) (h : FourPointCondition d) : IsTreeMetric d := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨r⟩⟩
  · exact isTreeMetric_of_isEmpty d
  have : Nonempty X := ⟨r⟩
  have htri : ∀ x y z, d x y ≤ d x z + d y z := fun x y z => by
    have := h x y z z
    rw [hdiag, max_self] at this
    linarith
  obtain ⟨L, f, hfL, hf⟩ := exists_levelFn (fun x y => (d r x + d r y - d x y) / 2)
    (fun x y => by rw [hsymm x y]; ring)
    (fun x y => by linarith [htri r y x, hsymm y x, hdiag x])
    (fun x y z => by
      rcases le_max_iff.mp (h x z y r) with h1 | h1
      · exact (min_le_left _ _).trans (by linarith [hsymm y r, hsymm z r])
      · exact (min_le_right _ _).trans (by linarith [hsymm y r, hsymm x r, hsymm z y]))
  have hd : d = fun x y => f (L.lvl x x) + f (L.lvl y y) - 2 * f (L.lvl x y) := by
    funext x y
    simp only [hfL, hdiag]
    ring
  rw [hd]
  exact isTreeMetric_of_levelFn L f hf

/-- **Buneman's theorem, converse direction.** A symmetric dissimilarity on a finite set that
vanishes on the diagonal and satisfies the four-point condition is a tree metric.

Source: Buneman (1974); Semple & Steel (2003), Theorem 7.2.6. -/
theorem isTreeMetric_of_fourPointCondition {X : Type*} [Finite X] (d : X → X → ℝ)
    (hdiag : ∀ x, d x x = 0) (hsymm : ∀ x y, d x y = d y x) (h : FourPointCondition d) :
    IsTreeMetric d := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin X
  obtain ⟨V, hV, G, hG, w, ι, hw, hdist⟩ :=
    isTreeMetric_aux (fun i j => d (e.symm i) (e.symm j)) (fun _ => hdiag _)
      (fun _ _ => hsymm _ _) (fun _ _ _ _ => h _ _ _ _)
  refine ⟨V, hV, G, hG, w, ι ∘ e, hw, fun x y p hp => ?_⟩
  simpa using hdist (e x) (e y) p hp

/-- **Buneman's four-point theorem.** A symmetric dissimilarity on a finite set that vanishes on
the diagonal is a tree metric if and only if it satisfies the four-point condition.

Source: Buneman (1974); Semple & Steel (2003), Theorem 7.2.6. -/
theorem isTreeMetric_iff_fourPointCondition {X : Type*} [Finite X] (d : X → X → ℝ)
    (hdiag : ∀ x, d x x = 0) (hsymm : ∀ x y, d x y = d y x) :
    IsTreeMetric d ↔ FourPointCondition d :=
  ⟨IsTreeMetric.fourPointCondition, isTreeMetric_of_fourPointCondition d hdiag hsymm⟩

end MathlibExt.Biology.Phylogenetics.Buneman
