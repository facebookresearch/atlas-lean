/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import MathlibExt.Combinatorics.SimpleGraph.Circumference
import Mathlib.Combinatorics.Compactness
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Erdős Problem 751 is false

Erdős asked whether for every `k` there is a graph of chromatic number `4` any two of whose
cycle lengths differ by at least `k`, and whether such graphs exist with arbitrarily large girth
(Erdős Problem 751, `conjecture`). Bondy and Vince showed that every finite graph of minimum degree
at least three has two cycles whose lengths differ by one or two
(`exists_cycleLengths_lt_le_add_two_of_three_le_minDegree`). The same conclusion holds for every
graph that is not `3`-colourable (`exists_cycleLengths_lt_le_add_two_of_not_colorable`), giving a
negative answer to both questions (`conjecture_refuted`).

## Proof

The proof is self-contained. A graph that is not `3`-colourable has a finite vertex set that is
not `3`-colourable (the de Bruijn–Erdős compactness argument, via `Finset.rado_selection`), and
that set contains a nonempty set `S` in which every vertex has at least three neighbours.

The main step shows, by strong induction on `|S|`, that a finite set `S` with at least two
vertices, at most one of which has fewer than three neighbours in `S`, carries two cycles whose
lengths differ by one or two. Choose a cycle `C` in `S` and a connected set `D ⊆ S` off `C` with
`|D|` as large as possible; this choice is modelled on the lemma of Bondy and Vince quoted in
J. Gao and J. Ma, *On a conjecture of Bondy and Vince*, arXiv:1902.05701. If `D`, or a piece of
`S` hanging off `C`, has neighbours in at most one vertex of `C`, the induction hypothesis applies
to a smaller set. Otherwise the maximality of `D` shows, by rerouting `C` through a chord or
through another piece of `S`, that every vertex of `C` without a neighbour in `D` has only its two
neighbours on `C` in `S`. So at most one vertex of `C` has no neighbour in `D`, and a path through
`D` between two vertices at distance `⌊(|C| - 1) / 2⌋` along `C` closes, with the two arcs of `C`
between them, two cycles whose lengths differ by one or two.

## Main declarations

* `conjecture`: the statement of Erdős Problem 751.
* `exists_cycleLengths_lt_le_add_two_of_three_le_minDegree`: a finite graph of minimum degree at
  least three has two cycle lengths `m < m' ≤ m + 2`.
* `exists_cycleLengths_lt_le_add_two_of_not_colorable`: so has every graph that is not
  `3`-colourable.
* `conjecture_refuted`: Erdős Problem 751 is false.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem751Wanted

/-! Source record `FC-ErdosProblem751`, ported from FormalConjectures
`ErdosProblems/751.lean` and checked against erdosproblems.com/751.
`SimpleGraph.cycleLengths` is MathlibExt's (ported from FC's
`FormalConjecturesForMathlib`).
The two original arbitrarily-large-gap propositions are preserved without
their `answer(False)` wrappers. Status: resolved false by Bondy--Vince. -/

/-- **Erdős Problem 751.** The statement that both of the following hold:
(i) for every natural number $k$ there is a simple graph $G$ with chromatic number $4$ in
which any two distinct cycle lengths of $G$ differ by at least $k$; (ii) for all natural numbers
$k$ and $g$ there is a simple graph $G$ with chromatic number $4$ and girth at least $g$ in which
any two distinct cycle lengths of $G$ differ by at least $k$. -/
def conjecture : Prop :=
  (∀ k : ℕ, ∃ (V : Type) (G : SimpleGraph V), G.chromaticNumber = 4 ∧
    ∀ m ∈ G.cycleLengths, ∀ m' ∈ G.cycleLengths, m < m' → m + k ≤ m') ∧
  (∀ k g : ℕ, ∃ (V : Type) (G : SimpleGraph V), G.chromaticNumber = 4 ∧
    g ≤ G.girth ∧
    ∀ m ∈ G.cycleLengths, ∀ m' ∈ G.cycleLengths, m < m' → m + k ≤ m')

open SimpleGraph Walk

variable {V : Type*} {G : SimpleGraph V}

/-- Two paths `Q : x ⟶ y` and `R : y ⟶ x` that meet only at `x` and `y` and share no edge
form a cycle `Q ++ R`. -/
private theorem isCycle_append_of_isPath {x y : V} {Q : G.Walk x y} {R : G.Walk y x}
    (hQ : Q.IsPath) (hR : R.IsPath) (hxy : x ≠ y)
    (hsupp : ∀ z ∈ Q.support, z ∈ R.support → z = x ∨ z = y)
    (hedge : ∀ e ∈ Q.edges, e ∉ R.edges) : (Q.append R).IsCycle := by
  cases Q with
  | nil => exact absurd rfl hxy
  | cons h Q' =>
    rw [cons_append, cons_isCycle_iff]
    have hQ' := (cons_isPath_iff _ _).mp hQ
    have hRn := hR.support_nodup
    rw [← cons_tail_support, List.nodup_cons] at hRn
    refine ⟨?_, ?_⟩
    · rw [isPath_def, support_append, List.nodup_append]
      refine ⟨hQ'.1.support_nodup, hRn.2, ?_⟩
      intro z hz1 z' hz2 hzz'
      subst hzz'
      rcases hsupp z (by simp [hz1]) (List.mem_of_mem_tail hz2) with rfl | rfl
      · exact hQ'.2 hz1
      · exact hRn.1 hz2
    · rw [edges_append, List.mem_append, not_or]
      exact ⟨fun h' => hQ'.2 (Q'.fst_mem_support_of_mem_edges h'),
        fun h' => hedge _ (by simp) h'⟩

/-- A finite set `D` of vertices is connected in `G` if any two of its vertices are joined by a
walk inside `D`. -/
private def Conn (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, ∃ p : G.Walk x y, ∀ z ∈ p.support, z ∈ D

/-- A single vertex is connected. -/
private theorem conn_singleton (v : V) : Conn G {v} := by
  intro x hx y hy
  rw [Finset.mem_singleton] at hx hy
  subst hx hy
  exact ⟨nil, by simp⟩

/-- Adding a vertex adjacent to a connected set keeps it connected. -/
private theorem conn_insert [DecidableEq V] {D : Finset V} (hD : Conn G D) {a x : V} (hx : x ∈ D)
    (hax : G.Adj a x) : Conn G (insert a D) := by
  have key : ∀ y ∈ D, ∃ p : G.Walk a y, ∀ z ∈ p.support, z ∈ insert a D := by
    intro y hy
    obtain ⟨p, hp⟩ := hD x hx y hy
    refine ⟨cons hax p, fun z hz => ?_⟩
    rw [support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hp z hz)
  intro y hy z hz
  rw [Finset.mem_insert] at hy hz
  rcases hy with rfl | hy <;> rcases hz with rfl | hz
  · exact ⟨nil, by simp⟩
  · exact key z hz
  · obtain ⟨p, hp⟩ := key y hy
    exact ⟨p.reverse, by simpa using hp⟩
  · obtain ⟨p, hp⟩ := hD y hy z hz
    exact ⟨p, fun w hw => Finset.mem_insert_of_mem (hp w hw)⟩

/-- Two distinct vertices `c, c'` outside a connected set `D`, with neighbours `x, y` in `D`, are
joined by a path of length at least two whose inner vertices lie in `D` and each of whose edges
has an end in `D`. -/
private theorem exists_path_through {D : Finset V} (hD : Conn G D) {c c' x y : V}
    (hc : c ∉ D) (hc' : c' ∉ D) (hcc' : c ≠ c') (hx : x ∈ D) (hy : y ∈ D)
    (hcx : G.Adj c x) (hyc' : G.Adj y c') :
    ∃ Q : G.Walk c c', Q.IsPath ∧ 2 ≤ Q.length ∧ (∀ z ∈ Q.support, z = c ∨ z = c' ∨ z ∈ D) ∧
      ∀ e ∈ Q.edges, ∃ z ∈ D, z ∈ e := by
  classical
  obtain ⟨p, hp⟩ := hD x hx y hy
  have hqD : ∀ z ∈ p.bypass.support, z ∈ D :=
    fun z hz => hp z (p.support_bypass_subset_support hz)
  refine ⟨cons hcx (p.bypass.concat hyc'), ?_, ?_, ?_, ?_⟩
  · rw [cons_isPath_iff, isPath_concat]
    refine ⟨⟨p.bypass_isPath, fun h => hc' (hqD _ h)⟩, ?_⟩
    rw [support_concat, List.mem_append, List.mem_singleton]
    rintro (h | h)
    · exact hc (hqD _ h)
    · exact hcc' h
  · simp [length_concat]
  · intro z hz
    rw [support_cons, List.mem_cons, support_concat, List.mem_append,
      List.mem_singleton] at hz
    rcases hz with rfl | hz | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (hqD _ hz))
    · exact Or.inr (Or.inl rfl)
  · intro e he
    rw [edges_cons, List.mem_cons, edges_concat, List.concat_eq_append, List.mem_append,
      List.mem_singleton] at he
    rcases he with rfl | he | rfl
    · exact ⟨x, hx, Sym2.mem_mk_right _ _⟩
    · induction e using Sym2.ind with
      | h a b => exact ⟨a, hqD _ (p.bypass.fst_mem_support_of_mem_edges he), Sym2.mem_mk_left _ _⟩
    · exact ⟨y, hy, Sym2.mem_mk_left _ _⟩

/-- If no vertex of `S` outside `D` and outside `P` is adjacent to `D`, then a walk in `S` avoiding
`P` that starts outside `D` never enters `D`. -/
private theorem walk_avoid {S D : Finset V} {P : V → Prop}
    (hclos : ∀ z ∈ S, z ∉ D → ¬ P z → ∀ x ∈ D, ¬ G.Adj z x) {w y : V} (p : G.Walk w y)
    (hp : ∀ z ∈ p.support, z ∈ S ∧ ¬ P z) (hw : w ∉ D) : ∀ z ∈ p.support, z ∉ D := by
  induction p with
  | nil =>
    intro z hz
    rw [support_nil, List.mem_singleton] at hz
    exact hz ▸ hw
  | cons h p ih =>
    rename_i a b _
    intro z hz
    rw [support_cons, List.mem_cons] at hz
    have hb : b ∉ D := by
      intro hbD
      have ha := hp a (by simp)
      exact hclos a ha.1 hw ha.2 b hbD h
    rcases hz with rfl | hz
    · exact hw
    · exact ih (fun z hz => hp z (by simp [hz])) hb z hz

/-- Two distinct vertices `c, c'` of a cycle `C` split it into two paths from `c'` to `c`, whose
vertices and edges are those of `C`, and which share no vertex other than `c` and `c'`. -/
private theorem exists_arcs {v c c' : V} {C : G.Walk v v} (hC : C.IsCycle)
    (hc : c ∈ C.support) (hc' : c' ∈ C.support) (hcc' : c ≠ c') :
    ∃ R₁ R₂ : G.Walk c' c, R₁.IsPath ∧ R₂.IsPath ∧
      (∀ z ∈ R₁.support, z ∈ C.support) ∧ (∀ z ∈ R₂.support, z ∈ C.support) ∧
      (∀ e ∈ R₁.edges, e ∈ C.edges) ∧ (∀ e ∈ R₂.edges, e ∈ C.edges) ∧
      ∀ z ∈ C.support, z ≠ c → z ≠ c' → z ∉ R₁.support ∨ z ∉ R₂.support := by
  classical
  have hCc : (C.rotate c hc).IsCycle := hC.rotate hc
  have hc'' : c' ∈ (C.rotate c hc).support := (mem_support_rotate_iff _ _ _).mpr hc'
  set Cc := C.rotate c hc with hCcdef
  have hspec := take_spec Cc hc''
  have hsupp : ∀ z, z ∈ Cc.support ↔ z ∈ C.support := fun z => mem_support_rotate_iff _ _ _
  have hedges : ∀ e, e ∈ Cc.edges ↔ e ∈ C.edges := fun e => (rotate_edges C c hc).mem_iff
  refine ⟨(Cc.takeUntil c' hc'').reverse, Cc.dropUntil c' hc'', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hCc.isPath_takeUntil hc'').reverse
  · rw [← hspec] at hCc
    exact hCc.isPath_of_append_right (not_nil_of_ne hcc')
  · intro z hz
    rw [support_reverse, List.mem_reverse] at hz
    exact (hsupp z).mp (Cc.support_takeUntil_subset_support hc'' hz)
  · intro z hz
    exact (hsupp z).mp (Cc.support_dropUntil_subset_support hc'' hz)
  · intro e he
    rw [edges_reverse, List.mem_reverse] at he
    exact (hedges e).mp (Cc.edges_takeUntil_subset_edges hc'' he)
  · intro e he
    exact (hedges e).mp (Cc.edges_dropUntil_subset_edges hc'' he)
  · intro z hz hzc hzc'
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    rw [support_reverse, List.mem_reverse] at h1
    have hnd := hCc.support_nodup
    rw [← hspec, tail_support_append, List.nodup_append] at hnd
    have h1' : z ∈ (Cc.takeUntil c' hc'').support.tail := by
      rw [← cons_tail_support, List.mem_cons] at h1
      exact h1.resolve_left hzc
    have h2' : z ∈ (Cc.dropUntil c' hc'').support.tail := by
      rw [← cons_tail_support, List.mem_cons] at h2
      exact h2.resolve_left hzc'
    exact hnd.2.2 z h1' z h2' rfl

/-- `G` has two cycle lengths `m < m'` with `m' ≤ m + 2`. -/
private def CloseCycles (G : SimpleGraph V) : Prop :=
  ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2

/-- **Rerouting.** Let `C` be a cycle in `S` and `D ⊆ S` a connected set off `C` of maximum size
among all such pairs. A path `Q` in `S` between distinct vertices `c, c'` of `C`, avoiding `D` and
sharing no other vertex and no edge with `C`, cannot exist if some vertex `a ≠ c, c'` of `C` has a
neighbour in `D`: replacing the arc of `C` through `a` by `Q` would give a cycle off `D ∪ {a}`. -/
private theorem reroute {S D : Finset V} {v : V} {C : G.Walk v v} (hC : C.IsCycle)
    (hCS : ∀ z ∈ C.support, z ∈ S) (hDS : D ⊆ S) (hDconn : Conn G D)
    (hDC : ∀ z ∈ D, z ∉ C.support)
    (hmax : ∀ D' : Finset V, D' ⊆ S → Conn G D' → ∀ (u : V) (C' : G.Walk u u), C'.IsCycle →
      (∀ z ∈ C'.support, z ∈ S) → (∀ z ∈ D', z ∉ C'.support) → D'.card ≤ D.card)
    {c c' a x : V} (hc : c ∈ C.support) (hc' : c' ∈ C.support) (hcc' : c ≠ c')
    {Q : G.Walk c c'} (hQ : Q.IsPath) (hQS : ∀ z ∈ Q.support, z ∈ S)
    (hQC : ∀ z ∈ Q.support, z ∈ C.support → z = c ∨ z = c') (hQD : ∀ z ∈ Q.support, z ∉ D)
    (hQe : ∀ e ∈ Q.edges, e ∉ C.edges)
    (ha : a ∈ C.support) (hac : a ≠ c) (hac' : a ≠ c') (hx : x ∈ D) (hax : G.Adj a x) :
    False := by
  classical
  obtain ⟨R₁, R₂, hR₁, hR₂, hR₁C, hR₂C, hR₁e, hR₂e, hdisj⟩ := exists_arcs hC hc hc' hcc'
  have main : ∀ R : G.Walk c' c, R.IsPath → (∀ z ∈ R.support, z ∈ C.support) →
      (∀ e ∈ R.edges, e ∈ C.edges) → a ∉ R.support → False := by
    intro R hR hRC hRe haR
    have hcyc : (Q.append R).IsCycle := isCycle_append_of_isPath hQ hR hcc'
      (fun z hzQ hzR => hQC z hzQ (hRC z hzR)) (fun e heQ heR => hQe e heQ (hRe e heR))
    have hle := hmax (insert a D) (Finset.insert_subset (hCS a ha) hDS)
      (conn_insert hDconn hx hax) c (Q.append R) hcyc
      (by
        intro z hz
        rw [mem_support_append_iff] at hz
        rcases hz with hz | hz
        · exact hQS z hz
        · exact hCS z (hRC z hz))
      (by
        intro z hz hzC
        rw [Finset.mem_insert] at hz
        rw [mem_support_append_iff] at hzC
        rcases hz with rfl | hz
        · rcases hzC with hzC | hzC
          · rcases hQC z hzC ha with rfl | rfl
            · exact hac rfl
            · exact hac' rfl
          · exact haR hzC
        · rcases hzC with hzC | hzC
          · exact hQD z hzC hz
          · exact hDC z hz (hRC z hzC))
    have haD : a ∉ D := fun h => hDC a h ha
    rw [Finset.card_insert_of_notMem haD] at hle
    omega
  rcases hdisj a ha hac hac' with h | h
  · exact main R₁ hR₁ hR₁C hR₁e h
  · exact main R₂ hR₂ hR₂C hR₂e h

/-- **The pair argument.** If all vertices of a cycle `Cb`, except possibly its base vertex `b`,
have a neighbour in a connected set `D` off the cycle, then `G` has two cycle lengths that differ
by one or two: a path through `D` joining two vertices of `Cb` at distance `⌊(|Cb| - 1) / 2⌋`
along `Cb` closes two cycles with the two arcs of `Cb` between them. -/
private theorem closeCycles_of_attach {D : Finset V} (hDconn : Conn G D) {b : V}
    (Cb : G.Walk b b) (hC : Cb.IsCycle) (hDC : ∀ z ∈ D, z ∉ Cb.support)
    (hatt : ∀ z ∈ Cb.support, z ≠ b → ∃ x ∈ D, G.Adj z x) : CloseCycles G := by
  classical
  have hlen := hC.three_le_length
  cases Cb with
  | nil => exact absurd hC (by simp)
  | cons h P =>
    rename_i x₀
    rw [length_cons] at hlen
    have hP : P.IsPath := ((cons_isCycle_iff _ _).mp hC).1
    set ℓ := P.length with hℓ
    set d := ℓ / 2 with hd
    have hd1 : 1 ≤ d := by omega
    have hd2 : d < ℓ := by omega
    set y := P.getVert d with hy
    have hx₀b : x₀ ≠ b := (G.ne_of_adj h).symm
    have hyb : y ≠ b := by
      intro hyb
      have : P.getVert d = P.getVert ℓ := by rw [← hy, hyb, getVert_length]
      have := hP.getVert_injOn (by simp; omega) (by simp [hℓ]) this
      omega
    have hyx₀ : y ≠ x₀ := by
      intro hyx
      have : P.getVert d = P.getVert 0 := by rw [← hy, hyx, getVert_zero]
      have := hP.getVert_injOn (by simp; omega) (by simp) this
      omega
    have hsupp : ∀ z ∈ P.support, z ∈ (cons h P).support := fun z hz => by simp [hz]
    have hx₀C : x₀ ∈ (cons h P).support := hsupp _ P.start_mem_support
    have hyC : y ∈ (cons h P).support := hsupp _ (P.getVert_mem_support d)
    obtain ⟨dx, hdx, hx₀dx⟩ := hatt x₀ hx₀C hx₀b
    obtain ⟨dy, hdy, hydy⟩ := hatt y hyC hyb
    have hx₀D : x₀ ∉ D := fun h' => hDC x₀ h' hx₀C
    have hyD : y ∉ D := fun h' => hDC y h' hyC
    obtain ⟨Q, hQ, hQlen, hQsupp, hQe⟩ :=
      exists_path_through hDconn hx₀D hyD hyx₀.symm hdx hdy hx₀dx hydy.symm
    -- the two arcs of the cycle between `x₀` and `y`
    have hcycle : ∀ R : G.Walk y x₀, R.IsPath → (∀ z ∈ R.support, z ∈ (cons h P).support) →
        (Q.append R).IsCycle := by
      intro R hR hRC
      refine isCycle_append_of_isPath hQ hR hyx₀.symm (fun z hzQ hzR => ?_) (fun e heQ heR => ?_)
      · rcases hQsupp z hzQ with hz | hz | hz
        · exact Or.inl hz
        · exact Or.inr hz
        · exact absurd (hRC z hzR) (hDC z hz)
      · obtain ⟨z, hzD, hze⟩ := hQe e heQ
        exact hDC z hzD (hRC z (mem_support_of_mem_edges heR hze))
    have hR₁ : (P.take d).reverse.IsPath := (hP.take d).reverse
    have hR₁C : ∀ z ∈ (P.take d).reverse.support, z ∈ (cons h P).support := by
      intro z hz
      rw [support_reverse, List.mem_reverse] at hz
      exact hsupp z ((P.isSubwalk_take d).support_subset hz)
    have hx₀drop : x₀ ∉ (P.drop d).support := by
      intro hmem
      have hpath : ((P.take d).append (P.drop d)).IsPath := by rwa [append_take_drop_eq]
      exact hpath.ne_of_mem_support_of_append hyx₀.symm (P.take d).start_mem_support hmem rfl
    have hR₂ : ((P.drop d).concat h).IsPath := (isPath_concat h).mpr ⟨hP.drop d, hx₀drop⟩
    have hR₂C : ∀ z ∈ ((P.drop d).concat h).support, z ∈ (cons h P).support := by
      intro z hz
      rw [support_concat, List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact hsupp z ((P.isSubwalk_drop d).support_subset hz)
      · exact hx₀C
    refine ⟨(Q.append (P.take d).reverse).length, ⟨x₀, _, hcycle _ hR₁ hR₁C, rfl⟩,
      (Q.append ((P.drop d).concat h)).length, ⟨x₀, _, hcycle _ hR₂ hR₂C, rfl⟩, ?_, ?_⟩
    · simp only [length_append, length_reverse, take_length, length_concat, drop_length]
      omega
    · simp only [length_append, length_reverse, take_length, length_concat, drop_length]
      omega

/-- If `S` has at least two vertices and at most one of them has fewer than three neighbours in
`S`, then some cycle in `S` misses a vertex of `S`. Take a longest path in `S` and an end of it
with at least three neighbours in `S`; these neighbours lie on the path, and the cycle closed by
the nearer of two neighbours other than the second vertex misses the other one. -/
private theorem exists_cycle_avoiding [DecidableRel G.Adj] {S : Finset V}
    (hS : 2 ≤ S.card)
    (hlow : ∀ u ∈ S, ∀ w ∈ S, (S.filter (G.Adj u)).card < 3 →
      (S.filter (G.Adj w)).card < 3 → u = w) :
    ∃ (u : V) (C : G.Walk u u), C.IsCycle ∧ (∀ z ∈ C.support, z ∈ S) ∧
      ∃ z ∈ S, z ∉ C.support := by
  classical
  have hbound : ∀ (a b : V) (p : G.Walk a b), p.IsPath → (∀ z ∈ p.support, z ∈ S) →
      p.length < S.card := by
    intro a b p hp hpS
    have h1 : p.support.toFinset ⊆ S := fun z hz => hpS z (List.mem_toFinset.mp hz)
    have h2 := Finset.card_le_card h1
    rw [List.toFinset_card_of_nodup hp.support_nodup, length_support] at h2
    omega
  let L : Finset ℕ := (Finset.range S.card).filter (fun n => ∃ (a b : V) (p : G.Walk a b),
    p.IsPath ∧ (∀ z ∈ p.support, z ∈ S) ∧ p.length = n)
  obtain ⟨s₀, hs₀⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hLne : L.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
    s₀, s₀, nil, by simp, by simpa using hs₀, rfl⟩⟩
  set n₀ := L.max' hLne with hn₀
  have hmaxL : ∀ (a b : V) (p : G.Walk a b), p.IsPath → (∀ z ∈ p.support, z ∈ S) →
      p.length ≤ n₀ := fun a b p hp hpS => L.le_max' _ (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (hbound a b p hp hpS), a, b, p, hp, hpS, rfl⟩)
  obtain ⟨a, b, P, hP, hPS, hPlen⟩ := (Finset.mem_filter.mp (L.max'_mem hLne)).2
  obtain ⟨s₁, hs₁, s₂, hs₂, hs₁₂⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  obtain ⟨v₁, hv₁, hv₁deg⟩ : ∃ v ∈ S, 3 ≤ (S.filter (G.Adj v)).card := by
    by_contra hcon
    push Not at hcon
    exact hs₁₂ (hlow s₁ hs₁ s₂ hs₂ (hcon s₁ hs₁) (hcon s₂ hs₂))
  obtain ⟨z₁, hz₁⟩ : (S.filter (G.Adj v₁)).Nonempty := Finset.card_pos.mp (by omega)
  rw [Finset.mem_filter] at hz₁
  have hn₀pos : 1 ≤ n₀ := by
    have := hmaxL v₁ z₁ (cons hz₁.2 nil) (by simp [G.ne_of_adj hz₁.2]) (by simp [hv₁, hz₁.1])
    simpa using this
  have claim : ∀ (a b : V) (P : G.Walk a b), P.IsPath → (∀ z ∈ P.support, z ∈ S) →
      P.length = n₀ → 3 ≤ (S.filter (G.Adj a)).card →
      ∃ (u : V) (C : G.Walk u u), C.IsCycle ∧ (∀ z ∈ C.support, z ∈ S) ∧
        ∃ z ∈ S, z ∉ C.support := by
    intro a b P hP hPS hPlen hadeg
    have hnb : ∀ z ∈ S, G.Adj a z → z ∈ P.support := by
      intro z hzS haz
      by_contra hzP
      have := hmaxL z b (cons haz.symm P) ((cons_isPath_iff _ _).mpr ⟨hP, hzP⟩) (by
        intro y hy
        rw [support_cons, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hzS
        · exact hPS y hy)
      rw [length_cons] at this
      omega
    cases P with
    | nil => simp at hPlen; omega
    | cons h P' =>
      rename_i a₁
      have hP' := (cons_isPath_iff _ _).mp hP
      have ha₁S : a₁ ∈ S := hPS a₁ (by simp)
      obtain ⟨w₁, hw₁, w₂, hw₂, hw₁₂⟩ := Finset.one_lt_card.mp (by
        rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨ha₁S, h⟩)]
        omega : 1 < ((S.filter (G.Adj a)).erase a₁).card)
      rw [Finset.mem_erase, Finset.mem_filter] at hw₁ hw₂
      have hmemP' : ∀ w, w ∈ S → G.Adj a w → w ∈ P'.support := by
        intro w hwS haw
        have := hnb w hwS haw
        rw [support_cons, List.mem_cons] at this
        exact this.resolve_left (G.ne_of_adj haw).symm
      have key : ∀ w w' : V, w ∈ S → G.Adj a w → w ≠ a₁ → w' ∈ S → G.Adj a w' →
          ∀ hw : w ∈ P'.support, w' ∉ (P'.takeUntil w hw).support →
          ∃ (u : V) (C : G.Walk u u), C.IsCycle ∧ (∀ z ∈ C.support, z ∈ S) ∧
            ∃ z ∈ S, z ∉ C.support := by
        intro w w' hwS haw hwa₁ hw'S haw' hw hw'
        refine ⟨a, cons h ((P'.takeUntil w hw).concat haw.symm), ?_, ?_, w', hw'S, ?_⟩
        · rw [cons_isCycle_iff, isPath_concat, edges_concat]
          refine ⟨⟨hP'.1.takeUntil hw,
            fun ha => hP'.2 (P'.support_takeUntil_subset_support hw ha)⟩, ?_⟩
          rw [List.concat_eq_append, List.mem_append, List.mem_singleton, not_or]
          refine ⟨fun he => hP'.2 (P'.support_takeUntil_subset_support hw
            (fst_mem_support_of_mem_edges _ he)), ?_⟩
          intro he
          rw [Sym2.eq_iff] at he
          rcases he with ⟨h1, -⟩ | ⟨-, h2⟩
          · exact (G.ne_of_adj haw) h1
          · exact hwa₁ h2.symm
        · intro z hz
          rw [support_cons, List.mem_cons, support_concat, List.mem_append,
            List.mem_singleton] at hz
          rcases hz with rfl | hz | rfl
          · exact hPS _ (by simp)
          · exact hPS z (by simp [P'.support_takeUntil_subset_support hw hz])
          · exact hPS _ (by simp)
        · rw [support_cons, List.mem_cons, support_concat, List.mem_append, List.mem_singleton]
          rintro (h' | h' | h')
          · exact G.ne_of_adj haw' h'.symm
          · exact hw' h'
          · exact G.ne_of_adj haw' h'.symm
      have hw₁P := hmemP' w₁ hw₁.2.1 hw₁.2.2
      have hw₂P := hmemP' w₂ hw₂.2.1 hw₂.2.2
      by_cases h₂ : w₂ ∈ (P'.takeUntil w₁ hw₁P).support
      · exact key w₂ w₁ hw₂.2.1 hw₂.2.2 hw₂.1 hw₁.2.1 hw₁.2.2 hw₂P
          (notMem_support_takeUntil_support_takeUntil_subset (Ne.symm hw₁₂) hw₁P h₂)
      · exact key w₁ w₂ hw₁.2.1 hw₁.2.2 hw₁.1 hw₂.2.1 hw₂.2.2 hw₁P h₂
  by_cases ha : 3 ≤ (S.filter (G.Adj a)).card
  · exact claim a b P hP hPS hPlen ha
  · have hb : 3 ≤ (S.filter (G.Adj b)).card := by
      by_contra hb
      have hab := hlow a (hPS a P.start_mem_support) b (hPS b P.end_mem_support)
        (by omega) (by omega)
      subst hab
      have := length_eq_zero_iff.mpr (isPath_iff_nil.mp hP)
      omega
    exact claim b a P.reverse hP.reverse (by simpa using hPS) (by simpa using hPlen) hb

/-- **A pendant piece.** Let `X ⊆ S` be a nonempty set off a cycle `C` in `S`, closed under
neighbours in `S` off `C`, and with neighbours in at most one vertex of `C`. Then the induction
hypothesis applies either to `X` together with its attachment vertex (if no vertex of `X` has fewer
than three neighbours in `S`) or to `S \ X`. -/
private theorem closeCycles_of_pendant [DecidableRel G.Adj] {S X : Finset V} {v : V}
    {C : G.Walk v v} (hC : C.IsCycle) (hCS : ∀ z ∈ C.support, z ∈ S)
    (hlow : ∀ u ∈ S, ∀ w ∈ S, (S.filter (G.Adj u)).card < 3 →
      (S.filter (G.Adj w)).card < 3 → u = w)
    (ih : ∀ T : Finset V, T.card < S.card → 2 ≤ T.card →
      (∀ u ∈ T, ∀ w ∈ T, (T.filter (G.Adj u)).card < 3 → (T.filter (G.Adj w)).card < 3 →
        u = w) → CloseCycles G)
    (hXne : X.Nonempty) (hXS : X ⊆ S) (hXC : ∀ z ∈ X, z ∉ C.support)
    (hXcl : ∀ z ∈ S, z ∉ X → z ∉ C.support → ∀ x ∈ X, ¬ G.Adj z x)
    (hXatt : ∀ c₁ ∈ C.support, ∀ c₂ ∈ C.support, (∃ x ∈ X, G.Adj c₁ x) →
      (∃ x ∈ X, G.Adj c₂ x) → c₁ = c₂) :
    CloseCycles G := by
  classical
  set N := S.filter (fun c => c ∈ C.support ∧ ∃ x ∈ X, G.Adj c x) with hN
  have hNsub : ∀ c₁ ∈ N, ∀ c₂ ∈ N, c₁ = c₂ := by
    intro c₁ h₁ c₂ h₂
    rw [hN, Finset.mem_filter] at h₁ h₂
    exact hXatt c₁ h₁.2.1 c₂ h₂.2.1 h₁.2.2 h₂.2.2
  have hNcard : N.card ≤ 1 := Finset.card_le_one.mpr hNsub
  set K := C.support.toFinset with hK
  have hKS : K ⊆ S := fun z hz => hCS z (List.mem_toFinset.mp hz)
  have hKX : ∀ z ∈ K, z ∉ X := fun z hz hzX => hXC z hzX (List.mem_toFinset.mp hz)
  have hK3 : 3 ≤ K.card := by
    have h1 : C.support.tail.toFinset ⊆ K := fun z hz =>
      List.mem_toFinset.mpr (List.mem_of_mem_tail (List.mem_toFinset.mp hz))
    have h2 := Finset.card_le_card h1
    rw [List.toFinset_card_of_nodup hC.support_nodup, List.length_tail, length_support] at h2
    have := hC.three_le_length
    omega
  have hXnb : ∀ x ∈ X, ∀ z ∈ S, G.Adj x z → z ∈ X ∨ z ∈ N := by
    intro x hx z hzS hxz
    by_cases hzX : z ∈ X
    · exact Or.inl hzX
    · by_cases hzC : z ∈ C.support
      · exact Or.inr (Finset.mem_filter.mpr ⟨hzS, hzC, x, hx, hxz.symm⟩)
      · exact absurd hxz.symm (hXcl z hzS hzX hzC x hx)
  by_cases hXlow : ∃ x ∈ X, (S.filter (G.Adj x)).card < 3
  · obtain ⟨x₀, hx₀X, hx₀low⟩ := hXlow
    apply ih (S \ X)
    · exact Finset.card_lt_card (Finset.sdiff_ssubset hXS hXne)
    · have : K ⊆ S \ X := fun z hz => Finset.mem_sdiff.mpr ⟨hKS hz, hKX z hz⟩
      have := Finset.card_le_card this
      omega
    · have key : ∀ y ∈ S \ X, ((S \ X).filter (G.Adj y)).card < 3 →
          y ∈ N ∨ (S.filter (G.Adj y)).card < 3 := by
        intro y hy hyl
        by_cases hyN : y ∈ N
        · exact Or.inl hyN
        · right
          rw [Finset.mem_sdiff] at hy
          have hnadj : ∀ x ∈ X, ¬ G.Adj y x := by
            intro x hx hyx
            by_cases hyC : y ∈ C.support
            · exact hyN (Finset.mem_filter.mpr ⟨hy.1, hyC, x, hx, hyx⟩)
            · exact hXcl y hy.1 hy.2 hyC x hx hyx
          have heq : (S \ X).filter (G.Adj y) = S.filter (G.Adj y) := by
            ext z
            simp only [Finset.mem_filter, Finset.mem_sdiff]
            constructor
            · rintro ⟨⟨hz, -⟩, h⟩
              exact ⟨hz, h⟩
            · rintro ⟨hz, h⟩
              exact ⟨⟨hz, fun hzX => hnadj z hzX h⟩, h⟩
          rwa [heq] at hyl
      intro u hu w hw hul hwl
      have hu' := Finset.mem_sdiff.mp hu
      have hw' := Finset.mem_sdiff.mp hw
      rcases key u hu hul with huN | hul' <;> rcases key w hw hwl with hwN | hwl'
      · exact hNsub u huN w hwN
      · exact absurd (hlow w hw'.1 x₀ (hXS hx₀X) hwl' hx₀low ▸ hx₀X) hw'.2
      · exact absurd (hlow u hu'.1 x₀ (hXS hx₀X) hul' hx₀low ▸ hx₀X) hu'.2
      · exact hlow u hu'.1 w hw'.1 hul' hwl'
  · push Not at hXlow
    have hsub : X ∪ N ⊆ S := Finset.union_subset hXS (Finset.filter_subset _ _)
    have hnbeq : ∀ x ∈ X, (X ∪ N).filter (G.Adj x) = S.filter (G.Adj x) := by
      intro x hx
      ext z
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hz, h⟩
        exact ⟨hsub hz, h⟩
      · rintro ⟨hz, h⟩
        exact ⟨Finset.mem_union.mpr (hXnb x hx z hz h), h⟩
    apply ih (X ∪ N)
    · have hdisj : Disjoint (X ∪ N) (K \ N) := by
        rw [Finset.disjoint_left]
        intro z hz hz'
        rw [Finset.mem_sdiff] at hz'
        rcases Finset.mem_union.mp hz with hz | hz
        · exact hKX z hz'.1 hz
        · exact hz'.2 hz
      have h1 := Finset.card_le_card
        (Finset.union_subset hsub ((Finset.sdiff_subset (s := K) (t := N)).trans hKS))
      rw [Finset.card_union_of_disjoint hdisj] at h1
      have h2 := Finset.le_card_sdiff N K
      omega
    · obtain ⟨x₀, hx₀⟩ := hXne
      have := Finset.card_le_card (Finset.filter_subset (G.Adj x₀) (X ∪ N))
      rw [hnbeq x₀ hx₀] at this
      have := hXlow x₀ hx₀
      omega
    · intro u hu w hw hul hwl
      have hmem : ∀ y ∈ X ∪ N, ((X ∪ N).filter (G.Adj y)).card < 3 → y ∈ N := by
        intro y hy hyl
        rcases Finset.mem_union.mp hy with hy | hy
        · rw [hnbeq y hy] at hyl
          exact absurd (hXlow y hy) (by omega)
        · exact hy
      exact hNsub u (hmem u hu hul) w (hmem w hw hwl)

/-- **Bondy–Vince for at most one vertex of low degree.** If a finite set `S` has at least two
vertices and at most one of them has fewer than three neighbours in `S`, then `G` has two cycle
lengths that differ by one or two. The proof is by strong induction on `|S|`. -/
private theorem closeCycles_of_card [DecidableRel G.Adj] (n : ℕ) :
    ∀ S : Finset V, S.card = n → 2 ≤ S.card →
      (∀ u ∈ S, ∀ w ∈ S, (S.filter (G.Adj u)).card < 3 → (S.filter (G.Adj w)).card < 3 →
        u = w) → CloseCycles G := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hSn hS hlow
  have ih' : ∀ T : Finset V, T.card < S.card → 2 ≤ T.card →
      (∀ u ∈ T, ∀ w ∈ T, (T.filter (G.Adj u)).card < 3 → (T.filter (G.Adj w)).card < 3 →
        u = w) → CloseCycles G :=
    fun T hT => ih T.card (hSn ▸ hT) T rfl
  obtain ⟨u₀, C₀, hC₀, hC₀S, z₀, hz₀S, hz₀C⟩ := exists_cycle_avoiding hS hlow
  let good : Finset V → Prop := fun D => D.Nonempty ∧ Conn G D ∧ ∃ (u : V) (C : G.Walk u u),
    C.IsCycle ∧ (∀ z ∈ C.support, z ∈ S) ∧ ∀ z ∈ D, z ∉ C.support
  have hne : (S.powerset.filter good).Nonempty :=
    ⟨{z₀}, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hz₀S),
      Finset.singleton_nonempty _, conn_singleton z₀, u₀, C₀, hC₀, hC₀S, by simpa using hz₀C⟩⟩
  obtain ⟨D, hDmem, hDmax⟩ := Finset.exists_max_image (S.powerset.filter good) Finset.card hne
  rw [Finset.mem_filter, Finset.mem_powerset] at hDmem
  obtain ⟨hDS, hDne, hDconn, v, C, hC, hCS, hDC⟩ := hDmem
  have hmax : ∀ D' : Finset V, D' ⊆ S → Conn G D' → ∀ (u : V) (C' : G.Walk u u), C'.IsCycle →
      (∀ z ∈ C'.support, z ∈ S) → (∀ z ∈ D', z ∉ C'.support) → D'.card ≤ D.card := by
    intro D' hD'S hD'conn u C' hC' hC'S hD'C
    rcases D'.eq_empty_or_nonempty with rfl | hD'ne
    · simp
    · exact hDmax D' (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hD'S, hD'ne, hD'conn, u, C',
        hC', hC'S, hD'C⟩)
  have hclos : ∀ z ∈ S, z ∉ D → z ∉ C.support → ∀ x ∈ D, ¬ G.Adj z x := by
    intro z hzS hzD hzC x hx hzx
    have := hmax (insert z D) (Finset.insert_subset hzS hDS) (conn_insert hDconn hx hzx) v C hC
      hCS (by
        intro y hy
        rw [Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · exact hzC
        · exact hDC y hy)
    rw [Finset.card_insert_of_notMem hzD] at this
    omega
  by_cases hA : ∃ a₁ ∈ C.support, ∃ a₂ ∈ C.support, a₁ ≠ a₂ ∧ (∃ x ∈ D, G.Adj a₁ x) ∧
      (∃ x ∈ D, G.Adj a₂ x)
  swap
  · refine closeCycles_of_pendant hC hCS hlow ih' hDne hDS hDC hclos ?_
    intro c₁ h₁ c₂ h₂ e₁ e₂
    by_contra hne
    exact hA ⟨c₁, h₁, c₂, h₂, hne, e₁, e₂⟩
  obtain ⟨a₁, ha₁, a₂, ha₂, ha₁₂, ⟨x₁, hx₁, hax₁⟩, ⟨x₂, hx₂, hax₂⟩⟩ := hA
  have hpick : ∀ c c' : V, (¬ ∃ x ∈ D, G.Adj c x) →
      ∃ a ∈ C.support, a ≠ c ∧ a ≠ c' ∧ ∃ x ∈ D, G.Adj a x := by
    intro c c' hc
    by_cases h : a₁ = c'
    · refine ⟨a₂, ha₂, ?_, ?_, x₂, hx₂, hax₂⟩
      · rintro rfl
        exact hc ⟨x₂, hx₂, hax₂⟩
      · rintro rfl
        exact ha₁₂ h
    · refine ⟨a₁, ha₁, ?_, h, x₁, hx₁, hax₁⟩
      rintro rfl
      exact hc ⟨x₁, hx₁, hax₁⟩
  by_cases hbad : ∃ c ∈ C.support, (¬ ∃ x ∈ D, G.Adj c x) ∧ 3 ≤ (S.filter (G.Adj c)).card
  · obtain ⟨c, hc, hcA, hc3⟩ := hbad
    obtain ⟨w, hwS, hcw, hwC⟩ : ∃ w ∈ S, G.Adj c w ∧ s(c, w) ∉ C.edges := by
      by_contra hcon
      push Not at hcon
      have hsub : ((S.filter (G.Adj c) : Finset V) : Set V) ⊆ C.toSubgraph.neighborSet c := by
        intro z hz
        rw [Finset.coe_filter, Set.mem_ofPred_eq] at hz
        exact adj_toSubgraph_iff_mem_edges.mpr (hcon z hz.1 hz.2)
      have h2 := hC.ncard_neighborSet_toSubgraph_eq_two hc
      have hfin : (C.toSubgraph.neighborSet c).Finite := Set.finite_of_ncard_pos (by omega)
      have := Set.ncard_le_ncard hsub hfin
      rw [Set.ncard_coe_finset, h2] at this
      omega
    have hcD : c ∉ D := fun h => hDC c h hc
    by_cases hwsupp : w ∈ C.support
    · exfalso
      obtain ⟨a, ha, hac, haw, x, hx, hax⟩ := hpick c w hcA
      refine reroute hC hCS hDS hDconn hDC hmax hc hwsupp (G.ne_of_adj hcw) (Q := cons hcw nil)
        ?_ ?_ ?_ ?_ ?_ ha hac haw hx hax
      · simp [G.ne_of_adj hcw]
      · intro z hz
        simp only [support_cons, support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact hCS _ hc
        · exact hwS
      · intro z hz _
        simp only [support_cons, support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
        exact hz
      · intro z hz hzD
        simp only [support_cons, support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact hcD hzD
        · exact hDC _ hzD hwsupp
      · intro e he
        simp only [edges_cons, edges_nil, List.mem_cons, List.not_mem_nil, or_false] at he
        subst he
        exact hwC
    · let X := S.filter (fun z => ∃ p : G.Walk w z, ∀ y ∈ p.support, y ∈ S ∧ y ∉ C.support)
      have hwX : w ∈ X := Finset.mem_filter.mpr ⟨hwS, nil, by simp [hwS, hwsupp]⟩
      have hXS : X ⊆ S := Finset.filter_subset _ _
      have hXC : ∀ z ∈ X, z ∉ C.support := by
        intro z hz
        obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hz).2
        exact (hp z p.end_mem_support).2
      have hXcl : ∀ z ∈ S, z ∉ X → z ∉ C.support → ∀ x ∈ X, ¬ G.Adj z x := by
        intro z hzS hzX hzC x hx hzx
        apply hzX
        obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hx).2
        refine Finset.mem_filter.mpr ⟨hzS, p.concat hzx.symm, ?_⟩
        intro y hy
        rw [support_concat, List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | rfl
        · exact hp y hy
        · exact ⟨hzS, hzC⟩
      have hwD : w ∉ D := fun h => hcA ⟨w, h, hcw⟩
      by_cases hXatt : ∃ c' ∈ C.support, c' ≠ c ∧ ∃ x ∈ X, G.Adj c' x
      · exfalso
        obtain ⟨c', hc', hc'c, x', hx'X, hc'x'⟩ := hXatt
        obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hx'X).2
        have hpD : ∀ z ∈ p.support, z ∉ D := walk_avoid hclos p hp hwD
        have hqS : ∀ z ∈ p.bypass.support, z ∈ S ∧ z ∉ C.support :=
          fun z hz => hp z (p.support_bypass_subset_support hz)
        have hqD : ∀ z ∈ p.bypass.support, z ∉ D :=
          fun z hz => hpD z (p.support_bypass_subset_support hz)
        obtain ⟨a, ha, hac, hac', x, hx, hax⟩ := hpick c c' hcA
        refine reroute hC hCS hDS hDconn hDC hmax hc hc' hc'c.symm
          (Q := cons hcw (p.bypass.concat hc'x'.symm)) ?_ ?_ ?_ ?_ ?_ ha hac hac' hx hax
        · rw [cons_isPath_iff, isPath_concat, support_concat, List.mem_append, List.mem_singleton]
          refine ⟨⟨p.bypass_isPath, fun h => (hqS _ h).2 hc'⟩, ?_⟩
          rintro (h | h)
          · exact (hqS _ h).2 hc
          · exact hc'c h.symm
        · intro z hz
          rw [support_cons, List.mem_cons, support_concat, List.mem_append,
            List.mem_singleton] at hz
          rcases hz with rfl | hz | rfl
          · exact hCS _ hc
          · exact (hqS z hz).1
          · exact hCS _ hc'
        · intro z hz hzC
          rw [support_cons, List.mem_cons, support_concat, List.mem_append,
            List.mem_singleton] at hz
          rcases hz with rfl | hz | rfl
          · exact Or.inl rfl
          · exact absurd hzC (hqS z hz).2
          · exact Or.inr rfl
        · intro z hz
          rw [support_cons, List.mem_cons, support_concat, List.mem_append,
            List.mem_singleton] at hz
          rcases hz with rfl | hz | rfl
          · exact hcD
          · exact hqD z hz
          · exact fun h => hDC _ h hc'
        · intro e he hCe
          rw [edges_cons, List.mem_cons, edges_concat, List.concat_eq_append, List.mem_append,
            List.mem_singleton] at he
          rcases he with rfl | he | rfl
          · exact hwsupp (snd_mem_support_of_mem_edges _ hCe)
          · induction e using Sym2.ind with
            | h y₁ y₂ =>
              exact (hqS _ (p.bypass.fst_mem_support_of_mem_edges he)).2
                (fst_mem_support_of_mem_edges _ hCe)
          · exact (hXC x' hx'X) (fst_mem_support_of_mem_edges _ hCe)
      · refine closeCycles_of_pendant hC hCS hlow ih' ⟨w, hwX⟩ hXS hXC hXcl ?_
        intro c₁ h₁ c₂ h₂ ⟨y₁, hy₁, e₁⟩ ⟨y₂, hy₂, e₂⟩
        have h₁c : c₁ = c := by
          by_contra hne
          exact hXatt ⟨c₁, h₁, hne, y₁, hy₁, e₁⟩
        have h₂c : c₂ = c := by
          by_contra hne
          exact hXatt ⟨c₂, h₂, hne, y₂, hy₂, e₂⟩
        rw [h₁c, h₂c]
  · have hbad' : ∀ c ∈ C.support, (¬ ∃ x ∈ D, G.Adj c x) → (S.filter (G.Adj c)).card < 3 := by
      intro c hc hcA
      by_contra h
      exact hbad ⟨c, hc, hcA, by omega⟩
    obtain ⟨b, hb, hbatt⟩ : ∃ b ∈ C.support, ∀ z ∈ C.support, z ≠ b → ∃ x ∈ D, G.Adj z x := by
      by_cases hex : ∃ b ∈ C.support, ¬ ∃ x ∈ D, G.Adj b x
      · obtain ⟨b, hb, hbA⟩ := hex
        refine ⟨b, hb, fun z hz hzb => ?_⟩
        by_contra hzA
        exact hzb (hlow z (hCS z hz) b (hCS b hb) (hbad' z hz hzA) (hbad' b hb hbA))
      · refine ⟨v, C.start_mem_support, fun z hz _ => ?_⟩
        by_contra hzA
        exact hex ⟨z, hz, hzA⟩
    exact closeCycles_of_attach hDconn (C.rotate b hb) (hC.rotate hb)
      (fun z hz hzC => hDC z hz ((mem_support_rotate_iff _ _ _).mp hzC))
      (fun z hz hzb => hbatt z ((mem_support_rotate_iff _ _ _).mp hz) hzb)

/-- A finite set of vertices that is not `3`-colourable contains a nonempty set in which every
vertex has at least three neighbours. -/
private theorem exists_subset_three_le [DecidableRel G.Adj] (n : ℕ) :
    ∀ s : Finset V, s.card = n →
      (¬ ∃ f : V → Fin 3, ∀ u ∈ s, ∀ w ∈ s, G.Adj u w → f u ≠ f w) →
      ∃ S ⊆ s, S.Nonempty ∧ ∀ v ∈ S, 3 ≤ (S.filter (G.Adj v)).card := by
  classical
  induction n with
  | zero =>
    intro s hs hcol
    exfalso
    apply hcol
    refine ⟨fun _ => 0, fun u hu => ?_⟩
    rw [Finset.card_eq_zero] at hs
    simp [hs] at hu
  | succ n ih =>
    intro s hs hcol
    by_cases hall : ∀ v ∈ s, 3 ≤ (s.filter (G.Adj v)).card
    · exact ⟨s, subset_rfl, Finset.card_pos.mp (by omega), hall⟩
    · push Not at hall
      obtain ⟨v, hv, hvlow⟩ := hall
      have hcol' : ¬ ∃ f : V → Fin 3, ∀ u ∈ s.erase v, ∀ w ∈ s.erase v, G.Adj u w → f u ≠ f w := by
        rintro ⟨f, hf⟩
        apply hcol
        obtain ⟨col, hcolv⟩ : ∃ col : Fin 3, col ∉ (s.filter (G.Adj v)).image f := by
          by_contra hcon
          push Not at hcon
          have h1 := Finset.card_le_card (fun c (_ : c ∈ (Finset.univ : Finset (Fin 3))) => hcon c)
          have h2 := Finset.card_image_le (s := s.filter (G.Adj v)) (f := f)
          simp only [Finset.card_univ, Fintype.card_fin] at h1
          omega
        refine ⟨Function.update f v col, fun u hu w hw huw => ?_⟩
        by_cases huv : u = v
        · subst huv
          have hwv : w ≠ u := (G.ne_of_adj huw).symm
          rw [Function.update_self, Function.update_of_ne hwv]
          intro h
          exact hcolv (h ▸ Finset.mem_image_of_mem f (Finset.mem_filter.mpr ⟨hw, huw⟩))
        · by_cases hwv : w = v
          · subst hwv
            rw [Function.update_self, Function.update_of_ne huv]
            intro h
            exact hcolv (h ▸ Finset.mem_image_of_mem f (Finset.mem_filter.mpr ⟨hu, huw.symm⟩))
          · rw [Function.update_of_ne huv, Function.update_of_ne hwv]
            exact hf u (Finset.mem_erase.mpr ⟨huv, hu⟩) w (Finset.mem_erase.mpr ⟨hwv, hw⟩) huw
      obtain ⟨S, hS, hSne, hSdeg⟩ :=
        ih (s.erase v) (by rw [Finset.card_erase_of_mem hv]; omega) hcol'
      exact ⟨S, hS.trans (Finset.erase_subset _ _), hSne, hSdeg⟩

/-- If every vertex of a nonempty finite set `S` has at least three neighbours in `S`, then `G` has
two cycle lengths that differ by one or two. -/
private theorem closeCycles_of_finset [DecidableRel G.Adj] (S : Finset V)
    (hS : S.Nonempty) (hdeg : ∀ v ∈ S, 3 ≤ (S.filter (G.Adj v)).card) : CloseCycles G := by
  refine closeCycles_of_card S.card S rfl ?_ (fun u hu _ _ hul _ => absurd (hdeg u hu) (by omega))
  obtain ⟨v, hv⟩ := hS
  have := Finset.card_le_card (Finset.filter_subset (G.Adj v) S)
  have := hdeg v hv
  omega

/-- **Bondy–Vince theorem, minimum degree three.** Every finite simple graph of minimum degree at
least three has two cycle lengths `m < m'` with `m' ≤ m + 2`, that is, two cycles whose lengths
differ by one or two. -/
theorem exists_cycleLengths_lt_le_add_two_of_three_le_minDegree [Fintype V] [DecidableRel G.Adj]
    (h : 3 ≤ G.minDegree) :
    ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2 := by
  classical
  have hne : (Finset.univ : Finset V).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    by_contra hV
    rw [not_nonempty_iff] at hV
    rw [minDegree_of_subsingleton] at h
    omega
  refine closeCycles_of_finset Finset.univ hne fun v _ => ?_
  rw [← neighborFinset_eq_filter, card_neighborFinset_eq_degree]
  exact h.trans (G.minDegree_le_degree v)

/-- **Bondy–Vince theorem, graphs that are not 3-colourable.**
Every simple graph, on any vertex type, that is not `3`-colourable has two cycle lengths
`m < m'` with `m' ≤ m + 2`, that is, two cycles whose lengths differ by one or two. In particular
this holds for every graph of chromatic number `4`. -/
theorem exists_cycleLengths_lt_le_add_two_of_not_colorable (h : ¬ G.Colorable 3) :
    ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2 := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Finset V,
      ¬ ∃ f : V → Fin 3, ∀ u ∈ s, ∀ w ∈ s, G.Adj u w → f u ≠ f w := by
    by_contra hcon
    push Not at hcon
    apply h
    choose g hg using hcon
    obtain ⟨χ, hχ⟩ := Finset.rado_selection (β := fun _ => Fin 3) g
    refine ⟨Coloring.mk χ fun {u w} huw => ?_⟩
    obtain ⟨t, hst, ht⟩ := hχ {u, w}
    rw [ht u (by simp), ht w (by simp)]
    exact hg t u (hst (by simp)) w (hst (by simp)) huw
  obtain ⟨S, -, hSne, hdeg⟩ := exists_subset_three_le s.card s rfl hs
  exact closeCycles_of_finset S hSne hdeg

/--
**Erdős Problem 751 is false.** It is not the case that both of the following hold:
(i) for every natural number $k$ there is a simple graph $G$ with chromatic number $4$ in
which any two distinct cycle lengths of $G$ differ by at least $k$; (ii) for all natural numbers
$k$ and $g$ there is a simple graph $G$ with chromatic number $4$ and girth at least $g$ in which
any two distinct cycle lengths of $G$ differ by at least $k$.

Source:
J. A. Bondy and A. Vince, Cycles in a graph whose lengths differ by one or two, Journal of Graph
Theory 27 (1998), 11-15,
https://doi.org/10.1002/(SICI)1097-0118(199801)27:1%3C11::AID-JGT3%3E3.0.CO;2-J; Jun Gao, Qingyi
Huo, Chun-Hung Liu, and Jie Ma, A unified proof of conjectures on cycle lengths in graphs,
arXiv:1904.08126v3, https://arxiv.org/abs/1904.08126v3. Moved from
`OpenConjectures/Combinatorics/ErdosProblem751`.
-/
theorem conjecture_refuted : ¬ conjecture := by
  rintro ⟨h, -⟩
  obtain ⟨V, G, hχ, hgap⟩ := h 3
  have hcol : ¬ G.Colorable 3 := by
    intro hc
    have := hc.chromaticNumber_le
    rw [hχ] at this
    norm_cast at this
  obtain ⟨m, hm, m', hm', hlt, hle⟩ := exists_cycleLengths_lt_le_add_two_of_not_colorable hcol
  have := hgap m hm m' hm' hlt
  omega

end MathlibExt.Combinatorics.ErdosProblem751Wanted
