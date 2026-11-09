/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring.Basic
public import MathlibExt.Combinatorics.SimpleGraph.ListColoring

@[expose] public section

/-!
# The partial list colouring ratio conjecture is false

Formal proof of `conjecture_refuted`, following Noel, *The Partial List Colouring Conjecture is
False* (arXiv:2609.23291), Theorem 1.1. The namespace `Noel` contains the 14-vertex graph `G`, the
2-list assignment `L`, the bound that no partial `L`-colouring has more than nine vertices, and
the proof that `G` is 3-choosable.
-/

namespace MathlibExt.GraphTheory.PartialListColoringWanted

/-! Source record `OPG-788`. Iradmusa's partial list coloring monotonicity conjecture
from the Open Problem Garden (posted May 12th, 2008): the ratio `λ_t / t` is
nonincreasing in `t` up to the list chromatic number. -/

/-- A proper coloring of the vertex subset `S` respecting the list assignment `L`:
every vertex of `S` gets a color from its own list, and adjacent vertices get distinct colors. -/
def IsListColoring {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (L : V → Finset ℕ) (f : V → ℕ) (S : Finset V) : Prop :=
  (∀ v ∈ S, f v ∈ L v) ∧ ∀ v ∈ S, ∀ w ∈ S, G.Adj v w → f v ≠ f w

/-- `lambdaMax G L` is `λ_L`: the maximum number of vertices of `G` colorable
with respect to the list assignment `L` (the largest `k` for which some
`k`-element subset admits a proper list coloring). -/
noncomputable def lambdaMax {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (L : V → Finset ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset V, ∃ f : V → ℕ, S.card = k ∧ IsListColoring G L f S}

/-- `lambdaMin G t` is `λ_t`: the minimum of `λ_L` over all list assignments
`L` with every list of size `t`. -/
noncomputable def lambdaMin {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (t : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ L : V → Finset ℕ, (∀ v, (L v).card = t) ∧ lambdaMax G L = k}

/-- Iradmusa's conjecture: for a graph with choice number `χ_ℓ` (via the
shared `SimpleGraph.IsChoiceNumber` predicate) and `1 ≤ r ≤ s ≤ χ_ℓ`, one
has `λ_r / r ≥ λ_s / s`. -/
def conjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (χ_ℓ r s : ℕ),
    G.IsChoiceNumber χ_ℓ →
    1 ≤ r → r ≤ s → s ≤ χ_ℓ →
    (lambdaMin G r : ℚ) / (r : ℚ) ≥ (lambdaMin G s : ℚ) / (s : ℚ)

namespace Noel

/-- The 14 vertices of the paper's graph: the two terminals and the three vertices of each of
the four triangles.  Paper triangle `T_{i+1}` is `T i`; its private vertex is `p i` and its
non-private vertices are `u i` and `v i`. -/
inductive V : Type
  | s1 : V
  | s2 : V
  | u : Fin 4 → V
  | v : Fin 4 → V
  | p : Fin 4 → V
  deriving DecidableEq, Fintype, Repr

/-- The adjacency relation of the paper's graph `G`, as a Boolean function.

* `s_1` and `s_2` are non-adjacent;
* both `s_1` and `s_2` are adjacent to `u i` and `v i` for every `i`;
* the private vertices `p i` are adjacent to no terminal;
* each `{u i, v i, p i}` is a triangle;
* there are no other edges. -/
def adjB : V → V → Bool
  | .s1, .s1 => false
  | .s1, .s2 => false
  | .s1, .u _ => true
  | .s1, .v _ => true
  | .s1, .p _ => false
  | .s2, .s1 => false
  | .s2, .s2 => false
  | .s2, .u _ => true
  | .s2, .v _ => true
  | .s2, .p _ => false
  | .u _, .s1 => true
  | .u _, .s2 => true
  | .u _, .u _ => false
  | .u i, .v j => decide (i = j)
  | .u i, .p j => decide (i = j)
  | .v _, .s1 => true
  | .v _, .s2 => true
  | .v i, .u j => decide (i = j)
  | .v _, .v _ => false
  | .v i, .p j => decide (i = j)
  | .p _, .s1 => false
  | .p _, .s2 => false
  | .p i, .u j => decide (i = j)
  | .p i, .v j => decide (i = j)
  | .p _, .p _ => false

/-- Adjacency of the paper's graph. -/
def AdjRel (a b : V) : Prop := adjB a b = true

instance : DecidableRel AdjRel := fun a b => by unfold AdjRel; infer_instance

/-- The paper's graph `G`. -/
def G : SimpleGraph V where
  Adj := AdjRel
  symm := ⟨by
    intro a b h
    cases a <;> cases b <;> simp_all [AdjRel, adjB]⟩
  loopless := ⟨by
    intro a
    cases a <;> simp [AdjRel, adjB]⟩

/-- Characterisation of adjacency in `G`. -/
@[simp] theorem G_adj {a b : V} : G.Adj a b ↔ adjB a b = true := Iff.rfl

/-- Computable decidability of adjacency in `G` (needed for concrete `decide` checks). -/
instance : DecidableRel G.Adj := fun a b => inferInstanceAs (Decidable (adjB a b = true))

/-- The triangle `T_i` of the paper (paper `T_{i+1}`). -/
def T (i : Fin 4) : Finset V := {V.u i, V.v i, V.p i}

/-- The two terminals. -/
def terminals : Finset V := {V.s1, V.s2}

/-- The union of the four triangles. -/
def allTriangles : Finset V := (Finset.univ : Finset (Fin 4)).biUnion T

/-- The common list of the vertices of `T_i`.  In the paper's colours these are
`T_1 ↦ {1,3}`, `T_2 ↦ {1,4}`, `T_3 ↦ {2,3}`, `T_4 ↦ {2,4}`; with the encoding
`1,2,3,4 ↦ 0,1,2,3` this is `{0,2}, {0,3}, {1,2}, {1,3}`. -/
def listOf : Fin 4 → Finset ℕ
  | ⟨0, _⟩ => {0, 2}
  | ⟨1, _⟩ => {0, 3}
  | ⟨2, _⟩ => {1, 2}
  | _ => {1, 3}

/-- The paper's 2-list assignment `L`: `L(s_1) = {1,2}`, `L(s_2) = {3,4}` and every vertex of
`T_i` has the common list `listOf i`.  (Paper colours are encoded as `0,1,2,3`.) -/
def L : V → Finset ℕ
  | .s1 => {0, 1}
  | .s2 => {2, 3}
  | .u i => listOf i
  | .v i => listOf i
  | .p i => listOf i

section Colouring

variable {W : Type*}

/-- A partial proper list-colouring: `S` is the set of coloured vertices and `c v` is the
colour of `v`.  Every coloured vertex receives a colour from its own list, and adjacent
coloured vertices receive different colours. -/
def IsPartialListColoring (G : SimpleGraph W) (L : W → Finset ℕ) (S : Finset W)
    (c : W → ℕ) : Prop :=
  (∀ v ∈ S, c v ∈ L v) ∧ ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v

/-- A full proper list-colouring of `G` from the lists `L`. -/
def IsListColoring (G : SimpleGraph W) (L : W → Finset ℕ) (c : W → ℕ) : Prop :=
  (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v

/-- `G` can be properly coloured from the lists `L`. -/
def ListColorable (G : SimpleGraph W) (L : W → Finset ℕ) : Prop :=
  ∃ c : W → ℕ, IsListColoring G L c

/-- `L` is a `k`-list assignment: every vertex has a list of exactly `k` colours. -/
def IsListAssignment (L : W → Finset ℕ) (k : ℕ) : Prop :=
  ∀ v, (L v).card = k

/-- `G` is `k`-choosable: from every `k`-list assignment `G` admits a proper list-colouring. -/
def Choosable (G : SimpleGraph W) (k : ℕ) : Prop :=
  ∀ L : W → Finset ℕ, IsListAssignment L k → ListColorable G L

/-- The list chromatic number of `G` is exactly `k`: `G` is `k`-choosable and, for every
`j < k`, is not `j`-choosable.  (This is the standard "least `k` such that `G` is
`k`-choosable" definition.) -/
def ListChromaticNumberEq (G : SimpleGraph W) (k : ℕ) : Prop :=
  Choosable G k ∧ ∀ j, j < k → ¬ Choosable G j

end Colouring

/-- The paper's Theorem 1 (`th:main`) for the explicit 14-vertex graph `G` and the explicit
2-list assignment `L` of the paper:

* `G` has 14 vertices;
* the list chromatic number of `G` is exactly 3;
* `L` is a 2-list assignment of `G`;
* every partial proper `L`-colouring of `G` colours at most 9 vertices
  (i.e. at most 9 vertices of `G` can be properly coloured from `L`). -/
def counterexample_statement : Prop :=
  Fintype.card V = 14 ∧
  ListChromaticNumberEq G 3 ∧
  IsListAssignment L 2 ∧
  ∀ (S : Finset V) (c : V → ℕ), IsPartialListColoring G L S c → S.card ≤ 9

/-- The explicit partial colouring of `9` vertices (so the bound `9` is attained and the
statement "at most 9 vertices" is not vacuous).  Triangles are `T 0 = {2,3,4}`,
`T 1 = {5,6,7}`, `T 2 = {8,9,10}`, `T 3 = {11,12,13}`; the coloured vertices are
`s1, s2, p0, u1, p1, u2, p2, u3, v3`. -/
def S9 : Finset V := {V.s1, V.s2, V.p 0, V.u 1, V.p 1, V.u 2, V.p 2, V.u 3, V.v 3}

/-- The colours of the nine vertices above (paper colours: `s1 ↦ 1`, `s2 ↦ 3`, `p0 ↦ 1`,
`u1 ↦ 4`, `p1 ↦ 1`, `u2 ↦ 2`, `p2 ↦ 3`, `u3 ↦ 2`, `v3 ↦ 4`). -/
def c9 : V → ℕ
  | .s1 => 0
  | .s2 => 2
  | .p 0 => 0
  | .u 1 => 3
  | .p 1 => 0
  | .u 2 => 1
  | .p 2 => 2
  | .u 3 => 1
  | .v 3 => 3
  | _ => 0

section

open Finset

lemma card_sdiff_singleton_ge (s : Finset ℕ) (x : ℕ) : s.card - 1 ≤ (s \ {x}).card := by
  rw [Finset.card_sdiff]
  have h : (({x} : Finset ℕ) ∩ s).card ≤ 1 := by
    calc (({x} : Finset ℕ) ∩ s).card ≤ ({x} : Finset ℕ).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = 1 := by simp
  omega

lemma card_sdiff_pair_ge (s : Finset ℕ) (x y : ℕ) (h : ¬ (x ∈ s ∧ y ∈ s)) :
    s.card - 1 ≤ (s \ {x, y}).card := by
  rw [Finset.card_sdiff]
  have h1 : (({x, y} : Finset ℕ) ∩ s).card ≤ 1 := by
    by_contra hle
    have h2 : 2 ≤ (({x, y} : Finset ℕ) ∩ s).card := by omega
    by_cases hxy : x = y
    · subst hxy
      have hc : (({x, x} : Finset ℕ) ∩ s).card ≤ 1 := by
        calc (({x, x} : Finset ℕ) ∩ s).card ≤ ({x, x} : Finset ℕ).card :=
              Finset.card_le_card Finset.inter_subset_left
          _ = 1 := by simp
      omega
    · have hcard : ({x, y} : Finset ℕ).card = 2 := by simp [hxy]
      have heq : ({x, y} : Finset ℕ) ∩ s = {x, y} :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
      have hx : x ∈ s := by
        have hx' : x ∈ ({x, y} : Finset ℕ) ∩ s := by rw [heq]; simp
        exact Finset.mem_of_mem_inter_right hx'
      have hy : y ∈ s := by
        have hy' : y ∈ ({x, y} : Finset ℕ) ∩ s := by rw [heq]; simp
        exact Finset.mem_of_mem_inter_right hy'
      exact h ⟨hx, hy⟩
  omega

lemma mul_le_two_of_add_le_three {a b : ℕ} (h : a + b ≤ 3) : a * b ≤ 2 := by
  have ha : a ≤ 3 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;> omega

/-- Three lists of sizes at least 1, 2, 3 admit pairwise distinct representatives. -/
lemma exists_pairwise_distinct {A B C : Finset ℕ} (hA : 1 ≤ A.card) (hB : 2 ≤ B.card)
    (hC : 3 ≤ C.card) :
    ∃ x ∈ A, ∃ y ∈ B, ∃ z ∈ C, x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
  have hBpos : 0 < (B \ {x}).card := by
    have h := card_sdiff_singleton_ge B x
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hBpos
  have hyB : y ∈ B := (Finset.mem_sdiff.mp hy).1
  have hyx : y ≠ x := by simpa using (Finset.mem_sdiff.mp hy).2
  have hCpos : 0 < ((C \ {x}) \ {y}).card := by
    have h1 := card_sdiff_singleton_ge C x
    have h2 := card_sdiff_singleton_ge (C \ {x}) y
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hCpos
  have hzCx : z ∈ C \ {x} := (Finset.mem_sdiff.mp hz).1
  have hzy : z ≠ y := by simpa using (Finset.mem_sdiff.mp hz).2
  have hzC : z ∈ C := (Finset.mem_sdiff.mp hzCx).1
  have hzx : z ≠ x := by simpa using (Finset.mem_sdiff.mp hzCx).2
  exact ⟨x, hx, y, hyB, z, hzC, hyx.symm, hzx.symm, hzy.symm⟩

lemma listOf_card (i : Fin 4) : (listOf i).card = 2 := by
  fin_cases i <;> decide

lemma L_two (v : V) : (L v).card = 2 := by
  cases v with
  | s1 => simp [L]
  | s2 => simp [L]
  | u i => exact listOf_card i
  | v i => exact listOf_card i
  | p i => exact listOf_card i

lemma adj_u_v (i : Fin 4) : G.Adj (V.u i) (V.v i) := by simp [G_adj, adjB]

lemma adj_u_p (i : Fin 4) : G.Adj (V.u i) (V.p i) := by simp [G_adj, adjB]

lemma adj_v_p (i : Fin 4) : G.Adj (V.v i) (V.p i) := by simp [G_adj, adjB]

lemma adj_s1_u (i : Fin 4) : G.Adj V.s1 (V.u i) := by simp [G_adj, adjB]

lemma adj_s1_v (i : Fin 4) : G.Adj V.s1 (V.v i) := by simp [G_adj, adjB]

lemma adj_s2_u (i : Fin 4) : G.Adj V.s2 (V.u i) := by simp [G_adj, adjB]

lemma adj_s2_v (i : Fin 4) : G.Adj V.s2 (V.v i) := by simp [G_adj, adjB]

/-- A triangle with a common list of size 2 contributes at most two coloured vertices. -/
lemma triangle_card_le_two (S : Finset V) (c : V → ℕ)
    (h : IsPartialListColoring G L S c) (i : Fin 4) : (S ∩ T i).card ≤ 2 := by
  by_contra hle
  have hge : 3 ≤ (S ∩ T i).card := by omega
  have hcardT : (T i).card = 3 := by simp [T]
  have heq : S ∩ T i = T i :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  have hu : V.u i ∈ S := by
    have h' : V.u i ∈ S ∩ T i := by rw [heq]; simp [T]
    exact Finset.mem_of_mem_inter_left h'
  have hv : V.v i ∈ S := by
    have h' : V.v i ∈ S ∩ T i := by rw [heq]; simp [T]
    exact Finset.mem_of_mem_inter_left h'
  have hp : V.p i ∈ S := by
    have h' : V.p i ∈ S ∩ T i := by rw [heq]; simp [T]
    exact Finset.mem_of_mem_inter_left h'
  have hmu : c (V.u i) ∈ L (V.u i) := h.1 _ hu
  have hmv : c (V.v i) ∈ L (V.v i) := h.1 _ hv
  have hmp : c (V.p i) ∈ L (V.p i) := h.1 _ hp
  have hLuv : L (V.u i) = L (V.v i) := rfl
  have hLvp : L (V.v i) = L (V.p i) := rfl
  have hd1 : c (V.u i) ≠ c (V.v i) := h.2 _ hu _ hv (adj_u_v i)
  have hd2 : c (V.u i) ≠ c (V.p i) := h.2 _ hu _ hp (adj_u_p i)
  have hd3 : c (V.v i) ≠ c (V.p i) := h.2 _ hv _ hp (adj_v_p i)
  have hset : ({c (V.u i), c (V.v i), c (V.p i)} : Finset ℕ) ⊆ L (V.u i) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hmu
    · rw [hLuv]; exact hmv
    · rw [hLuv, hLvp]; exact hmp
  have hc3 : ({c (V.u i), c (V.v i), c (V.p i)} : Finset ℕ).card = 3 := by
    simp [hd1, hd2, hd3]
  have h3 : 3 ≤ (L (V.u i)).card := by
    calc 3 = _ := hc3.symm
      _ ≤ _ := Finset.card_le_card hset
  have := L_two (V.u i)
  omega

/-- The four triangles contain exactly the non-terminal vertices. -/
lemma terminals_union_allTriangles : terminals ∪ allTriangles = (Finset.univ : Finset V) := by
  ext w
  cases w with
  | s1 => simp [terminals]
  | s2 => simp [terminals]
  | u i =>
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    exact Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [T]⟩)
  | v i =>
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    exact Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [T]⟩)
  | p i =>
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    exact Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [T]⟩)

lemma disjoint_terminals_allTriangles : Disjoint terminals allTriangles := by
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  simp only [terminals, Finset.mem_insert, Finset.mem_singleton] at hw1
  obtain ⟨i, -, hwi⟩ := Finset.mem_biUnion.mp hw2
  rcases hw1 with rfl | rfl <;> simp [T] at hwi

lemma partition_card (S : Finset V) :
    S.card = (S ∩ terminals).card + (S ∩ allTriangles).card := by
  have hdisj : Disjoint (S ∩ terminals) (S ∩ allTriangles) :=
    disjoint_terminals_allTriangles.mono Finset.inter_subset_right Finset.inter_subset_right
  have hEq : S = (S ∩ terminals) ∪ (S ∩ allTriangles) := by
    rw [← Finset.inter_union_distrib_left, terminals_union_allTriangles, Finset.inter_univ]
  conv_lhs => rw [hEq]
  exact Finset.card_union_of_disjoint hdisj

lemma inter_allTriangles_eq (S : Finset V) :
    S ∩ allTriangles = (Finset.univ : Finset (Fin 4)).biUnion (fun i => S ∩ T i) := by
  ext w
  simp only [allTriangles, Finset.mem_inter, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hwS, i, hwi⟩
    exact ⟨i, hwS, hwi⟩
  · rintro ⟨i, hwS, hwi⟩
    exact ⟨hwS, i, hwi⟩

lemma card_allTriangles_le (S : Finset V) (h : ∀ i, (S ∩ T i).card ≤ 2) :
    (S ∩ allTriangles).card ≤ 8 := by
  rw [inter_allTriangles_eq S]
  calc ((Finset.univ : Finset (Fin 4)).biUnion (fun i => S ∩ T i)).card
      ≤ ∑ i : Fin 4, (S ∩ T i).card := Finset.card_biUnion_le
    _ ≤ ∑ i : Fin 4, 2 := Finset.sum_le_sum (fun i _ => h i)
    _ = 8 := by simp

/-- If both terminals are coloured and triangle `T i` carries their two colours as its list,
then at most one vertex of `T i` can be coloured. -/
lemma special_triangle_bound (S : Finset V) (c : V → ℕ)
    (h : IsPartialListColoring G L S c) (h1 : V.s1 ∈ S) (h2 : V.s2 ∈ S) (i : Fin 4)
    (hlist : L (V.u i) = {c V.s1, c V.s2}) : (S ∩ T i).card ≤ 1 := by
  have hu : V.u i ∉ S := by
    intro huS
    have hineq : c (V.u i) ∈ L (V.u i) := h.1 _ huS
    rw [hlist] at hineq
    have hne1 : c (V.u i) ≠ c V.s1 := h.2 _ huS _ h1 (adj_s1_u i).symm
    have hne2 : c (V.u i) ≠ c V.s2 := h.2 _ huS _ h2 (adj_s2_u i).symm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hineq
    rcases hineq with h' | h'
    · exact hne1 h'
    · exact hne2 h'
  have hv : V.v i ∉ S := by
    intro hvS
    have hineq : c (V.v i) ∈ L (V.v i) := h.1 _ hvS
    have hlist' : L (V.v i) = {c V.s1, c V.s2} := hlist
    rw [hlist'] at hineq
    have hne1 : c (V.v i) ≠ c V.s1 := h.2 _ hvS _ h1 (adj_s1_v i).symm
    have hne2 : c (V.v i) ≠ c V.s2 := h.2 _ hvS _ h2 (adj_s2_v i).symm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hineq
    rcases hineq with h' | h'
    · exact hne1 h'
    · exact hne2 h'
  calc (S ∩ T i).card ≤ ({V.p i} : Finset V).card := by
        apply Finset.card_le_card
        intro w hw
        obtain ⟨hwS, hwi⟩ := Finset.mem_inter.mp hw
        simp only [T, Finset.mem_insert, Finset.mem_singleton] at hwi ⊢
        rcases hwi with rfl | rfl | rfl
        · exact absurd hwS hu
        · exact absurd hwS hv
        · simp
    _ = 1 := by simp

/-- The 2-list assignment `L` admits no partial proper colouring of more than nine vertices. -/
theorem nine_bound (S : Finset V) (c : V → ℕ) (h : IsPartialListColoring G L S c) :
    S.card ≤ 9 := by
  have htri : ∀ i : Fin 4, (S ∩ T i).card ≤ 2 := fun i => triangle_card_le_two S c h i
  have hcard := partition_card S
  by_cases hboth : V.s1 ∈ S ∧ V.s2 ∈ S
  · have hU : (S ∩ terminals).card = 2 := by
      have heq : S ∩ terminals = terminals := by
        ext w
        simp only [Finset.mem_inter, terminals, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨-, h'⟩; exact h'
        · rintro (rfl | rfl)
          · exact ⟨hboth.1, Or.inl rfl⟩
          · exact ⟨hboth.2, Or.inr rfl⟩
      rw [heq]; simp [terminals]
    have ha : c V.s1 = 0 ∨ c V.s1 = 1 := by
      have h' := h.1 _ hboth.1
      simpa [L] using h'
    have hb : c V.s2 = 2 ∨ c V.s2 = 3 := by
      have h' := h.1 _ hboth.2
      simpa [L] using h'
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · -- terminal colours 0 and 2: triangle `T 0` collapses to `{p 0}`
      have hspec : (S ∩ T 0).card ≤ 1 := by
        apply special_triangle_bound S c h hboth.1 hboth.2 0
        rw [ha, hb]; decide
      have hAl : (S ∩ allTriangles).card ≤ 7 := by
        rw [inter_allTriangles_eq S]
        calc ((Finset.univ : Finset (Fin 4)).biUnion (fun i => S ∩ T i)).card
            ≤ ∑ i : Fin 4, (S ∩ T i).card := Finset.card_biUnion_le
          _ ≤ ∑ i : Fin 4, (if i = (0 : Fin 4) then 1 else 2) := by
              apply Finset.sum_le_sum
              intro i _
              by_cases hi : i = (0 : Fin 4)
              · subst hi; simpa using hspec
              · simpa [hi] using htri i
          _ = 7 := by decide
      omega
    · -- terminal colours 0 and 3: triangle `T 1`
      have hspec : (S ∩ T 1).card ≤ 1 := by
        apply special_triangle_bound S c h hboth.1 hboth.2 1
        rw [ha, hb]; decide
      have hAl : (S ∩ allTriangles).card ≤ 7 := by
        rw [inter_allTriangles_eq S]
        calc ((Finset.univ : Finset (Fin 4)).biUnion (fun i => S ∩ T i)).card
            ≤ ∑ i : Fin 4, (S ∩ T i).card := Finset.card_biUnion_le
          _ ≤ ∑ i : Fin 4, (if i = (1 : Fin 4) then 1 else 2) := by
              apply Finset.sum_le_sum
              intro i _
              by_cases hi : i = (1 : Fin 4)
              · subst hi; simpa using hspec
              · simpa [hi] using htri i
          _ = 7 := by decide
      omega
    · -- terminal colours 1 and 2: triangle `T 2`
      have hspec : (S ∩ T 2).card ≤ 1 := by
        apply special_triangle_bound S c h hboth.1 hboth.2 2
        rw [ha, hb]; decide
      have hAl : (S ∩ allTriangles).card ≤ 7 := by
        rw [inter_allTriangles_eq S]
        calc ((Finset.univ : Finset (Fin 4)).biUnion (fun i => S ∩ T i)).card
            ≤ ∑ i : Fin 4, (S ∩ T i).card := Finset.card_biUnion_le
          _ ≤ ∑ i : Fin 4, (if i = (2 : Fin 4) then 1 else 2) := by
              apply Finset.sum_le_sum
              intro i _
              by_cases hi : i = (2 : Fin 4)
              · subst hi; simpa using hspec
              · simpa [hi] using htri i
          _ = 7 := by decide
      omega
    · -- terminal colours 1 and 3: triangle `T 3`
      have hspec : (S ∩ T 3).card ≤ 1 := by
        apply special_triangle_bound S c h hboth.1 hboth.2 3
        rw [ha, hb]; decide
      have hAl : (S ∩ allTriangles).card ≤ 7 := by
        rw [inter_allTriangles_eq S]
        calc ((Finset.univ : Finset (Fin 4)).biUnion (fun i => S ∩ T i)).card
            ≤ ∑ i : Fin 4, (S ∩ T i).card := Finset.card_biUnion_le
          _ ≤ ∑ i : Fin 4, (if i = (3 : Fin 4) then 1 else 2) := by
              apply Finset.sum_le_sum
              intro i _
              by_cases hi : i = (3 : Fin 4)
              · subst hi; simpa using hspec
              · simpa [hi] using htri i
          _ = 7 := by decide
      omega
  · have hU1 : (S ∩ terminals).card ≤ 1 := by
      by_cases h1 : V.s1 ∈ S
      · have h2 : V.s2 ∉ S := fun h2 => hboth ⟨h1, h2⟩
        have hsub : S ∩ terminals ⊆ {V.s1} := by
          intro w hw
          obtain ⟨hwS, hwt⟩ := Finset.mem_inter.mp hw
          simp only [terminals, Finset.mem_insert, Finset.mem_singleton] at hwt ⊢
          rcases hwt with rfl | rfl
          · simp
          · exact absurd hwS h2
        calc (S ∩ terminals).card ≤ ({V.s1} : Finset V).card := Finset.card_le_card hsub
          _ = 1 := by simp
      · have hsub : S ∩ terminals ⊆ {V.s2} := by
          intro w hw
          obtain ⟨hwS, hwt⟩ := Finset.mem_inter.mp hw
          simp only [terminals, Finset.mem_insert, Finset.mem_singleton] at hwt ⊢
          rcases hwt with rfl | rfl
          · exact absurd hwS h1
          · simp
        calc (S ∩ terminals).card ≤ ({V.s2} : Finset V).card := Finset.card_le_card hsub
          _ = 1 := by simp
    have hAl : (S ∩ allTriangles).card ≤ 8 := card_allTriangles_le S htri
    omega

lemma card_sdiff_pair_ge' (s : Finset ℕ) (x y : ℕ) : s.card - 2 ≤ (s \ {x, y}).card := by
  rw [Finset.card_sdiff]
  have h : (({x, y} : Finset ℕ) ∩ s).card ≤ 2 := by
    calc (({x, y} : Finset ℕ) ∩ s).card ≤ ({x, y} : Finset ℕ).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ ≤ 2 := by
          rcases eq_or_ne x y with h | h
          · subst h; simp
          · simp [h]
  omega

/-- `G` is 3-choosable: the paper's case analysis on `L(s_1) ∩ L(s_2)`. -/
theorem choosable_three : Choosable G 3 := by
  intro L' hL'
  by_cases hcase : (L' V.s1 ∩ L' V.s2).Nonempty
  · -- Case 1: the two terminal lists intersect.
    obtain ⟨x, hx⟩ := hcase
    have hx1 : x ∈ L' V.s1 := Finset.mem_of_mem_inter_left hx
    have hx2 : x ∈ L' V.s2 := Finset.mem_of_mem_inter_right hx
    have htri : ∀ i : Fin 4, ∃ a b e : ℕ,
        a ∈ L' (V.u i) \ {x} ∧ b ∈ L' (V.v i) \ {x} ∧ e ∈ L' (V.p i) ∧
        a ≠ b ∧ a ≠ e ∧ b ≠ e := by
      intro i
      obtain ⟨a, ha, b, hb, e, he, h1, h2, h3⟩ :=
        exists_pairwise_distinct (A := L' (V.u i) \ {x}) (B := L' (V.v i) \ {x})
          (C := L' (V.p i))
          (by have h := card_sdiff_singleton_ge (L' (V.u i)) x
              have h2 := hL' (V.u i)
              omega)
          (by have h := card_sdiff_singleton_ge (L' (V.v i)) x
              have h2 := hL' (V.v i)
              omega)
          (by have h := hL' (V.p i); omega)
      exact ⟨a, b, e, ha, hb, he, h1, h2, h3⟩
    choose ca cb cp hca hcb hcp hne1 hne2 hne3 using htri
    have hx_ca : ∀ i : Fin 4, x ≠ ca i := fun i => by
      have h : ca i ≠ x := by simpa using (Finset.mem_sdiff.mp (hca i)).2
      exact h.symm
    have hx_cb : ∀ i : Fin 4, x ≠ cb i := fun i => by
      have h : cb i ≠ x := by simpa using (Finset.mem_sdiff.mp (hcb i)).2
      exact h.symm
    have hcb_ca : ∀ i : Fin 4, cb i ≠ ca i := fun i => (hne1 i).symm
    have hcp_ca : ∀ i : Fin 4, cp i ≠ ca i := fun i => (hne2 i).symm
    have hcp_cb : ∀ i : Fin 4, cp i ≠ cb i := fun i => (hne3 i).symm
    refine ⟨fun w => match w with
      | .s1 => x
      | .s2 => x
      | .u i => ca i
      | .v i => cb i
      | .p i => cp i, ?_, ?_⟩
    · intro w
      cases w with
      | s1 => exact hx1
      | s2 => exact hx2
      | u i => exact (Finset.mem_sdiff.mp (hca i)).1
      | v i => exact (Finset.mem_sdiff.mp (hcb i)).1
      | p i => exact hcp i
    · intro a b hab
      cases a <;> cases b <;> simp_all [G_adj, adjB]
  · -- Case 2: the two terminal lists are disjoint.
    have hdisj : Disjoint (L' V.s1) (L' V.s2) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact Finset.not_nonempty_iff_eq_empty.mp hcase
    let P : Fin 4 → Finset (ℕ × ℕ) := fun i =>
      (L' (V.u i) ∩ L' V.s1) ×ˢ (L' (V.u i) ∩ L' V.s2)
    have hPle : ∀ i : Fin 4, (P i).card ≤ 2 := by
      intro i
      have hPcard : (P i).card =
          (L' (V.u i) ∩ L' V.s1).card * (L' (V.u i) ∩ L' V.s2).card := by
        simp [P, Finset.card_product]
      rw [hPcard]
      apply mul_le_two_of_add_le_three
      have hd : Disjoint (L' (V.u i) ∩ L' V.s1) (L' (V.u i) ∩ L' V.s2) :=
        hdisj.mono Finset.inter_subset_right Finset.inter_subset_right
      have hunion : ((L' (V.u i) ∩ L' V.s1) ∪ (L' (V.u i) ∩ L' V.s2)).card =
          (L' (V.u i) ∩ L' V.s1).card + (L' (V.u i) ∩ L' V.s2).card :=
        Finset.card_union_of_disjoint hd
      have hsub : ((L' (V.u i) ∩ L' V.s1) ∪ (L' (V.u i) ∩ L' V.s2)) ⊆ L' (V.u i) := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact (Finset.mem_inter.mp hw).1
        · exact (Finset.mem_inter.mp hw).1
      have h3 := Finset.card_le_card hsub
      rw [hL' (V.u i)] at h3
      omega
    have hUnion_le : ((Finset.univ : Finset (Fin 4)).biUnion P).card ≤ 8 := by
      calc ((Finset.univ : Finset (Fin 4)).biUnion P).card
          ≤ ∑ i : Fin 4, (P i).card := Finset.card_biUnion_le
        _ ≤ ∑ i : Fin 4, 2 := Finset.sum_le_sum (fun i _ => hPle i)
        _ = 8 := by simp
    have hQcard : (L' V.s1 ×ˢ L' V.s2).card = 9 := by
      rw [Finset.card_product, hL' V.s1, hL' V.s2]
    have hnotsub : ¬ (L' V.s1 ×ˢ L' V.s2) ⊆ (Finset.univ : Finset (Fin 4)).biUnion P := by
      intro hsub
      have h1 := Finset.card_le_card hsub
      omega
    obtain ⟨p, hpQ, hpR⟩ := Finset.not_subset.mp hnotsub
    have hp1 : p.1 ∈ L' V.s1 := (Finset.mem_product.mp hpQ).1
    have hp2 : p.2 ∈ L' V.s2 := (Finset.mem_product.mp hpQ).2
    have hpNot : ∀ i : Fin 4, ¬ (p.1 ∈ L' (V.u i) ∧ p.2 ∈ L' (V.u i)) := by
      intro i hcon
      exact hpR (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by
        rw [Finset.mem_product]
        exact ⟨Finset.mem_inter.mpr ⟨hcon.1, hp1⟩, Finset.mem_inter.mpr ⟨hcon.2, hp2⟩⟩⟩)
    have htri : ∀ i : Fin 4, ∃ a b e : ℕ,
        a ∈ L' (V.u i) \ {p.1, p.2} ∧ b ∈ L' (V.v i) \ {p.1, p.2} ∧
        e ∈ L' (V.p i) ∧ a ≠ b ∧ a ≠ e ∧ b ≠ e := by
      intro i
      have hv1 : 1 ≤ (L' (V.v i) \ {p.1, p.2}).card := by
        have h := card_sdiff_pair_ge' (L' (V.v i)) p.1 p.2
        have h2 := hL' (V.v i)
        omega
      have hu2 : 2 ≤ (L' (V.u i) \ {p.1, p.2}).card := by
        have h := card_sdiff_pair_ge (L' (V.u i)) p.1 p.2 (hpNot i)
        have h2 := hL' (V.u i)
        omega
      obtain ⟨xv, hxv, xu, hxu, z, hz, h1, h2, h3⟩ :=
        exists_pairwise_distinct (A := L' (V.v i) \ {p.1, p.2})
          (B := L' (V.u i) \ {p.1, p.2}) (C := L' (V.p i)) hv1 hu2
          (by have h := hL' (V.p i); omega)
      exact ⟨xu, xv, z, hxu, hxv, hz, h1.symm, h3, h2⟩
    choose cu cv cp hcu hcv hcp hne1 hne2 hne3 using htri
    have hp_cu1 : ∀ i : Fin 4, p.1 ≠ cu i := fun i => by
      intro hh
      have h := (Finset.mem_sdiff.mp (hcu i)).2
      exact h (by rw [Finset.mem_insert, Finset.mem_singleton]; exact Or.inl hh.symm)
    have hp_cu2 : ∀ i : Fin 4, p.2 ≠ cu i := fun i => by
      intro hh
      have h := (Finset.mem_sdiff.mp (hcu i)).2
      exact h (by rw [Finset.mem_insert, Finset.mem_singleton]; exact Or.inr hh.symm)
    have hp_cv1 : ∀ i : Fin 4, p.1 ≠ cv i := fun i => by
      intro hh
      have h := (Finset.mem_sdiff.mp (hcv i)).2
      exact h (by rw [Finset.mem_insert, Finset.mem_singleton]; exact Or.inl hh.symm)
    have hp_cv2 : ∀ i : Fin 4, p.2 ≠ cv i := fun i => by
      intro hh
      have h := (Finset.mem_sdiff.mp (hcv i)).2
      exact h (by rw [Finset.mem_insert, Finset.mem_singleton]; exact Or.inr hh.symm)
    have hcv_cu : ∀ i : Fin 4, cv i ≠ cu i := fun i => (hne1 i).symm
    have hcp_cu : ∀ i : Fin 4, cp i ≠ cu i := fun i => (hne2 i).symm
    have hcp_cv : ∀ i : Fin 4, cp i ≠ cv i := fun i => (hne3 i).symm
    refine ⟨fun w => match w with
      | .s1 => p.1
      | .s2 => p.2
      | .u i => cu i
      | .v i => cv i
      | .p i => cp i, ?_, ?_⟩
    · intro w
      cases w with
      | s1 => exact hp1
      | s2 => exact hp2
      | u i => exact (Finset.mem_sdiff.mp (hcu i)).1
      | v i => exact (Finset.mem_sdiff.mp (hcv i)).1
      | p i => exact hcp i
    · intro a b hab
      cases a <;> cases b <;> simp_all [G_adj, adjB]

/-- `G` is not 2-choosable: the paper's 2-list assignment `L` has no full proper colouring,
since at most 9 of the 14 vertices can be coloured from `L`. -/
theorem not_choosable_two : ¬ Choosable G 2 := by
  intro h
  have hL : IsListAssignment L 2 := by unfold IsListAssignment; decide
  obtain ⟨c, hc1, hc2⟩ := h L hL
  have hls : IsPartialListColoring G L (Finset.univ : Finset V) c := by
    refine ⟨?_, ?_⟩
    · intro v _
      exact hc1 v
    · intro u _ v _ huv
      exact hc2 u v huv
  have h9 := nine_bound (Finset.univ : Finset V) c hls
  have h14 : (Finset.univ : Finset V).card = 14 := by decide
  omega

/-- `G` is not 1-choosable: the constant 1-list assignment with list `{0}` admits no proper
colouring, since `G` has an edge. -/
theorem not_choosable_one : ¬ Choosable G 1 := by
  intro h
  have hL : IsListAssignment (fun _ : V => ({0} : Finset ℕ)) 1 := by
    intro v; simp
  obtain ⟨c, hc1, hc2⟩ := h (fun _ => {0}) hL
  have h0 : c (V.u 0) = 0 := by simpa using hc1 (V.u 0)
  have h1 : c (V.v 0) = 0 := by simpa using hc1 (V.v 0)
  exact hc2 (V.u 0) (V.v 0) (by decide) (by simp [h0, h1])

/-- `G` is not 0-choosable: every vertex has an empty list, so no vertex can be coloured. -/
theorem not_choosable_zero : ¬ Choosable G 0 := by
  intro h
  have hL : IsListAssignment (fun _ : V => (∅ : Finset ℕ)) 0 := fun v => by simp
  obtain ⟨c, hc1, hc2⟩ := h (fun _ => ∅) hL
  have hmem : c V.s1 ∈ (∅ : Finset ℕ) := hc1 V.s1
  exact absurd hmem (by simp)

/-- The paper's Theorem 1: the 14-vertex graph `G` has list chromatic number exactly 3, the
2-list assignment `L` admits no partial proper colouring of more than 9 vertices. -/
theorem counterexample : counterexample_statement := by
  refine ⟨by decide, ⟨choosable_three, ?_⟩, by unfold IsListAssignment; decide, nine_bound⟩
  intro j hj
  interval_cases j
  · exact not_choosable_zero
  · exact not_choosable_one
  · exact not_choosable_two

end

end Noel

/-- A graph that is choosable in the `ℕ`-list sense is list-colorable over
an arbitrary color type: the finite union of the lists is injectively encoded in `ℕ`. -/
lemma isListColorable_of_choosable {W : Type*} [Finite W]
    {H : SimpleGraph W} {q : ℕ} (h : Noel.Choosable H q) :
    H.IsListColorable q := by
  intro C _ lists hlists
  classical
  have : Fintype W := Fintype.ofFinite W
  let U : Finset C := Finset.univ.biUnion lists
  let e : {c // c ∈ U} ≃ Fin (Fintype.card U) := Fintype.equivFin _
  let ψ : C → ℕ := fun c => if hc : c ∈ U then (e ⟨c, hc⟩).val else 0
  have hψ : ∀ {a b : C}, a ∈ U → b ∈ U → ψ a = ψ b → a = b := by
    intro a b ha hb hab
    simp only [ψ, dite_eq_left ha, dite_eq_left hb] at hab
    have h1 : e ⟨a, ha⟩ = e ⟨b, hb⟩ := Fin.ext hab
    have h2 := e.injective h1
    simpa using congrArg Subtype.val h2
  -- `Noel.Choosable` uses lists of size exactly `q`; shrink the given lists to size `q`.
  have hsmall : ∀ v, ∃ t : Finset C, t ⊆ lists v ∧ t.card = q := fun v =>
    Finset.exists_subset_card_eq (hlists v)
  choose ls hls_sub hls_card using hsmall
  have hls_U : ∀ v, ls v ⊆ U := fun v c hc =>
    Finset.subset_biUnion_of_mem lists (Finset.mem_univ v) (hls_sub v hc)
  let lists' : W → Finset ℕ := fun v => (ls v).image ψ
  have hcard : ∀ v, (lists' v).card = q := by
    intro v
    have hinj : Set.InjOn ψ (↑(ls v) : Set C) := by
      intro a ha b hb hab
      exact hψ (hls_U v ha) (hls_U v hb) hab
    rw [Finset.card_image_of_injOn hinj]
    exact hls_card v
  obtain ⟨c', hmem', hprop'⟩ := h lists' hcard
  let g : W → C := fun v => Classical.choose (Finset.mem_image.mp (hmem' v))
  have hg_mem : ∀ v, g v ∈ lists v := fun v =>
    hls_sub v (Classical.choose_spec (Finset.mem_image.mp (hmem' v))).1
  have hg_val : ∀ v, ψ (g v) = c' v := fun v =>
    (Classical.choose_spec (Finset.mem_image.mp (hmem' v))).2
  refine ⟨⟨g, ?_⟩, hg_mem⟩
  intro u v huv hEq
  exact hprop' u v huv (by rw [← hg_val u, hEq, hg_val v])

/-- Conversely, list-colorability over `ℕ` gives `Noel.Choosable`. -/
lemma choosable_of_isListColorable {W : Type*} {H : SimpleGraph W} {q : ℕ}
    (h : H.IsListColorable q) : Noel.Choosable H q := by
  intro L hL
  obtain ⟨color, hmem⟩ := h ℕ L (fun v => by rw [hL v])
  exact ⟨color, hmem, fun u v huv => color.valid huv⟩

/-- Noel's explicit 14-vertex graph has choice number `3`, i.e. it
satisfies the hypothesis of `conjecture`. -/
theorem noel_isChoiceNumber : Noel.G.IsChoiceNumber 3 := by
  refine ⟨isListColorable_of_choosable Noel.choosable_three, ?_⟩
  intro r hr hlist
  have hch := choosable_of_isListColorable hlist
  interval_cases r
  · exact Noel.not_choosable_zero hch
  · exact Noel.not_choosable_one hch
  · exact Noel.not_choosable_two hch

/-- The set whose supremum is `lambdaMax G L` is nonempty: the empty set is always colourable. -/
private lemma lambdaMax_set_nonempty (L : Noel.V → Finset ℕ) :
    ({k : ℕ | ∃ S : Finset Noel.V, ∃ f : Noel.V → ℕ,
      S.card = k ∧ IsListColoring Noel.G L f S}).Nonempty :=
  ⟨0, ∅, fun _ => 0, rfl, by simp [IsListColoring]⟩

/-- `λ_L` never exceeds the number of vertices. -/
private lemma lambdaMax_le_card (L : Noel.V → Finset ℕ) :
    lambdaMax Noel.G L ≤ Fintype.card Noel.V := by
  apply csSup_le (lambdaMax_set_nonempty L)
  rintro k ⟨S, f, rfl, _⟩
  exact Finset.card_le_univ S

/-- The 2-list assignment `L` of the paper allows at most nine coloured vertices, so
`λ_L ≤ 9`. -/
private lemma lambdaMax_P02L_le_nine :
    lambdaMax Noel.G Noel.L ≤ 9 := by
  apply csSup_le (lambdaMax_set_nonempty Noel.L)
  rintro k ⟨S, f, rfl, hcol⟩
  exact Noel.nine_bound S f ⟨hcol.1, hcol.2⟩

/-- Every 3-list assignment admits a full proper colouring of the 14-vertex graph, hence
`λ_L = 14` for every 3-list assignment `L`. -/
private lemma lambdaMax_eq_fourteen (L : Noel.V → Finset ℕ)
    (hL : ∀ v, (L v).card = 3) :
    lambdaMax Noel.G L = 14 := by
  have hcard : Fintype.card Noel.V = 14 := by decide
  have hbdd : BddAbove {k : ℕ | ∃ S : Finset Noel.V, ∃ f : Noel.V → ℕ,
      S.card = k ∧ IsListColoring Noel.G L f S} := by
    refine ⟨14, ?_⟩
    rintro k ⟨S, f, rfl, _⟩
    have := Finset.card_le_univ S
    omega
  have hle : lambdaMax Noel.G L ≤ 14 := by
    apply csSup_le (lambdaMax_set_nonempty L)
    rintro k ⟨S, f, rfl, _⟩
    have := Finset.card_le_univ S
    omega
  have hmem : 14 ∈ {k : ℕ | ∃ S : Finset Noel.V, ∃ f : Noel.V → ℕ,
      S.card = k ∧ IsListColoring Noel.G L f S} := by
    obtain ⟨c, hc1, hc2⟩ := Noel.choosable_three L hL
    refine ⟨Finset.univ, c, ?_, ?_⟩
    · rw [Finset.card_univ]; exact hcard
    · refine ⟨?_, ?_⟩
      · intro v _; exact hc1 v
      · intro u _ v _ huv; exact hc2 u v huv
  have hge : 14 ≤ lambdaMax Noel.G L := le_csSup hbdd hmem
  omega

/-- `λ_2 ≤ 9`: the paper's 2-list assignment shows that the minimum over 2-list assignments
is at most nine. -/
private lemma lambdaMin_two_le_nine : lambdaMin Noel.G 2 ≤ 9 := by
  have hmem : lambdaMax Noel.G Noel.L ∈
      {k : ℕ | ∃ L : Noel.V → Finset ℕ,
        (∀ v, (L v).card = 2) ∧ lambdaMax Noel.G L = k} :=
    ⟨Noel.L, Noel.L_two, rfl⟩
  exact (Nat.sInf_le hmem).trans lambdaMax_P02L_le_nine

/-- `14 ≤ λ_3`: every 3-list assignment colours all fourteen vertices. -/
private lemma fourteen_le_lambdaMin_three : 14 ≤ lambdaMin Noel.G 3 := by
  apply le_csInf
  · refine ⟨lambdaMax Noel.G (fun _ => Finset.range 3),
      fun _ => Finset.range 3, ?_, rfl⟩
    intro v; simp
  · rintro k ⟨L, hL, rfl⟩
    rw [lambdaMax_eq_fourteen L hL]

/--
Resolved false: Noel (arXiv:2609.23291, Sept 2026), Theorem 1.1, gives a 14-vertex graph (four
triangles plus two terminals) with list chromatic number 3 and a 2-list assignment colouring at
most 9 vertices, so lambda_2/2 <= 9/2 < 14/3 = lambda_3/3, refuting the ratio conjecture at r=2,
s=3. Source: Jonathan A. Noel, The Partial List Colouring Conjecture is False, arXiv preprint
(2026), arXiv:2609.23291, https://arxiv.org/abs/2609.23291. Moved from
`OpenConjectures/GraphTheory/PartialListColoring`.
-/
theorem conjecture_refuted : ¬ conjecture := by
  intro hconj
  have hchoice := noel_isChoiceNumber
  have h2 := lambdaMin_two_le_nine
  have h3 := fourteen_le_lambdaMin_three
  have h := hconj Noel.V Noel.G 3 2 3 hchoice
    (by norm_num) (by norm_num) (by norm_num)
  have h2' : ((lambdaMin Noel.G 2 : ℕ) : ℚ) / 2 ≤ 9 / 2 := by
    have : ((lambdaMin Noel.G 2 : ℕ) : ℚ) ≤ 9 := by exact_mod_cast h2
    linarith
  have h3' : (14 : ℚ) / 3 ≤ ((lambdaMin Noel.G 3 : ℕ) : ℚ) / 3 := by
    have : (14 : ℚ) ≤ ((lambdaMin Noel.G 3 : ℕ) : ℚ) := by exact_mod_cast h3
    linarith
  linarith

end MathlibExt.GraphTheory.PartialListColoringWanted
