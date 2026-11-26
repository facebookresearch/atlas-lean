/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.DeriveFintype
public import MathlibExt.Combinatorics.SimpleGraph.ListColoring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Iradmusa's partial list colouring ratio conjecture is false

For a finite simple graph `G` and an assignment `L` of finite lists of colours to its vertices,
`lambdaMax G L` (written `λ_L`) is the largest number of vertices of `G` that can be properly
coloured from their lists, and `lambdaMin G t` (written `λ_t`) is the minimum of `λ_L` over all
assignments of lists of size `t`. Iradmusa conjectured that `λ_r / r ≥ λ_s / s` whenever
`1 ≤ r ≤ s ≤ χ_ℓ(G)`, where `χ_ℓ(G)` is the choice number of `G` (Open Problem Garden, posted
12 May 2008; M. N. Iradmusa, *A note on partial list coloring*, Australas. J. Combin. 46
(2010), 19–24). For `s = χ_ℓ(G)` this is the partial list colouring conjecture of Albertson,
Grossman and Haas, `λ_t ≥ t n / χ_ℓ(G)` for an `n`-vertex graph `G`.

Noel disproved that conjecture, and hence Iradmusa's (J. A. Noel, *The Partial List Colouring
Conjecture is False*, arXiv:2609.23291, Theorem 1.1). Take four disjoint triangles
`T₁, …, T₄`, each with a private vertex `pᵢ`, and two non-adjacent terminals `s₁, s₂` joined to
every non-private vertex of every triangle. This graph has choice number `3`, but for the
2-list assignment with `L(s₁) = {1, 2}`, `L(s₂) = {3, 4}` and the lists `{1, 3}`, `{1, 4}`,
`{2, 3}`, `{2, 4}` on the vertices of `T₁, …, T₄`, at most nine of its fourteen vertices can be
properly coloured. Hence `λ₂ / 2 ≤ 9 / 2 < 14 / 3 = λ₃ / 3`, which refutes Iradmusa's
conjecture for `r = 2` and `s = 3`.

## Main declarations

* `lambdaMax`, `lambdaMin`, `conjecture`: Iradmusa's quantities and conjecture.
* `card_le_lambdaMax`, `lambdaMax_le`, `lambdaMin_le_lambdaMax`, `le_lambdaMin`: bounds
  characterizing `lambdaMax` and `lambdaMin`.
* `Noel.G`, `Noel.L`: Noel's graph and 2-list assignment, with the colours `1, 2, 3, 4` encoded
  as `0, 1, 2, 3`.
* `Noel.card_le_nine`: every partial proper `Noel.L`-colouring colours at most nine vertices.
* `Noel.isChoiceNumber_three`: `Noel.G` has choice number `3`.
* `conjecture_refuted`: Iradmusa's conjecture is false.
-/

@[expose] public section

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

section Bounds

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {L : V → Finset ℕ}
  {f : V → ℕ} {S : Finset V} {k t : ℕ}

/-- A properly list-coloured vertex set has at most `λ_L` vertices. -/
theorem card_le_lambdaMax (h : IsListColoring G L f S) : S.card ≤ lambdaMax G L :=
  le_csSup ⟨Fintype.card V, by rintro _ ⟨S, f, rfl, -⟩; exact S.card_le_univ⟩ ⟨S, f, rfl, h⟩

/-- `λ_L ≤ k` when every properly list-coloured vertex set has at most `k` vertices. -/
theorem lambdaMax_le (h : ∀ (S : Finset V) (f : V → ℕ), IsListColoring G L f S → S.card ≤ k) :
    lambdaMax G L ≤ k :=
  csSup_le ⟨0, ∅, fun _ => 0, rfl, by simp [IsListColoring]⟩ <| by
    rintro _ ⟨S, f, rfl, hS⟩
    exact h S f hS

/-- `λ_L` is at most the number of vertices. -/
theorem lambdaMax_le_card (G : SimpleGraph V) (L : V → Finset ℕ) :
    lambdaMax G L ≤ Fintype.card V :=
  lambdaMax_le fun S _ _ => S.card_le_univ

/-- `λ_t ≤ λ_L` for every assignment `L` of lists of size `t`. -/
theorem lambdaMin_le_lambdaMax (hL : ∀ v, (L v).card = t) : lambdaMin G t ≤ lambdaMax G L :=
  Nat.sInf_le ⟨L, hL, rfl⟩

/-- `k ≤ λ_t` when `k ≤ λ_L` for every assignment `L` of lists of size `t`. -/
theorem le_lambdaMin (h : ∀ L : V → Finset ℕ, (∀ v, (L v).card = t) → k ≤ lambdaMax G L) :
    k ≤ lambdaMin G t :=
  le_csInf ⟨_, fun _ => Finset.range t, fun _ => Finset.card_range t, rfl⟩ <| by
    rintro _ ⟨L, hL, rfl⟩
    exact h L hL

end Bounds

namespace Noel

/-- The 14 vertices of Noel's graph: the two terminals `s1` and `s2` and, for each of the four
triangles, its private vertex `p i` and its non-private vertices `u i` and `v i`. The paper's
triangle `T_{i+1}` is `T i`. -/
inductive V : Type
  | s1 : V
  | s2 : V
  | u : Fin 4 → V
  | v : Fin 4 → V
  | p : Fin 4 → V
  deriving DecidableEq, Fintype

/-- The adjacency relation of Noel's graph, as a Boolean function.

* `s1` and `s2` are non-adjacent;
* both `s1` and `s2` are adjacent to `u i` and `v i` for every `i`;
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

/-- Noel's graph. -/
def G : SimpleGraph V where
  Adj a b := adjB a b = true
  symm := ⟨by
    intro a b h
    cases a <;> cases b <;> simp_all [adjB]⟩
  loopless := ⟨by
    intro a
    cases a <;> simp [adjB]⟩

@[simp] theorem G_adj {a b : V} : G.Adj a b ↔ adjB a b = true := Iff.rfl

instance : DecidableRel G.Adj := fun a b => inferInstanceAs (Decidable (adjB a b = true))

/-- The triangle `T i` (the paper's `T_{i+1}`). -/
def T (i : Fin 4) : Finset V := {V.u i, V.v i, V.p i}

/-- The two terminals. -/
def terminals : Finset V := {V.s1, V.s2}

/-- The common list of the vertices of `T i`. In the paper's colours these are
`T_1 ↦ {1, 3}`, `T_2 ↦ {1, 4}`, `T_3 ↦ {2, 3}`, `T_4 ↦ {2, 4}`; with the encoding
`1, 2, 3, 4 ↦ 0, 1, 2, 3` they are `{0, 2}, {0, 3}, {1, 2}, {1, 3}`. -/
def listOf : Fin 4 → Finset ℕ
  | ⟨0, _⟩ => {0, 2}
  | ⟨1, _⟩ => {0, 3}
  | ⟨2, _⟩ => {1, 2}
  | _ => {1, 3}

/-- Noel's 2-list assignment: `L(s1) = {1, 2}`, `L(s2) = {3, 4}`, and every vertex of `T i` has
the list `listOf i` (the paper's colours `1, 2, 3, 4` are encoded as `0, 1, 2, 3`). -/
def L : V → Finset ℕ
  | .s1 => {0, 1}
  | .s2 => {2, 3}
  | .u i => listOf i
  | .v i => listOf i
  | .p i => listOf i

theorem card_listOf (i : Fin 4) : (listOf i).card = 2 := by
  fin_cases i <;> decide

theorem card_L (w : V) : (L w).card = 2 := by
  cases w with
  | s1 => simp [L]
  | s2 => simp [L]
  | u i => exact card_listOf i
  | v i => exact card_listOf i
  | p i => exact card_listOf i

section Proofs

open Finset

private lemma card_sdiff_singleton_ge {α : Type*} [DecidableEq α] (s : Finset α) (x : α) :
    s.card - 1 ≤ (s \ {x}).card := by
  simpa using le_card_sdiff {x} s

private lemma card_sdiff_pair_ge {α : Type*} [DecidableEq α] (s : Finset α) (x y : α) :
    s.card - 2 ≤ (s \ {x, y}).card :=
  (Nat.sub_le_sub_left card_le_two s.card).trans (le_card_sdiff {x, y} s)

private lemma card_sdiff_pair_ge_of_not_and {α : Type*} [DecidableEq α] (s : Finset α) (x y : α)
    (h : ¬ (x ∈ s ∧ y ∈ s)) : s.card - 1 ≤ (s \ {x, y}).card := by
  rcases not_and_or.mp h with hx | hy
  · have hs : s \ {x, y} = s \ {y} := by
      ext z
      simp only [mem_sdiff, mem_insert, mem_singleton, not_or]
      constructor
      · rintro ⟨hz, -, hzy⟩
        exact ⟨hz, hzy⟩
      · rintro ⟨hz, hzy⟩
        exact ⟨hz, fun hzx => hx (hzx ▸ hz), hzy⟩
    rw [hs]
    exact card_sdiff_singleton_ge s y
  · have hs : s \ {x, y} = s \ {x} := by
      ext z
      simp only [mem_sdiff, mem_insert, mem_singleton, not_or]
      constructor
      · rintro ⟨hz, hzx, -⟩
        exact ⟨hz, hzx⟩
      · rintro ⟨hz, hzx⟩
        exact ⟨hz, hzx, fun hzy => hy (hzy ▸ hz)⟩
    rw [hs]
    exact card_sdiff_singleton_ge s x

private lemma mul_le_two_of_add_le_three {a b : ℕ} (h : a + b ≤ 3) : a * b ≤ 2 := by
  have ha : a ≤ 3 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;> omega

/-- Three lists of sizes at least 1, 2, 3 admit pairwise distinct representatives. -/
private lemma exists_pairwise_distinct {α : Type*} {A B C : Finset α}
    (hA : 1 ≤ A.card) (hB : 2 ≤ B.card) (hC : 3 ≤ C.card) :
    ∃ x ∈ A, ∃ y ∈ B, ∃ z ∈ C, x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  classical
  obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < A.card)
  have hBpos : 0 < (B \ {x}).card := by
    have h := card_sdiff_singleton_ge B x
    omega
  obtain ⟨y, hy⟩ := card_pos.mp hBpos
  have hyB : y ∈ B := (mem_sdiff.mp hy).1
  have hyx : y ≠ x := by simpa using (mem_sdiff.mp hy).2
  have hCpos : 0 < ((C \ {x}) \ {y}).card := by
    have h1 := card_sdiff_singleton_ge C x
    have h2 := card_sdiff_singleton_ge (C \ {x}) y
    omega
  obtain ⟨z, hz⟩ := card_pos.mp hCpos
  have hzCx : z ∈ C \ {x} := (mem_sdiff.mp hz).1
  have hzy : z ≠ y := by simpa using (mem_sdiff.mp hz).2
  have hzC : z ∈ C := (mem_sdiff.mp hzCx).1
  have hzx : z ≠ x := by simpa using (mem_sdiff.mp hzCx).2
  exact ⟨x, hx, y, hyB, z, hzC, hyx.symm, hzx.symm, hzy.symm⟩

private lemma adj_u_v (i : Fin 4) : G.Adj (V.u i) (V.v i) := by simp [adjB]

private lemma adj_u_p (i : Fin 4) : G.Adj (V.u i) (V.p i) := by simp [adjB]

private lemma adj_v_p (i : Fin 4) : G.Adj (V.v i) (V.p i) := by simp [adjB]

private lemma adj_s1_u (i : Fin 4) : G.Adj V.s1 (V.u i) := by simp [adjB]

private lemma adj_s1_v (i : Fin 4) : G.Adj V.s1 (V.v i) := by simp [adjB]

private lemma adj_s2_u (i : Fin 4) : G.Adj V.s2 (V.u i) := by simp [adjB]

private lemma adj_s2_v (i : Fin 4) : G.Adj V.s2 (V.v i) := by simp [adjB]

/-- A triangle with a common list of size 2 contributes at most two coloured vertices. -/
private lemma triangle_card_le_two {S : Finset V} {c : V → ℕ} (h : IsListColoring G L c S)
    (i : Fin 4) : (S ∩ T i).card ≤ 2 := by
  by_contra hle
  have hge : 3 ≤ (S ∩ T i).card := by omega
  have hcardT : (T i).card = 3 := by simp [T]
  have heq : S ∩ T i = T i := eq_of_subset_of_card_le inter_subset_right (by omega)
  have hu : V.u i ∈ S := by
    have h' : V.u i ∈ S ∩ T i := by rw [heq]; simp [T]
    exact mem_of_mem_inter_left h'
  have hv : V.v i ∈ S := by
    have h' : V.v i ∈ S ∩ T i := by rw [heq]; simp [T]
    exact mem_of_mem_inter_left h'
  have hp : V.p i ∈ S := by
    have h' : V.p i ∈ S ∩ T i := by rw [heq]; simp [T]
    exact mem_of_mem_inter_left h'
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
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hmu
    · rw [hLuv]; exact hmv
    · rw [hLuv, hLvp]; exact hmp
  have hc3 : ({c (V.u i), c (V.v i), c (V.p i)} : Finset ℕ).card = 3 := by
    simp [hd1, hd2, hd3]
  have h3 : 3 ≤ (L (V.u i)).card := by
    calc 3 = _ := hc3.symm
      _ ≤ _ := card_le_card hset
  have := card_L (V.u i)
  omega

/-- The four triangles cover exactly the non-terminal vertices. -/
private lemma terminals_union_allTriangles :
    terminals ∪ (univ : Finset (Fin 4)).biUnion T = (univ : Finset V) := by
  ext w
  cases w with
  | s1 => simp [terminals]
  | s2 => simp [terminals]
  | u i =>
    simp only [mem_union, mem_univ, iff_true]
    exact Or.inr (mem_biUnion.mpr ⟨i, mem_univ _, by simp [T]⟩)
  | v i =>
    simp only [mem_union, mem_univ, iff_true]
    exact Or.inr (mem_biUnion.mpr ⟨i, mem_univ _, by simp [T]⟩)
  | p i =>
    simp only [mem_union, mem_univ, iff_true]
    exact Or.inr (mem_biUnion.mpr ⟨i, mem_univ _, by simp [T]⟩)

private lemma disjoint_terminals_allTriangles :
    Disjoint terminals ((univ : Finset (Fin 4)).biUnion T) := by
  rw [disjoint_left]
  intro w hw1 hw2
  simp only [terminals, mem_insert, mem_singleton] at hw1
  obtain ⟨i, -, hwi⟩ := mem_biUnion.mp hw2
  rcases hw1 with rfl | rfl <;> simp [T] at hwi

/-- A vertex set splits into its terminals and its vertices in the four triangles. -/
private lemma card_le_card_inter_terminals_add (S : Finset V) :
    S.card ≤ (S ∩ terminals).card + ∑ i : Fin 4, (S ∩ T i).card := by
  have hEq : S = (S ∩ terminals) ∪ (univ : Finset (Fin 4)).biUnion (fun i => S ∩ T i) := by
    rw [← inter_biUnion, ← inter_union_distrib_left, terminals_union_allTriangles, inter_univ]
  calc S.card = ((S ∩ terminals) ∪ (univ : Finset (Fin 4)).biUnion (fun i => S ∩ T i)).card := by
        rw [← hEq]
    _ ≤ (S ∩ terminals).card + ((univ : Finset (Fin 4)).biUnion (fun i => S ∩ T i)).card :=
        card_union_le _ _
    _ ≤ (S ∩ terminals).card + ∑ i : Fin 4, (S ∩ T i).card := by
        gcongr
        exact card_biUnion_le

/-- If every triangle has at most two coloured vertices and one has at most one, the four
triangles have at most seven coloured vertices. -/
private lemma sum_card_inter_T_le_seven (S : Finset V) (h : ∀ i, (S ∩ T i).card ≤ 2)
    (i₀ : Fin 4) (h₀ : (S ∩ T i₀).card ≤ 1) : ∑ i : Fin 4, (S ∩ T i).card ≤ 7 := by
  calc ∑ i : Fin 4, (S ∩ T i).card ≤ ∑ i : Fin 4, (if i = i₀ then 1 else 2) := by
        apply sum_le_sum
        intro i _
        by_cases hi : i = i₀
        · subst hi; simpa using h₀
        · simpa [hi] using h i
    _ = 7 := by fin_cases i₀ <;> decide

/-- If both terminals are coloured and triangle `T i` carries their two colours as its list,
then at most one vertex of `T i` can be coloured. -/
private lemma special_triangle_bound {S : Finset V} {c : V → ℕ} (h : IsListColoring G L c S)
    (h1 : V.s1 ∈ S) (h2 : V.s2 ∈ S) (i : Fin 4) (hlist : L (V.u i) = {c V.s1, c V.s2}) :
    (S ∩ T i).card ≤ 1 := by
  have hu : V.u i ∉ S := by
    intro huS
    have hineq : c (V.u i) ∈ L (V.u i) := h.1 _ huS
    rw [hlist] at hineq
    have hne1 : c (V.u i) ≠ c V.s1 := h.2 _ huS _ h1 (adj_s1_u i).symm
    have hne2 : c (V.u i) ≠ c V.s2 := h.2 _ huS _ h2 (adj_s2_u i).symm
    simp only [mem_insert, mem_singleton] at hineq
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
    simp only [mem_insert, mem_singleton] at hineq
    rcases hineq with h' | h'
    · exact hne1 h'
    · exact hne2 h'
  calc (S ∩ T i).card ≤ ({V.p i} : Finset V).card := by
        apply card_le_card
        intro w hw
        obtain ⟨hwS, hwi⟩ := mem_inter.mp hw
        simp only [T, mem_insert, mem_singleton] at hwi ⊢
        rcases hwi with rfl | rfl | rfl
        · exact absurd hwS hu
        · exact absurd hwS hv
        · simp
    _ = 1 := by simp

/-- No partial proper colouring from Noel's 2-list assignment colours more than nine
vertices. -/
theorem card_le_nine {S : Finset V} {c : V → ℕ} (h : IsListColoring G L c S) :
    S.card ≤ 9 := by
  have htri : ∀ i : Fin 4, (S ∩ T i).card ≤ 2 := triangle_card_le_two h
  have hcard := card_le_card_inter_terminals_add S
  by_cases hboth : V.s1 ∈ S ∧ V.s2 ∈ S
  · have hU : (S ∩ terminals).card ≤ 2 :=
      (card_le_card inter_subset_right).trans (by simp [terminals])
    have ha : c V.s1 = 0 ∨ c V.s1 = 1 := by simpa [L] using h.1 _ hboth.1
    have hb : c V.s2 = 2 ∨ c V.s2 = 3 := by simpa [L] using h.1 _ hboth.2
    -- The triangle whose list is the two terminal colours has at most one coloured vertex.
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin 4, L (V.u i₀) = {c V.s1, c V.s2} := by
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
    have h7 := sum_card_inter_T_le_seven S htri i₀
      (special_triangle_bound h hboth.1 hboth.2 i₀ hi₀)
    omega
  · have hU : (S ∩ terminals).card ≤ 1 := by
      by_cases h1 : V.s1 ∈ S
      · have h2 : V.s2 ∉ S := fun h2 => hboth ⟨h1, h2⟩
        have hsub : S ∩ terminals ⊆ {V.s1} := by
          intro w hw
          obtain ⟨hwS, hwt⟩ := mem_inter.mp hw
          simp only [terminals, mem_insert, mem_singleton] at hwt ⊢
          rcases hwt with rfl | rfl
          · rfl
          · exact absurd hwS h2
        simpa using card_le_card hsub
      · have hsub : S ∩ terminals ⊆ {V.s2} := by
          intro w hw
          obtain ⟨hwS, hwt⟩ := mem_inter.mp hw
          simp only [terminals, mem_insert, mem_singleton] at hwt ⊢
          rcases hwt with rfl | rfl
          · exact absurd hwS h1
          · rfl
        simpa using card_le_card hsub
    have h8 : ∑ i : Fin 4, (S ∩ T i).card ≤ ∑ _i : Fin 4, 2 := sum_le_sum fun i _ => htri i
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h8
    omega

/-- Lists of exactly three colours always admit a proper colouring of Noel's graph: the
paper's case analysis on whether the lists of the two terminals intersect. -/
private lemma exists_coloring_of_card_eq_three {C : Type*} (L' : V → Finset C)
    (hL' : ∀ w, (L' w).card = 3) :
    ∃ c : V → C, (∀ w, c w ∈ L' w) ∧ ∀ a b, G.Adj a b → c a ≠ c b := by
  classical
  by_cases hcase : (L' V.s1 ∩ L' V.s2).Nonempty
  · -- Case 1: the two terminal lists intersect.
    obtain ⟨x, hx⟩ := hcase
    have hx1 : x ∈ L' V.s1 := mem_of_mem_inter_left hx
    have hx2 : x ∈ L' V.s2 := mem_of_mem_inter_right hx
    have htri : ∀ i : Fin 4, ∃ a b e : C,
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
      have h : ca i ≠ x := by simpa using (mem_sdiff.mp (hca i)).2
      exact h.symm
    have hx_cb : ∀ i : Fin 4, x ≠ cb i := fun i => by
      have h : cb i ≠ x := by simpa using (mem_sdiff.mp (hcb i)).2
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
      | u i => exact (mem_sdiff.mp (hca i)).1
      | v i => exact (mem_sdiff.mp (hcb i)).1
      | p i => exact hcp i
    · intro a b hab
      cases a <;> cases b <;> simp_all [adjB]
  · -- Case 2: the two terminal lists are disjoint.
    have hdisj : Disjoint (L' V.s1) (L' V.s2) := by
      rw [disjoint_iff_inter_eq_empty]
      exact not_nonempty_iff_eq_empty.mp hcase
    let P : Fin 4 → Finset (C × C) := fun i =>
      (L' (V.u i) ∩ L' V.s1) ×ˢ (L' (V.u i) ∩ L' V.s2)
    have hPle : ∀ i : Fin 4, (P i).card ≤ 2 := by
      intro i
      have hPcard : (P i).card =
          (L' (V.u i) ∩ L' V.s1).card * (L' (V.u i) ∩ L' V.s2).card := by
        simp [P, card_product]
      rw [hPcard]
      apply mul_le_two_of_add_le_three
      have hd : Disjoint (L' (V.u i) ∩ L' V.s1) (L' (V.u i) ∩ L' V.s2) :=
        hdisj.mono inter_subset_right inter_subset_right
      have hunion : ((L' (V.u i) ∩ L' V.s1) ∪ (L' (V.u i) ∩ L' V.s2)).card =
          (L' (V.u i) ∩ L' V.s1).card + (L' (V.u i) ∩ L' V.s2).card :=
        card_union_of_disjoint hd
      have hsub : ((L' (V.u i) ∩ L' V.s1) ∪ (L' (V.u i) ∩ L' V.s2)) ⊆ L' (V.u i) :=
        union_subset inter_subset_left inter_subset_left
      have h3 := card_le_card hsub
      rw [hL' (V.u i)] at h3
      omega
    have hUnion_le : ((univ : Finset (Fin 4)).biUnion P).card ≤ 8 := by
      calc ((univ : Finset (Fin 4)).biUnion P).card
          ≤ ∑ i : Fin 4, (P i).card := card_biUnion_le
        _ ≤ ∑ i : Fin 4, 2 := sum_le_sum (fun i _ => hPle i)
        _ = 8 := by simp
    have hQcard : (L' V.s1 ×ˢ L' V.s2).card = 9 := by
      rw [card_product, hL' V.s1, hL' V.s2]
    have hnotsub : ¬ (L' V.s1 ×ˢ L' V.s2) ⊆ (univ : Finset (Fin 4)).biUnion P := by
      intro hsub
      have h1 := card_le_card hsub
      omega
    obtain ⟨q, hqQ, hqR⟩ := not_subset.mp hnotsub
    have hq1 : q.1 ∈ L' V.s1 := (mem_product.mp hqQ).1
    have hq2 : q.2 ∈ L' V.s2 := (mem_product.mp hqQ).2
    have hqNot : ∀ i : Fin 4, ¬ (q.1 ∈ L' (V.u i) ∧ q.2 ∈ L' (V.u i)) := by
      intro i hcon
      exact hqR (mem_biUnion.mpr ⟨i, mem_univ _, by
        rw [mem_product]
        exact ⟨mem_inter.mpr ⟨hcon.1, hq1⟩, mem_inter.mpr ⟨hcon.2, hq2⟩⟩⟩)
    have htri : ∀ i : Fin 4, ∃ a b e : C,
        a ∈ L' (V.u i) \ {q.1, q.2} ∧ b ∈ L' (V.v i) \ {q.1, q.2} ∧
        e ∈ L' (V.p i) ∧ a ≠ b ∧ a ≠ e ∧ b ≠ e := by
      intro i
      have hv1 : 1 ≤ (L' (V.v i) \ {q.1, q.2}).card := by
        have h := card_sdiff_pair_ge (L' (V.v i)) q.1 q.2
        have h2 := hL' (V.v i)
        omega
      have hu2 : 2 ≤ (L' (V.u i) \ {q.1, q.2}).card := by
        have h := card_sdiff_pair_ge_of_not_and (L' (V.u i)) q.1 q.2 (hqNot i)
        have h2 := hL' (V.u i)
        omega
      obtain ⟨xv, hxv, xu, hxu, z, hz, h1, h2, h3⟩ :=
        exists_pairwise_distinct (A := L' (V.v i) \ {q.1, q.2})
          (B := L' (V.u i) \ {q.1, q.2}) (C := L' (V.p i)) hv1 hu2
          (by have h := hL' (V.p i); omega)
      exact ⟨xu, xv, z, hxu, hxv, hz, h1.symm, h3, h2⟩
    choose cu cv cp hcu hcv hcp hne1 hne2 hne3 using htri
    have hq_cu1 : ∀ i : Fin 4, q.1 ≠ cu i := fun i hh =>
      (mem_sdiff.mp (hcu i)).2 (by rw [mem_insert, mem_singleton]; exact Or.inl hh.symm)
    have hq_cu2 : ∀ i : Fin 4, q.2 ≠ cu i := fun i hh =>
      (mem_sdiff.mp (hcu i)).2 (by rw [mem_insert, mem_singleton]; exact Or.inr hh.symm)
    have hq_cv1 : ∀ i : Fin 4, q.1 ≠ cv i := fun i hh =>
      (mem_sdiff.mp (hcv i)).2 (by rw [mem_insert, mem_singleton]; exact Or.inl hh.symm)
    have hq_cv2 : ∀ i : Fin 4, q.2 ≠ cv i := fun i hh =>
      (mem_sdiff.mp (hcv i)).2 (by rw [mem_insert, mem_singleton]; exact Or.inr hh.symm)
    have hcv_cu : ∀ i : Fin 4, cv i ≠ cu i := fun i => (hne1 i).symm
    have hcp_cu : ∀ i : Fin 4, cp i ≠ cu i := fun i => (hne2 i).symm
    have hcp_cv : ∀ i : Fin 4, cp i ≠ cv i := fun i => (hne3 i).symm
    refine ⟨fun w => match w with
      | .s1 => q.1
      | .s2 => q.2
      | .u i => cu i
      | .v i => cv i
      | .p i => cp i, ?_, ?_⟩
    · intro w
      cases w with
      | s1 => exact hq1
      | s2 => exact hq2
      | u i => exact (mem_sdiff.mp (hcu i)).1
      | v i => exact (mem_sdiff.mp (hcv i)).1
      | p i => exact hcp i
    · intro a b hab
      cases a <;> cases b <;> simp_all [adjB]

end Proofs

/-- Noel's graph is 3-choosable. -/
theorem isListColorable_three : G.IsListColorable 3 := by
  intro C _ lists hlists
  choose L' hL'sub hL' using fun w => Finset.exists_subset_card_eq (hlists w)
  obtain ⟨c, hc, hadj⟩ := exists_coloring_of_card_eq_three L' hL'
  exact ⟨SimpleGraph.Coloring.mk c fun hab => hadj _ _ hab, fun w => hL'sub w (hc w)⟩

/-- Noel's graph is not 2-choosable: at most nine of its fourteen vertices can be coloured
from the 2-list assignment `L`. -/
theorem not_isListColorable_two : ¬ G.IsListColorable 2 := by
  intro h
  obtain ⟨color, hmem⟩ := h ℕ L fun w => (card_L w).ge
  have h9 := card_le_nine (S := Finset.univ) (c := color)
    ⟨fun w _ => hmem w, fun _ _ _ _ hab => color.valid hab⟩
  have h14 : (Finset.univ : Finset V).card = 14 := by decide
  omega

/-- Noel's graph has choice number `3`. -/
theorem isChoiceNumber_three : G.IsChoiceNumber 3 :=
  ⟨isListColorable_three, fun _ hr h => not_isListColorable_two (h.mono (by omega))⟩

/-- `λ_L ≤ 9` for Noel's 2-list assignment `L`. -/
theorem lambdaMax_L_le_nine : lambdaMax G L ≤ 9 :=
  lambdaMax_le fun _ _ h => card_le_nine h

/-- `λ_2 ≤ 9` for Noel's graph. -/
theorem lambdaMin_two_le_nine : lambdaMin G 2 ≤ 9 :=
  (lambdaMin_le_lambdaMax card_L).trans lambdaMax_L_le_nine

/-- `λ_3 = 14` for Noel's graph: every assignment of lists of size 3 colours all fourteen
vertices. -/
theorem lambdaMin_three : lambdaMin G 3 = 14 := by
  have hcard : Fintype.card V = 14 := by decide
  refine le_antisymm ?_ ?_
  · calc lambdaMin G 3 ≤ lambdaMax G (fun _ => Finset.range 3) :=
          lambdaMin_le_lambdaMax fun _ => Finset.card_range 3
      _ ≤ 14 := hcard ▸ lambdaMax_le_card G _
  · refine le_lambdaMin fun L' hL' => ?_
    obtain ⟨color, hmem⟩ := isListColorable_three ℕ L' fun w => (hL' w).ge
    have h := card_le_lambdaMax (G := G) (S := Finset.univ) (f := color)
      ⟨fun w _ => hmem w, fun _ _ _ _ hab => color.valid hab⟩
    rwa [Finset.card_univ, hcard] at h

end Noel

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
  have h := hconj Noel.V Noel.G 3 2 3 Noel.isChoiceNumber_three
    (by norm_num) (by norm_num) (by norm_num)
  have h2 : (lambdaMin Noel.G 2 : ℚ) ≤ 9 := by exact_mod_cast Noel.lambdaMin_two_le_nine
  have h3 : (lambdaMin Noel.G 3 : ℚ) = 14 := by exact_mod_cast Noel.lambdaMin_three
  rw [h3] at h
  push_cast at h
  linarith

end MathlibExt.GraphTheory.PartialListColoringWanted
