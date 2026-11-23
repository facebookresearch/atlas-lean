/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Kiezun
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.Moralization
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.FinCases

/-!
# Tests for the moralization criterion

Agreement of d-separation and moral-graph separation on the three-node
junctions: chain and fork are separated by the middle node on both
criteria; the collider is separated unconditioned and non-separated
given the collider, on both criteria.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset Convexity

variable {α : Type*}

/-! ### Small-DAG agreement checks (three-node junctions) -/

/-- The chain `0 → 1 → 2` parent sets. -/
def chainPaMor : (k : Fin 3) → Finset (Fin k)
  | ⟨0, _⟩ => ∅
  | ⟨1, _⟩ => {0}
  | ⟨2, _⟩ => {1}
  | ⟨_ + 3, h⟩ => absurd h (by omega)

/-- The fork `1 ← 0 → 2` parent sets. -/
def forkPaMor : (k : Fin 3) → Finset (Fin k)
  | ⟨0, _⟩ => ∅
  | ⟨1, _⟩ => {0}
  | ⟨2, _⟩ => {0}
  | ⟨_ + 3, h⟩ => absurd h (by omega)

/-- The collider `0 → 2 ← 1` parent sets. -/
def colliderPaMor : (k : Fin 3) → Finset (Fin k)
  | ⟨0, _⟩ => ∅
  | ⟨1, _⟩ => ∅
  | ⟨2, _⟩ => {0, 1}
  | ⟨_ + 3, h⟩ => absurd h (by omega)

/-- Singletons of distinct vertices are disjoint. -/
private theorem disjoint_singleton_of_ne {n : ℕ} {a b : Fin n} (h : a ≠ b) :
    Disjoint ({a} : Set (Fin n)) {b} :=
  Set.disjoint_left.mpr (fun x hx => by
    have hxa : x = a := Set.mem_singleton_iff.mp hx
    subst hxa
    simp only [Set.mem_singleton_iff]
    exact h)

/-- Chain check: both criteria separate `0` from `2` given `1`, all tables. -/
theorem chain_moral_agreement
    (cpt : (k : Fin 3) → (chainPaMor k → α) → StdSimplex ℝ α) :
    (BayesNet.mk chainPaMor cpt).DSeparated {0} {2} {1} ∧
      ((BayesNet.mk chainPaMor cpt).moralGraph
        ((BayesNet.mk chainPaMor cpt).ancestorsOf ({0} ∪ {2} ∪ {1}))).SeparatedBy
        {0} {2} {1} := by
  have edge_iff (i j : Fin 3) : (BayesNet.mk chainPaMor cpt).Edge i j ↔
      (∃ h : i.val < j.val, (⟨i.val, h⟩ : Fin j) ∈ chainPaMor j) := Iff.rfl
  have hsep : ((BayesNet.mk chainPaMor cpt).moralGraph
      ((BayesNet.mk chainPaMor cpt).ancestorsOf ({0} ∪ {2} ∪ {1}))).SeparatedBy
      {0} {2} {1} := by
    intro a b_ ha hb w
    revert ha hb
    induction w with
    | @nil u =>
        intro ha hb
        have ha0 : u = 0 := Set.mem_singleton_iff.mp ha
        subst ha0
        simp at hb
    | @cons u v w_ h rest ih =>
        intro ha hb
        have hu0 : u = 0 := Set.mem_singleton_iff.mp ha
        subst hu0
        have hv1 : v = 1 := by
          rw [BayesNet.moralGraph_adj] at h
          obtain ⟨hne, h0A, hvA, hsk | hmar⟩ := h
          · fin_cases v
            · exact absurd hsk (by simp only [BayesNet.Adj, edge_iff]; decide)
            · rfl
            · exact absurd hsk (by simp only [BayesNet.Adj, edge_iff]; decide)
          · obtain ⟨c, hcA, e0c, evc⟩ := hmar
            fin_cases c
            · exact absurd e0c (by rw [edge_iff]; decide)
            · fin_cases v
              · exact absurd rfl hne
              · exact absurd evc (by rw [edge_iff]; decide)
              · exact absurd evc (by rw [edge_iff]; decide)
            · exact absurd e0c (by rw [edge_iff]; decide)
        refine ⟨1, by simp, ?_⟩
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem 0 (by subst hv1; exact rest.start_mem_support)
  have hXY : Disjoint ({0} : Set (Fin 3)) {2} :=
    disjoint_singleton_of_ne (by decide : (0 : Fin 3) ≠ 2)
  have hXZ : Disjoint ({0} : Set (Fin 3)) {1} :=
    disjoint_singleton_of_ne (by decide : (0 : Fin 3) ≠ 1)
  have hYZ : Disjoint ({2} : Set (Fin 3)) {1} :=
    disjoint_singleton_of_ne (by decide : (2 : Fin 3) ≠ 1)
  have hdsep :=
    (BayesNet.mk chainPaMor cpt).dSeparated_of_separatedBy_moralGraph hXY hXZ
      hYZ hsep
  exact ⟨hdsep, hsep⟩

/-- Fork check: both criteria separate `1` from `2` given `0`, all tables. -/
theorem fork_moral_agreement
    (cpt : (k : Fin 3) → (forkPaMor k → α) → StdSimplex ℝ α) :
    (BayesNet.mk forkPaMor cpt).DSeparated {1} {2} {0} ∧
      ((BayesNet.mk forkPaMor cpt).moralGraph
        ((BayesNet.mk forkPaMor cpt).ancestorsOf ({1} ∪ {2} ∪ {0}))).SeparatedBy
        {1} {2} {0} := by
  have edge_iff (i j : Fin 3) : (BayesNet.mk forkPaMor cpt).Edge i j ↔
      (∃ h : i.val < j.val, (⟨i.val, h⟩ : Fin j) ∈ forkPaMor j) := Iff.rfl
  have hsep : ((BayesNet.mk forkPaMor cpt).moralGraph
      ((BayesNet.mk forkPaMor cpt).ancestorsOf ({1} ∪ {2} ∪ {0}))).SeparatedBy
      {1} {2} {0} := by
    intro a b_ ha hb w
    revert ha hb
    induction w with
    | @nil u =>
        intro ha hb
        have ha1 : u = 1 := Set.mem_singleton_iff.mp ha
        subst ha1
        simp at hb
    | @cons u v w_ h rest ih =>
        intro ha hb
        have hu1 : u = 1 := Set.mem_singleton_iff.mp ha
        subst hu1
        have hv0 : v = 0 := by
          rw [BayesNet.moralGraph_adj] at h
          obtain ⟨hne, h1A, hvA, hsk | hmar⟩ := h
          · fin_cases v
            · rfl
            · exact absurd hsk (by simp only [BayesNet.Adj, edge_iff]; decide)
            · exact absurd hsk (by simp only [BayesNet.Adj, edge_iff]; decide)
          · obtain ⟨c, hcA, e1c, evc⟩ := hmar
            fin_cases c
            · exact absurd e1c (by rw [edge_iff]; decide)
            · exact absurd e1c (by rw [edge_iff]; decide)
            · exact absurd e1c (by rw [edge_iff]; decide)
        refine ⟨0, by simp, ?_⟩
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem 1 (by subst hv0; exact rest.start_mem_support)
  have hXY : Disjoint ({1} : Set (Fin 3)) {2} :=
    disjoint_singleton_of_ne (by decide : (1 : Fin 3) ≠ 2)
  have hXZ : Disjoint ({1} : Set (Fin 3)) {0} :=
    disjoint_singleton_of_ne (by decide : (1 : Fin 3) ≠ 0)
  have hYZ : Disjoint ({2} : Set (Fin 3)) {0} :=
    disjoint_singleton_of_ne (by decide : (2 : Fin 3) ≠ 0)
  have hdsep :=
    (BayesNet.mk forkPaMor cpt).dSeparated_of_separatedBy_moralGraph hXY hXZ hYZ
      hsep
  exact ⟨hdsep, hsep⟩

/-- Collider check, unconditioned: both criteria separate `0` from `1`. -/
theorem collider_moral_agreement_empty
    (cpt : (k : Fin 3) → (colliderPaMor k → α) → StdSimplex ℝ α) :
    (BayesNet.mk colliderPaMor cpt).DSeparated {0} {1} ∅ ∧
      ((BayesNet.mk colliderPaMor cpt).moralGraph
        ((BayesNet.mk colliderPaMor cpt).ancestorsOf ({0} ∪ {1} ∪ ∅))).SeparatedBy
        {0} {1} ∅ := by
  have edge_iff (i j : Fin 3) : (BayesNet.mk colliderPaMor cpt).Edge i j ↔
      (∃ h : i.val < j.val, (⟨i.val, h⟩ : Fin j) ∈ colliderPaMor j) := Iff.rfl
  have no_out_2 : ∀ c : Fin 3, ¬ (BayesNet.mk colliderPaMor cpt).Edge 2 c := by
    intro c
    fin_cases c <;> (rw [edge_iff]; decide)
  have rtc2_eq : ∀ s : Fin 3,
      Relation.ReflTransGen (BayesNet.mk colliderPaMor cpt).Edge 2 s → s = 2 := by
    intro s hrtc
    induction hrtc with
    | refl => rfl
    | tail h1 h2 ih =>
        rw [ih] at h2
        exact absurd h2 (no_out_2 _)
  have h2notA : (2 : Fin 3) ∉ (BayesNet.mk colliderPaMor cpt).ancestorsOf
      ({0} ∪ {1} ∪ ∅) := by
    intro h2A
    obtain ⟨s, hs, hrtc⟩ := h2A
    have hs2 : s = 2 := rtc2_eq s hrtc
    subst hs2
    simp at hs
  have hsep : ((BayesNet.mk colliderPaMor cpt).moralGraph
      ((BayesNet.mk colliderPaMor cpt).ancestorsOf ({0} ∪ {1} ∪ ∅))).SeparatedBy
      {0} {1} ∅ := by
    intro a b_ ha hb w
    revert ha hb
    induction w with
    | @nil u =>
        intro ha hb
        have ha0 : u = 0 := Set.mem_singleton_iff.mp ha
        subst ha0
        simp at hb
    | @cons u v w_ h rest ih =>
        intro ha hb
        have hu0 : u = 0 := Set.mem_singleton_iff.mp ha
        subst hu0
        rw [BayesNet.moralGraph_adj] at h
        obtain ⟨hne, h0A, hvA, hsk | hmar⟩ := h
        · fin_cases v
          · exact absurd hsk (by simp only [BayesNet.Adj, edge_iff]; decide)
          · exact absurd hsk (by simp only [BayesNet.Adj, edge_iff]; decide)
          · exact absurd hvA h2notA
        · obtain ⟨c, hcA, e0c, evc⟩ := hmar
          fin_cases c
          · exact absurd e0c (by rw [edge_iff]; decide)
          · exact absurd e0c (by rw [edge_iff]; decide)
          · exact absurd hcA h2notA
  have hXY : Disjoint ({0} : Set (Fin 3)) {1} :=
    disjoint_singleton_of_ne (by decide : (0 : Fin 3) ≠ 1)
  have hXZ : Disjoint ({0} : Set (Fin 3)) ∅ :=
    Set.disjoint_left.mpr (fun x hx => by simp)
  have hYZ : Disjoint ({1} : Set (Fin 3)) ∅ :=
    Set.disjoint_left.mpr (fun x hx => by simp)
  have hdsep :=
    (BayesNet.mk colliderPaMor cpt).dSeparated_of_separatedBy_moralGraph hXY
      hXZ hYZ hsep
  exact ⟨hdsep, hsep⟩

/-- Collider check, conditioned on the collider: both criteria fail to
separate `0` from `1` given `2` (the moral edge `0—1` appears exactly
because `2 ∈ an({0,1,2})`). -/
theorem collider_moral_agreement_given
    (cpt : (k : Fin 3) → (colliderPaMor k → α) → StdSimplex ℝ α) :
    ¬ (BayesNet.mk colliderPaMor cpt).DSeparated {0} {1} {2} ∧
      ¬ ((BayesNet.mk colliderPaMor cpt).moralGraph
        ((BayesNet.mk colliderPaMor cpt).ancestorsOf ({0} ∪ {1} ∪ {2}))).SeparatedBy
        {0} {1} {2} := by
  have edge_iff (i j : Fin 3) : (BayesNet.mk colliderPaMor cpt).Edge i j ↔
      (∃ h : i.val < j.val, (⟨i.val, h⟩ : Fin j) ∈ colliderPaMor j) := Iff.rfl
  have hnd : ¬ (BayesNet.mk colliderPaMor cpt).DSeparated {0} {1} {2} := by
    intro hdis
    have hmem0 : (0 : Fin 3) ∈ ({0} : Set (Fin 3)) := by simp
    have hmem1 : (1 : Fin 3) ∈ ({1} : Set (Fin 3)) := by simp
    have hch : List.IsChain (BayesNet.mk colliderPaMor cpt).Adj [0, 2, 1] := by
      rw [List.isChain_iff_getElem]
      intro i hi
      simp at hi
      have hi2 : i < 2 := by omega
      interval_cases i
      · show (BayesNet.mk colliderPaMor cpt).Adj 0 2
        simp only [BayesNet.Adj, edge_iff]
        decide
      · show (BayesNet.mk colliderPaMor cpt).Adj 2 1
        simp only [BayesNet.Adj, edge_iff]
        decide
    have hpath : (BayesNet.mk colliderPaMor cpt).IsPath 0 1 [0, 2, 1] :=
      ⟨by decide, hch, rfl, rfl⟩
    have hblk := hdis 0 hmem0 1 hmem1 [0, 2, 1] hpath
    obtain ⟨i, hi, hb⟩ := hblk
    simp at hi
    have hi0 : i = 0 := by omega
    simp only [hi0] at hb
    have e02 : (BayesNet.mk colliderPaMor cpt).Edge 0 2 := by
      rw [edge_iff]; decide
    have e12 : (BayesNet.mk colliderPaMor cpt).Edge 1 2 := by
      rw [edge_iff]; decide
    simp only [BayesNet.BlockedAt] at hb
    rcases hb with ⟨_, _, hno⟩ | ⟨hncoll, _⟩
    · exact hno 2 Relation.ReflTransGen.refl (by simp)
    · exact hncoll ⟨e02, e12⟩
  have hns : ¬ ((BayesNet.mk colliderPaMor cpt).moralGraph
      ((BayesNet.mk colliderPaMor cpt).ancestorsOf ({0} ∪ {1} ∪ {2}))).SeparatedBy
      {0} {1} {2} := by
    intro hsep
    have hXY : Disjoint ({0} : Set (Fin 3)) {1} :=
      disjoint_singleton_of_ne (by decide : (0 : Fin 3) ≠ 1)
    have hXZ : Disjoint ({0} : Set (Fin 3)) {2} :=
      disjoint_singleton_of_ne (by decide : (0 : Fin 3) ≠ 2)
    have hYZ : Disjoint ({1} : Set (Fin 3)) {2} :=
      disjoint_singleton_of_ne (by decide : (1 : Fin 3) ≠ 2)
    have hdsep :=
      (BayesNet.mk colliderPaMor cpt).dSeparated_of_separatedBy_moralGraph hXY
        hXZ hYZ hsep
    exact hnd hdsep
  exact ⟨hnd, hns⟩

end Cslib.MachineLearning.GraphicalModels
