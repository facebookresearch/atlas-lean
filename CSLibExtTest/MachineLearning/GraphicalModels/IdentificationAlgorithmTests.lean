/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Kiezun
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.IdentificationAlgorithm
import Mathlib.Tactic.FinCases

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels.ADMG

variable {V : Type*} [Fintype V] [DecidableEq V] (G : ADMG V)
  (σ : V ≃ Fin (Fintype.card V))  -- π, "some topological ordering of nodes in G"; the recursion
  -- is defined for every ordering, and identifies under a topological one (module doc)

/-- Fig. 1(a) directed edges strictly increase the vertex number. -/
theorem figDirA_edge {u w : Fin 3}
    (h : (u, w) = (0, 1) ∨ (u, w) = (1, 2)) : u.val < w.val := by
  rcases h with h | h <;> rw [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;> decide

/-- Transitive closure of the Fig. 1(a) edges strictly increases the vertex number. -/
theorem figTransGenA {u w : Fin 3}
    (h : Relation.TransGen (fun u w : Fin 3 => (u, w) = (0, 1) ∨ (u, w) = (1, 2)) u w) :
    u.val < w.val := by
  induction h with
  | single hd => exact figDirA_edge hd
  | tail _ hd ih => have h2 := figDirA_edge hd; omega

/-- Fig. 1(b) directed edges target `1` from elsewhere. -/
theorem figDirB_edge {u w : Fin 3}
    (h : (u, w) = (0, 1) ∨ (u, w) = (2, 1)) : w = 1 ∧ u ≠ 1 := by
  rcases h with h | h <;> rw [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    exact ⟨rfl, by decide⟩

/-- Transitive closure of the Fig. 1(b) edges targets `1` from elsewhere. -/
theorem figTransGenB {u w : Fin 3}
    (h : Relation.TransGen (fun u w : Fin 3 => (u, w) = (0, 1) ∨ (u, w) = (2, 1)) u w) :
    w = 1 ∧ u ≠ 1 := by
  induction h with
  | single hd => exact figDirB_edge hd
  | tail _ hd ih =>
    obtain ⟨hb, -⟩ := ih
    obtain ⟨-, hb'⟩ := figDirB_edge hd
    exact absurd hb hb'

/-- Reflexive-transitive closure of the Fig. 1(a) edges never decreases the vertex number. -/
theorem figReflTransGenA_le {u w : Fin 3}
    (h : Relation.ReflTransGen
      (fun u w : Fin 3 => (u, w) = (0, 1) ∨ (u, w) = (1, 2)) u w) :
    u.val ≤ w.val := by
  induction h with
  | refl => exact le_refl _
  | tail _ hd ih => have h2 := figDirA_edge hd; omega

/-- Only `2` reaches `2` along the Fig. 1(b) directed edges. -/
theorem figReflTransGenB_eq {u w : Fin 3}
    (h : Relation.ReflTransGen
      (fun u w : Fin 3 => (u, w) = (0, 1) ∨ (u, w) = (2, 1)) u w) :
    w = 2 → u = 2 := by
  induction h with
  | refl => exact fun h => h
  | tail _ hd ih =>
    intro hw2
    rw [hw2] at hd
    rcases hd with hd | hd <;> rw [Prod.mk.injEq] at hd <;> exact absurd hd.2 (by decide)

/-- The Fig. 1 bidirected edge only joins `0` and `1`. -/
theorem figBidir_adj {a b : Fin 3}
    (h : (SimpleGraph.fromRel (fun u w : Fin 3 => (u, w) = (0, 1))).Adj a b) :
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  rw [SimpleGraph.fromRel_adj] at h
  obtain ⟨-, h | h⟩ := h
  · left; rw [Prod.mk.injEq] at h; exact h
  · right; rw [Prod.mk.injEq] at h; exact ⟨h.2, h.1⟩

/-- Induced-subgraph directed edges live inside the set and come from the host graph. -/
theorem figInduceDir {G : ADMG (Fin 3)} {D : Finset (Fin 3)} {a b : Fin 3}
    (h : (G.induce ↑D).dir a b) : a ∈ (↑D : Set (Fin 3)) ∧ b ∈ ↑D ∧ G.dir a b := h

/-- Induced-subgraph bidirected edges of a Fig. 1 graph live inside the set and join
`0` with `1`. -/
theorem figInduceBidir_adj {G : ADMG (Fin 3)}
    (hb : G.bidir = SimpleGraph.fromRel (fun u w : Fin 3 => (u, w) = (0, 1)))
    {D : Finset (Fin 3)} {a b : Fin 3}
    (h : (SimpleGraph.fromRel
      (fun x y : Fin 3 => x ∈ (↑D : Set (Fin 3)) ∧ y ∈ ↑D ∧ G.bidir.Adj x y)).Adj a b) :
    a ∈ (↑D : Set (Fin 3)) ∧ b ∈ ↑D ∧ ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) := by
  rw [SimpleGraph.fromRel_adj, hb] at h
  obtain ⟨-, h | h⟩ := h
  · obtain ⟨ham, hbm, hadj⟩ := h
    exact ⟨ham, hbm, figBidir_adj hadj⟩
  · obtain ⟨hbm, ham, hadj⟩ := h
    obtain h | h := figBidir_adj hadj
    · exact ⟨ham, hbm, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨ham, hbm, Or.inl ⟨h.2, h.1⟩⟩

/-- Membership in `ancIn`, through the classical filter. -/
theorem figAncIn_mem (D Y : Finset V) (x : V) :
    x ∈ G.ancIn D Y ↔ x ∈ D ∧ ∃ y ∈ Y, Relation.ReflTransGen (G.induce ↑D).dir x y := by
  classical
  unfold ancIn
  rw [Finset.mem_filter]

/-- Membership in `ancCut`, through the classical filter. -/
theorem figAncCut_mem (D X Y : Finset V) (x : V) :
    x ∈ G.ancCut D X Y ↔ x ∈ D ∧ ∃ y ∈ Y, Relation.ReflTransGen
      (fun a b => (G.induce ↑D).dir a b ∧ b ∉ X) x y := by
  classical
  unfold ancCut
  rw [Finset.mem_filter]

/-- Membership in `compIn`, through the classical filter. -/
theorem figCompIn_mem (D : Finset V) (v x : V) :
    x ∈ G.compIn D v ↔ x ∈ D ∧ x ∈ (G.induce ↑D).cComponent v := by
  classical
  unfold compIn
  rw [Finset.mem_filter]

/-- Test graph Fig. 1(a): X -> Z -> Y with X <-> Z, on Fin 3 with 0 = X, 1 = Z,
2 = Y. -/
def fig1a : ADMG (Fin 3) where
  dir u w := (u, w) = (0, 1) ∨ (u, w) = (1, 2)
  bidir := SimpleGraph.fromRel fun u w => (u, w) = (0, 1)
  acyclic := by
    show ∀ v : Fin 3,
      ¬ Relation.TransGen (fun u w : Fin 3 => (u, w) = (0, 1) ∨ (u, w) = (1, 2)) v v
    intro v h
    exact absurd (figTransGenA h) (lt_irrefl _)

/-- Test graph Fig. 1(b): X -> Z <- Y with X <-> Z, on Fin 3 with 0 = X, 1 = Z,
2 = Y. -/
def fig1b : ADMG (Fin 3) where
  dir u w := (u, w) = (0, 1) ∨ (u, w) = (2, 1)
  bidir := SimpleGraph.fromRel fun u w => (u, w) = (0, 1)
  acyclic := by
    show ∀ v : Fin 3,
      ¬ Relation.TransGen (fun u w : Fin 3 => (u, w) = (0, 1) ∨ (u, w) = (2, 1)) v v
    intro v h
    obtain ⟨hv, hne⟩ := figTransGenB h
    exact hne hv

/-- The identity ordering on `Fin 3` (`0 = X`, `1 = Z`, `2 = Y`), passed to `ID` as its
ordering parameter. -/
def fig1order : Fin 3 ≃ Fin 3 := Equiv.refl _

theorem fig1a_fail : fig1a.ID fig1order {2} {0} = .error ({0, 1}, {1}) := by
  have hA1 : fig1a.ancIn Finset.univ {2} = Finset.univ := by
    ext x
    rw [figAncIn_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    have h01 : (0 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧ (1 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧
        fig1a.dir 0 1 := by
      refine ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩
      show ((0, 1) : Fin 3 × Fin 3) = (0, 1) ∨ (0, 1) = (1, 2)
      exact Or.inl rfl
    have h12 : (1 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧ (2 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧
        fig1a.dir 1 2 := by
      refine ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩
      show ((1, 2) : Fin 3 × Fin 3) = (0, 1) ∨ (1, 2) = (1, 2)
      exact Or.inr rfl
    rcases hx3 with rfl | rfl | rfl
    · constructor
      · intro h; exact h.1
      · intro _
        refine ⟨Finset.mem_univ _, 2, by decide, ?_⟩
        exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single h01)
          (Relation.ReflTransGen.single h12)
    · constructor
      · intro h; exact h.1
      · intro _
        refine ⟨Finset.mem_univ _, 2, by decide, ?_⟩
        exact Relation.ReflTransGen.single h12
    · constructor
      · intro h; exact h.1
      · intro _
        refine ⟨Finset.mem_univ _, 2, by decide, ?_⟩
        exact Relation.ReflTransGen.refl
  have hA2 : fig1a.ancCut Finset.univ {0} {2} = Finset.univ := by
    ext x
    rw [figAncCut_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    have h01 : (fig1a.induce ↑(Finset.univ : Finset (Fin 3))).dir 0 1 ∧ (1 : Fin 3) ∉ ({0} : Finset (Fin 3)) := by
      refine ⟨?_, by decide⟩
      show (0 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧ (1 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧
        fig1a.dir 0 1
      refine ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩
      show ((0, 1) : Fin 3 × Fin 3) = (0, 1) ∨ (0, 1) = (1, 2)
      exact Or.inl rfl
    have h12 : (fig1a.induce ↑(Finset.univ : Finset (Fin 3))).dir 1 2 ∧ (2 : Fin 3) ∉ ({0} : Finset (Fin 3)) := by
      refine ⟨?_, by decide⟩
      show (1 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧ (2 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧
        fig1a.dir 1 2
      refine ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩
      show ((1, 2) : Fin 3 × Fin 3) = (0, 1) ∨ (1, 2) = (1, 2)
      exact Or.inr rfl
    rcases hx3 with rfl | rfl | rfl
    · constructor
      · intro h; exact h.1
      · intro _
        refine ⟨Finset.mem_univ _, 2, by decide, ?_⟩
        exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single h01)
          (Relation.ReflTransGen.single h12)
    · constructor
      · intro h; exact h.1
      · intro _
        refine ⟨Finset.mem_univ _, 2, by decide, ?_⟩
        exact Relation.ReflTransGen.single h12
    · constructor
      · intro h; exact h.1
      · intro _
        refine ⟨Finset.mem_univ _, 2, by decide, ?_⟩
        exact Relation.ReflTransGen.refl
  have hA4 : fig1a.ancIn Finset.univ {1} = {0, 1} := by
    ext x
    rw [figAncIn_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    have hle : (fig1a.induce ↑(Finset.univ : Finset (Fin 3))).dir ≤
        (fun u w : Fin 3 => (u, w) = (0, 1) ∨ (u, w) = (1, 2)) := by
      intro a b hab
      exact (figInduceDir hab).2.2
    have h01 : (0 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧ (1 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧
        fig1a.dir 0 1 := by
      refine ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩
      show ((0, 1) : Fin 3 × Fin 3) = (0, 1) ∨ (0, 1) = (1, 2)
      exact Or.inl rfl
    rcases hx3 with rfl | rfl | rfl
    · constructor
      · intro _; decide
      · intro _
        refine ⟨Finset.mem_univ _, 1, by decide, ?_⟩
        exact Relation.ReflTransGen.single h01
    · constructor
      · intro _; decide
      · intro _
        refine ⟨Finset.mem_univ _, 1, by decide, ?_⟩
        exact Relation.ReflTransGen.refl
    · constructor
      · rintro ⟨-, y, hy, hr⟩
        have hy1 : y = 1 := Finset.mem_singleton.mp hy
        subst hy1
        have hle' := figReflTransGenA_le ((Relation.ReflTransGen.mono hle) _ _ hr)
        exact absurd hle' (by decide)
      · intro hcon; exact absurd hcon (by decide)
  have hA5 : fig1a.ancIn {0, 1} {1} = {0, 1} := by
    ext x
    rw [figAncIn_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    have h01 : (0 : Fin 3) ∈ (↑(({0, 1} : Finset (Fin 3))) : Set (Fin 3)) ∧
        (1 : Fin 3) ∈ (↑(({0, 1} : Finset (Fin 3))) : Set (Fin 3)) ∧ fig1a.dir 0 1 := by
      refine ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩
      show ((0, 1) : Fin 3 × Fin 3) = (0, 1) ∨ (0, 1) = (1, 2)
      exact Or.inl rfl
    rcases hx3 with rfl | rfl | rfl
    · constructor
      · intro h; exact h.1
      · intro _
        refine ⟨by decide, 1, by decide, ?_⟩
        exact Relation.ReflTransGen.single h01
    · constructor
      · intro h; exact h.1
      · intro _
        refine ⟨by decide, 1, by decide, ?_⟩
        exact Relation.ReflTransGen.refl
    · constructor
      · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
      · intro hcon; exact absurd hcon (by decide)
  have hA6 : fig1a.ancCut {0, 1} {0} {1} = {0, 1} := by
    ext x
    rw [figAncCut_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    have h01 : (fig1a.induce ↑(({0, 1} : Finset (Fin 3)))).dir 0 1 ∧
        (1 : Fin 3) ∉ ({0} : Finset (Fin 3)) := by
      refine ⟨?_, by decide⟩
      show (0 : Fin 3) ∈ (↑(({0, 1} : Finset (Fin 3))) : Set (Fin 3)) ∧
        (1 : Fin 3) ∈ (↑(({0, 1} : Finset (Fin 3))) : Set (Fin 3)) ∧ fig1a.dir 0 1
      refine ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩
      show ((0, 1) : Fin 3 × Fin 3) = (0, 1) ∨ (0, 1) = (1, 2)
      exact Or.inl rfl
    rcases hx3 with rfl | rfl | rfl
    · constructor
      · intro h; exact h.1
      · intro _
        refine ⟨by decide, 1, by decide, ?_⟩
        exact Relation.ReflTransGen.single h01
    · constructor
      · intro h; exact h.1
      · intro _
        refine ⟨by decide, 1, by decide, ?_⟩
        exact Relation.ReflTransGen.refl
    · constructor
      · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
      · intro hcon; exact absurd hcon (by decide)
  have hreach1 : ∀ {w : Fin 3},
      (fig1a.induce ↑(({1, 2} : Finset (Fin 3)))).bidir.Reachable 1 w → w = 1 := by
    intro w h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => rfl
    | tail _ hstep ih =>
      rw [ih] at hstep
      obtain ⟨-, hmem, h | h⟩ := figInduceBidir_adj (G := fig1a) rfl hstep
      · exact absurd h.1 (by decide)
      · have h0mem : (0 : Fin 3) ∈ (({1, 2} : Finset (Fin 3))) := by
          rw [← h.2]; exact Finset.mem_coe.mp hmem
        exact absurd h0mem (by decide)
  have hC11 : fig1a.compIn {1, 2} 1 = {1} := by
    ext x
    rw [figCompIn_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    rcases hx3 with rfl | rfl | rfl
    · constructor
      · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
      · intro hcon; exact absurd hcon (by decide)
    · constructor
      · intro _; decide
      · intro _
        refine ⟨by decide, ?_⟩
        unfold ADMG.cComponent
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
    · constructor
      · rintro ⟨-, hr⟩
        rw [(fig1a.induce ↑(({1, 2} : Finset (Fin 3)))).mem_cComponent_iff] at hr
        have h21 := hreach1 hr
        rw [h21]
        decide
      · intro hcon; exact absurd hcon (by decide)
  have hreach2 : ∀ {w : Fin 3},
      (fig1a.induce ↑(({1, 2} : Finset (Fin 3)))).bidir.Reachable 2 w → w = 2 := by
    intro w h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => rfl
    | tail _ hstep ih =>
      rw [ih] at hstep
      obtain ⟨-, -, h | h⟩ := figInduceBidir_adj (G := fig1a) rfl hstep
      · exact absurd h.1 (by decide)
      · exact absurd h.1 (by decide)
  have hC12 : fig1a.compIn {1, 2} 2 = {2} := by
    ext x
    rw [figCompIn_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    rcases hx3 with rfl | rfl | rfl
    · constructor
      · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
      · intro hcon; exact absurd hcon (by decide)
    · constructor
      · rintro ⟨-, hr⟩
        rw [(fig1a.induce ↑(({1, 2} : Finset (Fin 3)))).mem_cComponent_iff] at hr
        have h12 := hreach2 hr
        rw [h12]
        decide
      · intro hcon; exact absurd hcon (by decide)
    · constructor
      · intro _; decide
      · intro _
        refine ⟨by decide, ?_⟩
        unfold ADMG.cComponent
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  have hC3 : fig1a.cComponentsIn {1, 2} = {{1}, {2}} := by
    unfold cComponentsIn
    rw [Finset.image_insert, Finset.image_singleton, hC11, hC12]
  have hC1 : fig1a.compIn {1} 1 = {1} := by
    ext x
    rw [figCompIn_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    rcases hx3 with rfl | rfl | rfl
    · constructor
      · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
      · intro hcon; exact absurd hcon (by decide)
    · constructor
      · intro _; decide
      · intro _
        refine ⟨by decide, ?_⟩
        unfold ADMG.cComponent
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
    · constructor
      · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
      · intro hcon; exact absurd hcon (by decide)
  have hA7 : fig1a.cComponentsIn {1} = {{1}} := by
    unfold cComponentsIn
    rw [Finset.image_singleton, hC1]
  have hC2 : fig1a.compIn {2} 2 = {2} := by
    ext x
    rw [figCompIn_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    rcases hx3 with rfl | rfl | rfl
    · constructor
      · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
      · intro hcon; exact absurd hcon (by decide)
    · constructor
      · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
      · intro hcon; exact absurd hcon (by decide)
    · constructor
      · intro _; decide
      · intro _
        refine ⟨by decide, ?_⟩
        unfold ADMG.cComponent
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  have hA10 : fig1a.cComponentsIn {2} = {{2}} := by
    unfold cComponentsIn
    rw [Finset.image_singleton, hC2]
  have hadj01 : (SimpleGraph.fromRel
        (fun x y : Fin 3 => x ∈ (↑(({0, 1} : Finset (Fin 3))) : Set (Fin 3)) ∧ y ∈ (↑(({0, 1} : Finset (Fin 3))) : Set (Fin 3)) ∧
          fig1a.bidir.Adj x y)).Adj 0 1 := by
    rw [SimpleGraph.fromRel_adj]
    refine ⟨by decide,
      Or.inl ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩⟩
    have hb01 : (SimpleGraph.fromRel (fun u w : Fin 3 => (u, w) = (0, 1))).Adj 0 1 := by
      rw [SimpleGraph.fromRel_adj]
      exact ⟨by decide, Or.inl rfl⟩
    exact hb01
  have hadj10 : (SimpleGraph.fromRel
        (fun x y : Fin 3 => x ∈ (↑(({0, 1} : Finset (Fin 3))) : Set (Fin 3)) ∧ y ∈ (↑(({0, 1} : Finset (Fin 3))) : Set (Fin 3)) ∧
          fig1a.bidir.Adj x y)).Adj 1 0 := by
    rw [SimpleGraph.fromRel_adj]
    refine ⟨by decide,
      Or.inl ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩⟩
    have hb10 : (SimpleGraph.fromRel (fun u w : Fin 3 => (u, w) = (0, 1))).Adj 1 0 := by
      rw [SimpleGraph.fromRel_adj]
      exact ⟨by decide, Or.inr rfl⟩
    exact hb10
  have hc0 : fig1a.compIn {0, 1} 0 = {0, 1} := by
    ext x
    rw [figCompIn_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    rcases hx3 with rfl | rfl | rfl
    · constructor
      · intro _; decide
      · intro _
        refine ⟨by decide, ?_⟩
        unfold ADMG.cComponent
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
    · constructor
      · intro _; decide
      · intro _
        refine ⟨by decide, ?_⟩
        rw [(fig1a.induce ↑(({0, 1} : Finset (Fin 3)))).mem_cComponent_iff,
          SimpleGraph.reachable_iff_reflTransGen]
        exact Relation.ReflTransGen.single hadj01
    · constructor
      · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
      · intro hcon; exact absurd hcon (by decide)
  have hc1 : fig1a.compIn {0, 1} 1 = {0, 1} := by
    ext x
    rw [figCompIn_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    rcases hx3 with rfl | rfl | rfl
    · constructor
      · intro _; decide
      · intro _
        refine ⟨by decide, ?_⟩
        rw [(fig1a.induce ↑(({0, 1} : Finset (Fin 3)))).mem_cComponent_iff,
          SimpleGraph.reachable_iff_reflTransGen]
        exact Relation.ReflTransGen.single hadj10
    · constructor
      · intro _; decide
      · intro _
        refine ⟨by decide, ?_⟩
        unfold ADMG.cComponent
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
    · constructor
      · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
      · intro hcon; exact absurd hcon (by decide)
  have hA8 : fig1a.cComponentsIn {0, 1} = {{0, 1}} := by
    unfold cComponentsIn
    rw [Finset.image_insert, Finset.image_singleton, hc0, hc1]
    decide
  have hreachU0 : ∀ {w : Fin 3},
      (fig1a.induce ↑(({0, 1, 2} : Finset (Fin 3)))).bidir.Reachable 0 w → w = 0 ∨ w = 1 := by
    intro w h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact Or.inl rfl
    | tail _ hstep ih =>
      rcases ih with rfl | rfl
      · obtain ⟨-, -, h | h⟩ := figInduceBidir_adj (G := fig1a) rfl hstep
        · exact Or.inr h.2
        · exact absurd h.1 (by decide)
      · obtain ⟨-, -, h | h⟩ := figInduceBidir_adj (G := fig1a) rfl hstep
        · exact absurd h.1 (by decide)
        · exact Or.inl h.2
  have hreachU1 : ∀ {w : Fin 3},
      (fig1a.induce ↑(({0, 1, 2} : Finset (Fin 3)))).bidir.Reachable 1 w → w = 0 ∨ w = 1 := by
    intro w h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact Or.inr rfl
    | tail _ hstep ih =>
      rcases ih with rfl | rfl
      · obtain ⟨-, -, h | h⟩ := figInduceBidir_adj (G := fig1a) rfl hstep
        · exact Or.inr h.2
        · exact absurd h.1 (by decide)
      · obtain ⟨-, -, h | h⟩ := figInduceBidir_adj (G := fig1a) rfl hstep
        · exact absurd h.1 (by decide)
        · exact Or.inl h.2
  have hreachU2 : ∀ {w : Fin 3},
      (fig1a.induce ↑(({0, 1, 2} : Finset (Fin 3)))).bidir.Reachable 2 w → w = 2 := by
    intro w h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => rfl
    | tail _ hstep ih =>
      rw [ih] at hstep
      obtain ⟨-, -, h | h⟩ := figInduceBidir_adj (G := fig1a) rfl hstep
      · exact absurd h.1 (by decide)
      · exact absurd h.1 (by decide)
  have hu01 : (SimpleGraph.fromRel
        (fun x y : Fin 3 => x ∈ (↑(({0, 1, 2} : Finset (Fin 3))) : Set (Fin 3)) ∧
          y ∈ (↑(({0, 1, 2} : Finset (Fin 3))) : Set (Fin 3)) ∧ fig1a.bidir.Adj x y)).Adj 0 1 := by
    rw [SimpleGraph.fromRel_adj]
    refine ⟨by decide,
      Or.inl ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩⟩
    have hb01 : (SimpleGraph.fromRel (fun u w : Fin 3 => (u, w) = (0, 1))).Adj 0 1 := by
      rw [SimpleGraph.fromRel_adj]
      exact ⟨by decide, Or.inl rfl⟩
    exact hb01
  have hu10 : (SimpleGraph.fromRel
        (fun x y : Fin 3 => x ∈ (↑(({0, 1, 2} : Finset (Fin 3))) : Set (Fin 3)) ∧
          y ∈ (↑(({0, 1, 2} : Finset (Fin 3))) : Set (Fin 3)) ∧ fig1a.bidir.Adj x y)).Adj 1 0 := by
    rw [SimpleGraph.fromRel_adj]
    refine ⟨by decide,
      Or.inl ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩⟩
    have hb10 : (SimpleGraph.fromRel (fun u w : Fin 3 => (u, w) = (0, 1))).Adj 1 0 := by
      rw [SimpleGraph.fromRel_adj]
      exact ⟨by decide, Or.inr rfl⟩
    exact hb10
  have cu0 : fig1a.compIn {0, 1, 2} 0 = {0, 1} := by
    ext x
    rw [figCompIn_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    rcases hx3 with rfl | rfl | rfl
    · constructor
      · intro _; decide
      · intro _
        refine ⟨by decide, ?_⟩
        unfold ADMG.cComponent
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
    · constructor
      · intro _; decide
      · intro _
        refine ⟨by decide, ?_⟩
        rw [(fig1a.induce ↑(({0, 1, 2} : Finset (Fin 3)))).mem_cComponent_iff,
          SimpleGraph.reachable_iff_reflTransGen]
        exact Relation.ReflTransGen.single hu01
    · constructor
      · rintro ⟨-, hr⟩
        rw [(fig1a.induce ↑(({0, 1, 2} : Finset (Fin 3)))).mem_cComponent_iff] at hr
        rcases hreachU0 hr with h | h
        · rw [h]; decide
        · rw [h]; decide
      · intro hcon; exact absurd hcon (by decide)
  have cu1 : fig1a.compIn {0, 1, 2} 1 = {0, 1} := by
    ext x
    rw [figCompIn_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    rcases hx3 with rfl | rfl | rfl
    · constructor
      · intro _; decide
      · intro _
        refine ⟨by decide, ?_⟩
        rw [(fig1a.induce ↑(({0, 1, 2} : Finset (Fin 3)))).mem_cComponent_iff,
          SimpleGraph.reachable_iff_reflTransGen]
        exact Relation.ReflTransGen.single hu10
    · constructor
      · intro _; decide
      · intro _
        refine ⟨by decide, ?_⟩
        unfold ADMG.cComponent
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
    · constructor
      · rintro ⟨-, hr⟩
        rw [(fig1a.induce ↑(({0, 1, 2} : Finset (Fin 3)))).mem_cComponent_iff] at hr
        rcases hreachU1 hr with h | h
        · rw [h]; decide
        · rw [h]; decide
      · intro hcon; exact absurd hcon (by decide)
  have cu2 : fig1a.compIn {0, 1, 2} 2 = {2} := by
    ext x
    rw [figCompIn_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    rcases hx3 with rfl | rfl | rfl
    · constructor
      · rintro ⟨-, hr⟩
        rw [(fig1a.induce ↑(({0, 1, 2} : Finset (Fin 3)))).mem_cComponent_iff] at hr
        have h02 := hreachU2 hr
        rw [h02]; decide
      · intro hcon; exact absurd hcon (by decide)
    · constructor
      · rintro ⟨-, hr⟩
        rw [(fig1a.induce ↑(({0, 1, 2} : Finset (Fin 3)))).mem_cComponent_iff] at hr
        have h12 := hreachU2 hr
        rw [h12]; decide
      · intro hcon; exact absurd hcon (by decide)
    · constructor
      · intro _; decide
      · intro _
        refine ⟨by decide, ?_⟩
        unfold ADMG.cComponent
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  have hA11 : fig1a.cComponentsIn Finset.univ = {{0, 1}, {2}} := by
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} from by decide]
    unfold cComponentsIn
    rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton, cu0, cu1, cu2]
    decide
  have heqA := fun (Y X D : Finset (Fin 3)) (P : IdExpr (Fin 3)) =>
    idRec.eq_def fig1a fig1order Y X D P
  have hUX1 : (Finset.univ \ ({1} : Finset (Fin 3))) = {0, 2} := by decide
  have hcall1 : fig1a.idRec fig1order {1} (Finset.univ \ {1}) Finset.univ IdExpr.obs =
      .error (({0, 1} : Finset (Fin 3)), ({1} : Finset (Fin 3))) := by
    rw [hUX1, heqA]
    have h1ne : (({0, 2} : Finset (Fin 3))) ≠ ∅ := by decide
    rw [ite_eq_right h1ne]
    have h2yes : fig1a.ancIn Finset.univ {1} ≠ Finset.univ := by rw [hA4]; decide
    rw [dite_eq_left h2yes, hA4]
    have hcap : ((({0, 2} : Finset (Fin 3))) ∩ {0, 1}) = {0} := by decide
    have hsd : (Finset.univ \ (({0, 1} : Finset (Fin 3)))) = {2} := by decide
    rw [hcap, hsd, heqA]
    have h1ne' : (({0} : Finset (Fin 3))) ≠ ∅ := by decide
    rw [ite_eq_right h1ne']
    have h2no : ¬ (fig1a.ancIn {0, 1} {1} ≠ {0, 1}) := by rw [hA5]; decide
    rw [dite_eq_right h2no]
    have hDX3 : ((({0, 1} : Finset (Fin 3))) \ {0}) = {1} := by decide
    have h3no : ¬ (((({0, 1} : Finset (Fin 3)) \ {0}) \
        fig1a.ancCut {0, 1} {0} {1}).Nonempty) := by
      rw [hDX3, hA6]
      rw [show ((({1} : Finset (Fin 3))) \ {0, 1}) = ∅ from by decide]
      exact Finset.not_nonempty_empty
    rw [dite_eq_right h3no]
    have h4no : ¬ (((({0, 1} : Finset (Fin 3)) \ {0}) ∉
        fig1a.cComponentsIn ((({0, 1} : Finset (Fin 3))) \ {0}))) := by
      rw [hDX3, hA7]; decide
    rw [dite_eq_right h4no]
    have h5yes : ({0, 1} : Finset (Fin 3)) ∈ fig1a.cComponentsIn {0, 1} := by
      rw [hA8]; decide
    rw [dite_eq_left h5yes, hDX3]
  have hUX2 : (Finset.univ \ ({2} : Finset (Fin 3))) = {0, 1} := by decide
  have hcall2 : ∃ v,
      fig1a.idRec fig1order {2} (Finset.univ \ {2}) Finset.univ IdExpr.obs = .ok v := by
    rw [hUX2, heqA]
    have h1ne : (({0, 1} : Finset (Fin 3))) ≠ ∅ := by decide
    rw [ite_eq_right h1ne]
    have h2no : ¬ (fig1a.ancIn Finset.univ {2} ≠ Finset.univ) := by rw [hA1]; decide
    rw [dite_eq_right h2no]
    have hDX3 : (Finset.univ \ (({0, 1} : Finset (Fin 3)))) = {2} := by decide
    have h2mem : (2 : Fin 3) ∈ fig1a.ancCut Finset.univ {0, 1} {2} := by
      rw [figAncCut_mem]
      exact ⟨Finset.mem_univ _, 2, by decide, Relation.ReflTransGen.refl⟩
    have hempty : ((({2} : Finset (Fin 3))) \ fig1a.ancCut Finset.univ {0, 1} {2}) = ∅ := by
      ext x
      rw [Finset.mem_sdiff]
      constructor
      · rintro ⟨hx2, hxnin⟩
        rw [Finset.mem_singleton] at hx2
        subst hx2
        exact absurd h2mem hxnin
      · intro hcon
        simp at hcon
    have h3no : ¬ ((((Finset.univ : Finset (Fin 3)) \ {0, 1}) \
        fig1a.ancCut Finset.univ {0, 1} {2}).Nonempty) := by
      rw [hDX3, hempty]
      exact Finset.not_nonempty_empty
    rw [dite_eq_right h3no]
    have h4no : ¬ ((((Finset.univ : Finset (Fin 3)) \ {0, 1}) ∉
        fig1a.cComponentsIn ((Finset.univ : Finset (Fin 3)) \ {0, 1}))) := by
      rw [hDX3, hA10]; decide
    rw [dite_eq_right h4no]
    have h5no : ¬ ((Finset.univ : Finset (Fin 3)) ∈ fig1a.cComponentsIn Finset.univ) := by
      rw [hA11]; decide
    rw [dite_eq_right h5no]
    have h6yes : ((Finset.univ : Finset (Fin 3)) \ {0, 1}) ∈ fig1a.cComponentsIn Finset.univ := by
      rw [hDX3, hA11]; decide
    rw [ite_eq_left h6yes]
    exact ⟨_, rfl⟩
  have hDX : (Finset.univ \ (({0} : Finset (Fin 3)))) = {1, 2} := by decide
  have hmap : List.mapM
        (fun S : { S : Finset (Fin 3) // S ∈ (fig1a.cComponentsIn (Finset.univ \ {0})).toList } =>
          fig1a.idRec fig1order S.1 (Finset.univ \ S.1) Finset.univ IdExpr.obs)
        (fig1a.cComponentsIn (Finset.univ \ {0})).toList.attach =
      .error (({0, 1} : Finset (Fin 3)), ({1} : Finset (Fin 3))) := by
    rw [hDX, hC3]
    have hall : ∀ e ∈ ((({{1}, {2}} : Finset (Finset (Fin 3)))).toList.attach),
        ((e.1 : Finset (Fin 3)) = {1} ∨ (e.1 : Finset (Fin 3)) = {2}) := by
      intro e _
      have hmem : (e.1 : Finset (Fin 3)) ∈ (({{1}, {2}} : Finset (Finset (Fin 3)))).toList :=
        e.2
      rw [Finset.mem_toList, Finset.mem_insert, Finset.mem_singleton] at hmem
      exact hmem
    have hex : ∃ e ∈ ((({{1}, {2}} : Finset (Finset (Fin 3)))).toList.attach),
        ((e.1 : Finset (Fin 3)) = {1}) := by
      have h1mem : (({1} : Finset (Fin 3))) ∈
          (({{1}, {2}} : Finset (Finset (Fin 3)))).toList := by
        rw [Finset.mem_toList]
        decide
      exact ⟨⟨{1}, h1mem⟩, List.mem_attach _ _, rfl⟩
    have hind : ∀ (l : List
          { S : Finset (Fin 3) // S ∈ (({{1}, {2}} : Finset (Finset (Fin 3)))).toList }),
        (∀ e ∈ l, (e.1 : Finset (Fin 3)) = {1} ∨ (e.1 : Finset (Fin 3)) = {2}) →
        (∃ e ∈ l, (e.1 : Finset (Fin 3)) = {1}) →
        List.mapM
          (fun S : { S : Finset (Fin 3) //
            S ∈ (({{1}, {2}} : Finset (Finset (Fin 3)))).toList } =>
            fig1a.idRec fig1order S.1 (Finset.univ \ S.1) Finset.univ IdExpr.obs) l =
          .error (({0, 1} : Finset (Fin 3)), ({1} : Finset (Fin 3))) := by
      intro l
      induction l with
      | nil =>
        intro _ hex0
        obtain ⟨e, hmem, _⟩ := hex0
        exact absurd hmem (by simp)
      | cons a l ih =>
        intro hall0 hex0
        rcases hall0 a (by simp) with ha1 | ha2
        · have hfa : (fun S : { S : Finset (Fin 3) //
                S ∈ (({{1}, {2}} : Finset (Finset (Fin 3)))).toList } =>
              fig1a.idRec fig1order S.1 (Finset.univ \ S.1) Finset.univ IdExpr.obs) a =
              .error (({0, 1} : Finset (Fin 3)), ({1} : Finset (Fin 3))) := by
            show fig1a.idRec fig1order a.1 (Finset.univ \ a.1) Finset.univ IdExpr.obs = _
            rw [ha1]
            exact hcall1
          simp only [List.mapM_cons, hfa]
          rfl
        · have hfa : ∃ v, (fun S : { S : Finset (Fin 3) //
                S ∈ (({{1}, {2}} : Finset (Finset (Fin 3)))).toList } =>
              fig1a.idRec fig1order S.1 (Finset.univ \ S.1) Finset.univ IdExpr.obs) a = .ok v := by
            show ∃ v, fig1a.idRec fig1order a.1 (Finset.univ \ a.1) Finset.univ IdExpr.obs =
              .ok v
            rw [ha2]
            exact hcall2
          obtain ⟨v, hfa⟩ := hfa
          have hex0' : ∃ e ∈ l, (e.1 : Finset (Fin 3)) = {1} := by
            obtain ⟨e, hmem, he1⟩ := hex0
            rw [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · rw [ha2] at he1
              exact absurd he1 (by decide)
            · exact ⟨e, hmem, he1⟩
          have hall0' : ∀ e ∈ l,
              (e.1 : Finset (Fin 3)) = {1} ∨ (e.1 : Finset (Fin 3)) = {2} :=
            fun e h => hall0 e (List.mem_cons_of_mem _ h)
          simp only [List.mapM_cons, hfa, ih hall0' hex0']
          rfl
    exact hind _ hall hex
  have hXne : (({0} : Finset (Fin 3))) ≠ ∅ := by decide
  show fig1a.idRec fig1order {2} {0} Finset.univ IdExpr.obs = .error ({0, 1}, {1})
  rw [heqA, ite_eq_right hXne]
  have h2no : ¬ (fig1a.ancIn Finset.univ {2} ≠ Finset.univ) := by rw [hA1]; decide
  rw [dite_eq_right h2no]
  have h3no : ¬ ((((Finset.univ : Finset (Fin 3)) \ {0}) \
      fig1a.ancCut Finset.univ {0} {2}).Nonempty) := by
    rw [hDX, hA2]
    rw [show ((({1, 2} : Finset (Fin 3))) \ Finset.univ) = ∅ from by decide]
    exact Finset.not_nonempty_empty
  rw [dite_eq_right h3no]
  have h4yes : ((Finset.univ : Finset (Fin 3)) \ {0}) ∉
      fig1a.cComponentsIn (Finset.univ \ {0}) := by
    rw [hDX, hC3]; decide
  rw [dite_eq_left h4yes, hmap]
  rfl

theorem fig1b_ok : fig1b.ID fig1order {2} {0} = .ok (.sum ∅ (.sum {0, 1} .obs)) := by
  have hB1 : fig1b.ancIn Finset.univ {2} = {2} := by
    ext x
    rw [figAncIn_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    have hle : (fig1b.induce ↑(Finset.univ : Finset (Fin 3))).dir ≤
        (fun u w : Fin 3 => (u, w) = (0, 1) ∨ (u, w) = (2, 1)) := by
      intro a b hab
      exact (figInduceDir hab).2.2
    rcases hx3 with rfl | rfl | rfl
    · constructor
      · rintro ⟨-, y, hy, hr⟩
        have hy2 : y = 2 := Finset.mem_singleton.mp hy
        subst hy2
        have h02 := figReflTransGenB_eq ((Relation.ReflTransGen.mono hle) _ _ hr) rfl
        exact absurd h02 (by decide)
      · intro hcon; exact absurd hcon (by decide)
    · constructor
      · rintro ⟨-, y, hy, hr⟩
        have hy2 : y = 2 := Finset.mem_singleton.mp hy
        subst hy2
        have h12 := figReflTransGenB_eq ((Relation.ReflTransGen.mono hle) _ _ hr) rfl
        exact absurd h12 (by decide)
      · intro hcon; exact absurd hcon (by decide)
    · constructor
      · intro _; decide
      · intro _
        refine ⟨Finset.mem_univ _, 2, by decide, ?_⟩
        exact Relation.ReflTransGen.refl
  have heqB := fun (Y X D : Finset (Fin 3)) (P : IdExpr (Fin 3)) =>
    idRec.eq_def fig1b fig1order Y X D P
  have hcap : ((({0} : Finset (Fin 3))) ∩ {2}) = ∅ := by decide
  have hsd : ((Finset.univ : Finset (Fin 3)) \ {2}) = {0, 1} := by decide
  have hXne : (({0} : Finset (Fin 3))) ≠ ∅ := by decide
  show fig1b.idRec fig1order {2} {0} Finset.univ IdExpr.obs = .ok (.sum ∅ (.sum {0, 1} .obs))
  rw [heqB, ite_eq_right hXne]
  have h2yes : fig1b.ancIn Finset.univ {2} ≠ Finset.univ := by rw [hB1]; decide
  rw [dite_eq_left h2yes, hB1, hcap, hsd, heqB]
  have h1yes : ((∅ : Finset (Fin 3))) = ∅ := rfl
  rw [ite_eq_left h1yes]
  have hsd2 : ((({2} : Finset (Fin 3))) \ {2}) = ∅ := by decide
  rw [hsd2]


end Cslib.MachineLearning.GraphicalModels.ADMG
