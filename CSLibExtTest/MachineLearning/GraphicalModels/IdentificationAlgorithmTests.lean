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

/-- Synthetic graph A directed edges strictly increase the vertex number. -/
theorem synDirA_edge {u w : Fin 3}
    (h : (u, w) = (0, 1) ∨ (u, w) = (1, 2)) : u.val < w.val := by
  rcases h with h | h <;> rw [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;> decide

/-- Transitive closure of the synthetic graph A edges strictly increases the vertex number. -/
theorem synTransGenA {u w : Fin 3}
    (h : Relation.TransGen (fun u w : Fin 3 => (u, w) = (0, 1) ∨ (u, w) = (1, 2)) u w) :
    u.val < w.val := by
  induction h with
  | single hd => exact synDirA_edge hd
  | tail _ hd ih => have h2 := synDirA_edge hd; omega

/-- Synthetic graph B directed edges target `1` from elsewhere. -/
theorem synDirB_edge {u w : Fin 3}
    (h : (u, w) = (0, 1) ∨ (u, w) = (2, 1)) : w = 1 ∧ u ≠ 1 := by
  rcases h with h | h <;> rw [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    exact ⟨rfl, by decide⟩

/-- Transitive closure of the synthetic graph B edges targets `1` from elsewhere. -/
theorem synTransGenB {u w : Fin 3}
    (h : Relation.TransGen (fun u w : Fin 3 => (u, w) = (0, 1) ∨ (u, w) = (2, 1)) u w) :
    w = 1 ∧ u ≠ 1 := by
  induction h with
  | single hd => exact synDirB_edge hd
  | tail _ hd ih =>
    obtain ⟨hb, -⟩ := ih
    obtain ⟨-, hb'⟩ := synDirB_edge hd
    exact absurd hb hb'

/-- Reflexive-transitive closure of the synthetic graph A edges never decreases the vertex number. -/
theorem synReflTransGenA_le {u w : Fin 3}
    (h : Relation.ReflTransGen
      (fun u w : Fin 3 => (u, w) = (0, 1) ∨ (u, w) = (1, 2)) u w) :
    u.val ≤ w.val := by
  induction h with
  | refl => exact le_refl _
  | tail _ hd ih => have h2 := synDirA_edge hd; omega

/-- Only `2` reaches `2` along the Synthetic graph B directed edges. -/
theorem synReflTransGenB_eq {u w : Fin 3}
    (h : Relation.ReflTransGen
      (fun u w : Fin 3 => (u, w) = (0, 1) ∨ (u, w) = (2, 1)) u w) :
    w = 2 → u = 2 := by
  induction h with
  | refl => exact fun h => h
  | tail _ hd ih =>
    intro hw2
    rw [hw2] at hd
    rcases hd with hd | hd <;> rw [Prod.mk.injEq] at hd <;> exact absurd hd.2 (by decide)

/-- The shared bidirected edge only joins `0` and `1`. -/
theorem synBidir_adj {a b : Fin 3}
    (h : (SimpleGraph.fromRel (fun u w : Fin 3 => (u, w) = (0, 1))).Adj a b) :
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  rw [SimpleGraph.fromRel_adj] at h
  obtain ⟨-, h | h⟩ := h
  · left; rw [Prod.mk.injEq] at h; exact h
  · right; rw [Prod.mk.injEq] at h; exact ⟨h.2, h.1⟩

/-- Induced-subgraph directed edges live inside the set and come from the host graph. -/
theorem synInduceDir {G : ADMG (Fin 3)} {D : Finset (Fin 3)} {a b : Fin 3}
    (h : (G.induce ↑D).dir a b) : a ∈ (↑D : Set (Fin 3)) ∧ b ∈ ↑D ∧ G.dir a b := h

/-- Induced-subgraph bidirected edges of a synthetic graph live inside the set and join
`0` with `1`. -/
theorem synInduceBidir_adj {G : ADMG (Fin 3)}
    (hb : G.bidir = SimpleGraph.fromRel (fun u w : Fin 3 => (u, w) = (0, 1)))
    {D : Finset (Fin 3)} {a b : Fin 3}
    (h : (SimpleGraph.fromRel
      (fun x y : Fin 3 => x ∈ (↑D : Set (Fin 3)) ∧ y ∈ ↑D ∧ G.bidir.Adj x y)).Adj a b) :
    a ∈ (↑D : Set (Fin 3)) ∧ b ∈ ↑D ∧ ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) := by
  rw [SimpleGraph.fromRel_adj, hb] at h
  obtain ⟨-, h | h⟩ := h
  · obtain ⟨ham, hbm, hadj⟩ := h
    exact ⟨ham, hbm, synBidir_adj hadj⟩
  · obtain ⟨hbm, ham, hadj⟩ := h
    obtain h | h := synBidir_adj hadj
    · exact ⟨ham, hbm, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨ham, hbm, Or.inl ⟨h.2, h.1⟩⟩

/-- Membership in `ancIn`, through the classical filter. -/
theorem synAncIn_mem (D Y : Finset V) (x : V) :
    x ∈ G.ancIn D Y ↔ x ∈ D ∧ ∃ y ∈ Y, Relation.ReflTransGen (G.induce ↑D).dir x y := by
  classical
  unfold ancIn
  rw [Finset.mem_filter]

/-- Membership in `ancCut`, through the classical filter. -/
theorem synAncCut_mem (D X Y : Finset V) (x : V) :
    x ∈ G.ancCut D X Y ↔ x ∈ D ∧ ∃ y ∈ Y, Relation.ReflTransGen
      (fun a b => (G.induce ↑D).dir a b ∧ b ∉ X) x y := by
  classical
  unfold ancCut
  rw [Finset.mem_filter]

/-- Membership in `compIn`, through the classical filter. -/
theorem synCompIn_mem (D : Finset V) (v x : V) :
    x ∈ G.compIn D v ↔ x ∈ D ∧ x ∈ (G.induce ↑D).cComponent v := by
  classical
  unfold compIn
  rw [Finset.mem_filter]

/-- Synthetic test graph A: X -> Z -> Y with X <-> Z, on Fin 3 with 0 = X, 1 = Z,
2 = Y. P_x(y) is not identifiable here (a hedge), and `ID` fails at line 5. -/
def synA : ADMG (Fin 3) where
  dir u w := (u, w) = (0, 1) ∨ (u, w) = (1, 2)
  bidir := SimpleGraph.fromRel fun u w => (u, w) = (0, 1)
  acyclic := by
    show ∀ v : Fin 3,
      ¬ Relation.TransGen (fun u w : Fin 3 => (u, w) = (0, 1) ∨ (u, w) = (1, 2)) v v
    intro v h
    exact absurd (synTransGenA h) (lt_irrefl _)

/-- Synthetic test graph B: X -> Z <- Y with X <-> Z, on Fin 3 with 0 = X, 1 = Z,
2 = Y. P_x(z) is identifiable here. -/
def synB : ADMG (Fin 3) where
  dir u w := (u, w) = (0, 1) ∨ (u, w) = (2, 1)
  bidir := SimpleGraph.fromRel fun u w => (u, w) = (0, 1)
  acyclic := by
    show ∀ v : Fin 3,
      ¬ Relation.TransGen (fun u w : Fin 3 => (u, w) = (0, 1) ∨ (u, w) = (2, 1)) v v
    intro v h
    obtain ⟨hv, hne⟩ := synTransGenB h
    exact hne hv

/-- The identity ordering on `Fin 3` (`0 = X`, `1 = Z`, `2 = Y`), passed to `ID` as its
ordering parameter. -/
def synOrder : Fin 3 ≃ Fin 3 := Equiv.refl _

theorem synA_fail : synA.ID synOrder {2} {0} = .error ({0, 1}, {1}) := by
  have hA1 : synA.ancIn Finset.univ {2} = Finset.univ := by
    ext x
    rw [synAncIn_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    have h01 : (0 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧ (1 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧
        synA.dir 0 1 := by
      refine ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩
      show ((0, 1) : Fin 3 × Fin 3) = (0, 1) ∨ (0, 1) = (1, 2)
      exact Or.inl rfl
    have h12 : (1 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧ (2 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧
        synA.dir 1 2 := by
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
  have hA2 : synA.ancCut Finset.univ {0} {2} = Finset.univ := by
    ext x
    rw [synAncCut_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    have h01 : (synA.induce ↑(Finset.univ : Finset (Fin 3))).dir 0 1 ∧ (1 : Fin 3) ∉ ({0} : Finset (Fin 3)) := by
      refine ⟨?_, by decide⟩
      show (0 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧ (1 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧
        synA.dir 0 1
      refine ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩
      show ((0, 1) : Fin 3 × Fin 3) = (0, 1) ∨ (0, 1) = (1, 2)
      exact Or.inl rfl
    have h12 : (synA.induce ↑(Finset.univ : Finset (Fin 3))).dir 1 2 ∧ (2 : Fin 3) ∉ ({0} : Finset (Fin 3)) := by
      refine ⟨?_, by decide⟩
      show (1 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧ (2 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧
        synA.dir 1 2
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
  have hA4 : synA.ancIn Finset.univ {1} = {0, 1} := by
    ext x
    rw [synAncIn_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    have hle : (synA.induce ↑(Finset.univ : Finset (Fin 3))).dir ≤
        (fun u w : Fin 3 => (u, w) = (0, 1) ∨ (u, w) = (1, 2)) := by
      intro a b hab
      exact (synInduceDir hab).2.2
    have h01 : (0 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧ (1 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧
        synA.dir 0 1 := by
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
        have hle' := synReflTransGenA_le ((Relation.ReflTransGen.mono hle) _ _ hr)
        exact absurd hle' (by decide)
      · intro hcon; exact absurd hcon (by decide)
  have hA5 : synA.ancIn {0, 1} {1} = {0, 1} := by
    ext x
    rw [synAncIn_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    have h01 : (0 : Fin 3) ∈ (↑(({0, 1} : Finset (Fin 3))) : Set (Fin 3)) ∧
        (1 : Fin 3) ∈ (↑(({0, 1} : Finset (Fin 3))) : Set (Fin 3)) ∧ synA.dir 0 1 := by
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
  have hA6 : synA.ancCut {0, 1} {0} {1} = {0, 1} := by
    ext x
    rw [synAncCut_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    have h01 : (synA.induce ↑(({0, 1} : Finset (Fin 3)))).dir 0 1 ∧
        (1 : Fin 3) ∉ ({0} : Finset (Fin 3)) := by
      refine ⟨?_, by decide⟩
      show (0 : Fin 3) ∈ (↑(({0, 1} : Finset (Fin 3))) : Set (Fin 3)) ∧
        (1 : Fin 3) ∈ (↑(({0, 1} : Finset (Fin 3))) : Set (Fin 3)) ∧ synA.dir 0 1
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
      (synA.induce ↑(({1, 2} : Finset (Fin 3)))).bidir.Reachable 1 w → w = 1 := by
    intro w h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => rfl
    | tail _ hstep ih =>
      rw [ih] at hstep
      obtain ⟨-, hmem, h | h⟩ := synInduceBidir_adj (G := synA) rfl hstep
      · exact absurd h.1 (by decide)
      · have h0mem : (0 : Fin 3) ∈ (({1, 2} : Finset (Fin 3))) := by
          rw [← h.2]; exact Finset.mem_coe.mp hmem
        exact absurd h0mem (by decide)
  have hC11 : synA.compIn {1, 2} 1 = {1} := by
    ext x
    rw [synCompIn_mem]
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
        rw [(synA.induce ↑(({1, 2} : Finset (Fin 3)))).mem_cComponent_iff] at hr
        have h21 := hreach1 hr
        rw [h21]
        decide
      · intro hcon; exact absurd hcon (by decide)
  have hreach2 : ∀ {w : Fin 3},
      (synA.induce ↑(({1, 2} : Finset (Fin 3)))).bidir.Reachable 2 w → w = 2 := by
    intro w h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => rfl
    | tail _ hstep ih =>
      rw [ih] at hstep
      obtain ⟨-, -, h | h⟩ := synInduceBidir_adj (G := synA) rfl hstep
      · exact absurd h.1 (by decide)
      · exact absurd h.1 (by decide)
  have hC12 : synA.compIn {1, 2} 2 = {2} := by
    ext x
    rw [synCompIn_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    rcases hx3 with rfl | rfl | rfl
    · constructor
      · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
      · intro hcon; exact absurd hcon (by decide)
    · constructor
      · rintro ⟨-, hr⟩
        rw [(synA.induce ↑(({1, 2} : Finset (Fin 3)))).mem_cComponent_iff] at hr
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
  have hC3 : synA.cComponentsIn {1, 2} = {{1}, {2}} := by
    unfold cComponentsIn
    rw [Finset.image_insert, Finset.image_singleton, hC11, hC12]
  have hC1 : synA.compIn {1} 1 = {1} := by
    ext x
    rw [synCompIn_mem]
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
  have hA7 : synA.cComponentsIn {1} = {{1}} := by
    unfold cComponentsIn
    rw [Finset.image_singleton, hC1]
  have hC2 : synA.compIn {2} 2 = {2} := by
    ext x
    rw [synCompIn_mem]
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
  have hA10 : synA.cComponentsIn {2} = {{2}} := by
    unfold cComponentsIn
    rw [Finset.image_singleton, hC2]
  have hadj01 : (SimpleGraph.fromRel
        (fun x y : Fin 3 => x ∈ (↑(({0, 1} : Finset (Fin 3))) : Set (Fin 3)) ∧ y ∈ (↑(({0, 1} : Finset (Fin 3))) : Set (Fin 3)) ∧
          synA.bidir.Adj x y)).Adj 0 1 := by
    rw [SimpleGraph.fromRel_adj]
    refine ⟨by decide,
      Or.inl ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩⟩
    have hb01 : (SimpleGraph.fromRel (fun u w : Fin 3 => (u, w) = (0, 1))).Adj 0 1 := by
      rw [SimpleGraph.fromRel_adj]
      exact ⟨by decide, Or.inl rfl⟩
    exact hb01
  have hadj10 : (SimpleGraph.fromRel
        (fun x y : Fin 3 => x ∈ (↑(({0, 1} : Finset (Fin 3))) : Set (Fin 3)) ∧ y ∈ (↑(({0, 1} : Finset (Fin 3))) : Set (Fin 3)) ∧
          synA.bidir.Adj x y)).Adj 1 0 := by
    rw [SimpleGraph.fromRel_adj]
    refine ⟨by decide,
      Or.inl ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩⟩
    have hb10 : (SimpleGraph.fromRel (fun u w : Fin 3 => (u, w) = (0, 1))).Adj 1 0 := by
      rw [SimpleGraph.fromRel_adj]
      exact ⟨by decide, Or.inr rfl⟩
    exact hb10
  have hc0 : synA.compIn {0, 1} 0 = {0, 1} := by
    ext x
    rw [synCompIn_mem]
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
        rw [(synA.induce ↑(({0, 1} : Finset (Fin 3)))).mem_cComponent_iff,
          SimpleGraph.reachable_iff_reflTransGen]
        exact Relation.ReflTransGen.single hadj01
    · constructor
      · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
      · intro hcon; exact absurd hcon (by decide)
  have hc1 : synA.compIn {0, 1} 1 = {0, 1} := by
    ext x
    rw [synCompIn_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    rcases hx3 with rfl | rfl | rfl
    · constructor
      · intro _; decide
      · intro _
        refine ⟨by decide, ?_⟩
        rw [(synA.induce ↑(({0, 1} : Finset (Fin 3)))).mem_cComponent_iff,
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
  have hA8 : synA.cComponentsIn {0, 1} = {{0, 1}} := by
    unfold cComponentsIn
    rw [Finset.image_insert, Finset.image_singleton, hc0, hc1]
    decide
  have hreachU0 : ∀ {w : Fin 3},
      (synA.induce ↑(({0, 1, 2} : Finset (Fin 3)))).bidir.Reachable 0 w → w = 0 ∨ w = 1 := by
    intro w h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact Or.inl rfl
    | tail _ hstep ih =>
      rcases ih with rfl | rfl
      · obtain ⟨-, -, h | h⟩ := synInduceBidir_adj (G := synA) rfl hstep
        · exact Or.inr h.2
        · exact absurd h.1 (by decide)
      · obtain ⟨-, -, h | h⟩ := synInduceBidir_adj (G := synA) rfl hstep
        · exact absurd h.1 (by decide)
        · exact Or.inl h.2
  have hreachU1 : ∀ {w : Fin 3},
      (synA.induce ↑(({0, 1, 2} : Finset (Fin 3)))).bidir.Reachable 1 w → w = 0 ∨ w = 1 := by
    intro w h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact Or.inr rfl
    | tail _ hstep ih =>
      rcases ih with rfl | rfl
      · obtain ⟨-, -, h | h⟩ := synInduceBidir_adj (G := synA) rfl hstep
        · exact Or.inr h.2
        · exact absurd h.1 (by decide)
      · obtain ⟨-, -, h | h⟩ := synInduceBidir_adj (G := synA) rfl hstep
        · exact absurd h.1 (by decide)
        · exact Or.inl h.2
  have hreachU2 : ∀ {w : Fin 3},
      (synA.induce ↑(({0, 1, 2} : Finset (Fin 3)))).bidir.Reachable 2 w → w = 2 := by
    intro w h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => rfl
    | tail _ hstep ih =>
      rw [ih] at hstep
      obtain ⟨-, -, h | h⟩ := synInduceBidir_adj (G := synA) rfl hstep
      · exact absurd h.1 (by decide)
      · exact absurd h.1 (by decide)
  have hu01 : (SimpleGraph.fromRel
        (fun x y : Fin 3 => x ∈ (↑(({0, 1, 2} : Finset (Fin 3))) : Set (Fin 3)) ∧
          y ∈ (↑(({0, 1, 2} : Finset (Fin 3))) : Set (Fin 3)) ∧ synA.bidir.Adj x y)).Adj 0 1 := by
    rw [SimpleGraph.fromRel_adj]
    refine ⟨by decide,
      Or.inl ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩⟩
    have hb01 : (SimpleGraph.fromRel (fun u w : Fin 3 => (u, w) = (0, 1))).Adj 0 1 := by
      rw [SimpleGraph.fromRel_adj]
      exact ⟨by decide, Or.inl rfl⟩
    exact hb01
  have hu10 : (SimpleGraph.fromRel
        (fun x y : Fin 3 => x ∈ (↑(({0, 1, 2} : Finset (Fin 3))) : Set (Fin 3)) ∧
          y ∈ (↑(({0, 1, 2} : Finset (Fin 3))) : Set (Fin 3)) ∧ synA.bidir.Adj x y)).Adj 1 0 := by
    rw [SimpleGraph.fromRel_adj]
    refine ⟨by decide,
      Or.inl ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩⟩
    have hb10 : (SimpleGraph.fromRel (fun u w : Fin 3 => (u, w) = (0, 1))).Adj 1 0 := by
      rw [SimpleGraph.fromRel_adj]
      exact ⟨by decide, Or.inr rfl⟩
    exact hb10
  have cu0 : synA.compIn {0, 1, 2} 0 = {0, 1} := by
    ext x
    rw [synCompIn_mem]
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
        rw [(synA.induce ↑(({0, 1, 2} : Finset (Fin 3)))).mem_cComponent_iff,
          SimpleGraph.reachable_iff_reflTransGen]
        exact Relation.ReflTransGen.single hu01
    · constructor
      · rintro ⟨-, hr⟩
        rw [(synA.induce ↑(({0, 1, 2} : Finset (Fin 3)))).mem_cComponent_iff] at hr
        rcases hreachU0 hr with h | h
        · rw [h]; decide
        · rw [h]; decide
      · intro hcon; exact absurd hcon (by decide)
  have cu1 : synA.compIn {0, 1, 2} 1 = {0, 1} := by
    ext x
    rw [synCompIn_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    rcases hx3 with rfl | rfl | rfl
    · constructor
      · intro _; decide
      · intro _
        refine ⟨by decide, ?_⟩
        rw [(synA.induce ↑(({0, 1, 2} : Finset (Fin 3)))).mem_cComponent_iff,
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
        rw [(synA.induce ↑(({0, 1, 2} : Finset (Fin 3)))).mem_cComponent_iff] at hr
        rcases hreachU1 hr with h | h
        · rw [h]; decide
        · rw [h]; decide
      · intro hcon; exact absurd hcon (by decide)
  have cu2 : synA.compIn {0, 1, 2} 2 = {2} := by
    ext x
    rw [synCompIn_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    rcases hx3 with rfl | rfl | rfl
    · constructor
      · rintro ⟨-, hr⟩
        rw [(synA.induce ↑(({0, 1, 2} : Finset (Fin 3)))).mem_cComponent_iff] at hr
        have h02 := hreachU2 hr
        rw [h02]; decide
      · intro hcon; exact absurd hcon (by decide)
    · constructor
      · rintro ⟨-, hr⟩
        rw [(synA.induce ↑(({0, 1, 2} : Finset (Fin 3)))).mem_cComponent_iff] at hr
        have h12 := hreachU2 hr
        rw [h12]; decide
      · intro hcon; exact absurd hcon (by decide)
    · constructor
      · intro _; decide
      · intro _
        refine ⟨by decide, ?_⟩
        unfold ADMG.cComponent
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  have hA11 : synA.cComponentsIn Finset.univ = {{0, 1}, {2}} := by
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} from by decide]
    unfold cComponentsIn
    rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton, cu0, cu1, cu2]
    decide
  have heqA := fun (Y X D : Finset (Fin 3)) (P : IdExpr (Fin 3)) =>
    idRec.eq_def synA synOrder Y X D P
  have hUX1 : (Finset.univ \ ({1} : Finset (Fin 3))) = {0, 2} := by decide
  have hcall1 : synA.idRec synOrder {1} (Finset.univ \ {1}) Finset.univ IdExpr.obs =
      .error (({0, 1} : Finset (Fin 3)), ({1} : Finset (Fin 3))) := by
    rw [hUX1, heqA]
    have h1ne : (({0, 2} : Finset (Fin 3))) ≠ ∅ := by decide
    rw [ite_eq_right h1ne]
    have h2yes : synA.ancIn Finset.univ {1} ≠ Finset.univ := by rw [hA4]; decide
    rw [dite_eq_left h2yes, hA4]
    have hcap : ((({0, 2} : Finset (Fin 3))) ∩ {0, 1}) = {0} := by decide
    have hsd : (Finset.univ \ (({0, 1} : Finset (Fin 3)))) = {2} := by decide
    rw [hcap, hsd, heqA]
    have h1ne' : (({0} : Finset (Fin 3))) ≠ ∅ := by decide
    rw [ite_eq_right h1ne']
    have h2no : ¬ (synA.ancIn {0, 1} {1} ≠ {0, 1}) := by rw [hA5]; decide
    rw [dite_eq_right h2no]
    have hDX3 : ((({0, 1} : Finset (Fin 3))) \ {0}) = {1} := by decide
    have h3no : ¬ (((({0, 1} : Finset (Fin 3)) \ {0}) \
        synA.ancCut {0, 1} {0} {1}).Nonempty) := by
      rw [hDX3, hA6]
      rw [show ((({1} : Finset (Fin 3))) \ {0, 1}) = ∅ from by decide]
      exact Finset.not_nonempty_empty
    rw [dite_eq_right h3no]
    have h4no : ¬ (((({0, 1} : Finset (Fin 3)) \ {0}) ∉
        synA.cComponentsIn ((({0, 1} : Finset (Fin 3))) \ {0}))) := by
      rw [hDX3, hA7]; decide
    rw [dite_eq_right h4no]
    have h5yes : ({0, 1} : Finset (Fin 3)) ∈ synA.cComponentsIn {0, 1} := by
      rw [hA8]; decide
    rw [dite_eq_left h5yes, hDX3]
  have hUX2 : (Finset.univ \ ({2} : Finset (Fin 3))) = {0, 1} := by decide
  have hcall2 : ∃ v,
      synA.idRec synOrder {2} (Finset.univ \ {2}) Finset.univ IdExpr.obs = .ok v := by
    rw [hUX2, heqA]
    have h1ne : (({0, 1} : Finset (Fin 3))) ≠ ∅ := by decide
    rw [ite_eq_right h1ne]
    have h2no : ¬ (synA.ancIn Finset.univ {2} ≠ Finset.univ) := by rw [hA1]; decide
    rw [dite_eq_right h2no]
    have hDX3 : (Finset.univ \ (({0, 1} : Finset (Fin 3)))) = {2} := by decide
    have h2mem : (2 : Fin 3) ∈ synA.ancCut Finset.univ {0, 1} {2} := by
      rw [synAncCut_mem]
      exact ⟨Finset.mem_univ _, 2, by decide, Relation.ReflTransGen.refl⟩
    have hempty : ((({2} : Finset (Fin 3))) \ synA.ancCut Finset.univ {0, 1} {2}) = ∅ := by
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
        synA.ancCut Finset.univ {0, 1} {2}).Nonempty) := by
      rw [hDX3, hempty]
      exact Finset.not_nonempty_empty
    rw [dite_eq_right h3no]
    have h4no : ¬ ((((Finset.univ : Finset (Fin 3)) \ {0, 1}) ∉
        synA.cComponentsIn ((Finset.univ : Finset (Fin 3)) \ {0, 1}))) := by
      rw [hDX3, hA10]; decide
    rw [dite_eq_right h4no]
    have h5no : ¬ ((Finset.univ : Finset (Fin 3)) ∈ synA.cComponentsIn Finset.univ) := by
      rw [hA11]; decide
    rw [dite_eq_right h5no]
    have h6yes : ((Finset.univ : Finset (Fin 3)) \ {0, 1}) ∈ synA.cComponentsIn Finset.univ := by
      rw [hDX3, hA11]; decide
    rw [ite_eq_left h6yes]
    exact ⟨_, rfl⟩
  have hDX : (Finset.univ \ (({0} : Finset (Fin 3)))) = {1, 2} := by decide
  have hmap : List.mapM
        (fun S : { S : Finset (Fin 3) // S ∈ (synA.cComponentsIn (Finset.univ \ {0})).toList } =>
          synA.idRec synOrder S.1 (Finset.univ \ S.1) Finset.univ IdExpr.obs)
        (synA.cComponentsIn (Finset.univ \ {0})).toList.attach =
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
            synA.idRec synOrder S.1 (Finset.univ \ S.1) Finset.univ IdExpr.obs) l =
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
              synA.idRec synOrder S.1 (Finset.univ \ S.1) Finset.univ IdExpr.obs) a =
              .error (({0, 1} : Finset (Fin 3)), ({1} : Finset (Fin 3))) := by
            show synA.idRec synOrder a.1 (Finset.univ \ a.1) Finset.univ IdExpr.obs = _
            rw [ha1]
            exact hcall1
          simp only [List.mapM_cons, hfa]
          rfl
        · have hfa : ∃ v, (fun S : { S : Finset (Fin 3) //
                S ∈ (({{1}, {2}} : Finset (Finset (Fin 3)))).toList } =>
              synA.idRec synOrder S.1 (Finset.univ \ S.1) Finset.univ IdExpr.obs) a = .ok v := by
            show ∃ v, synA.idRec synOrder a.1 (Finset.univ \ a.1) Finset.univ IdExpr.obs =
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
  show synA.idRec synOrder {2} {0} Finset.univ IdExpr.obs = .error ({0, 1}, {1})
  rw [heqA, ite_eq_right hXne]
  have h2no : ¬ (synA.ancIn Finset.univ {2} ≠ Finset.univ) := by rw [hA1]; decide
  rw [dite_eq_right h2no]
  have h3no : ¬ ((((Finset.univ : Finset (Fin 3)) \ {0}) \
      synA.ancCut Finset.univ {0} {2}).Nonempty) := by
    rw [hDX, hA2]
    rw [show ((({1, 2} : Finset (Fin 3))) \ Finset.univ) = ∅ from by decide]
    exact Finset.not_nonempty_empty
  rw [dite_eq_right h3no]
  have h4yes : ((Finset.univ : Finset (Fin 3)) \ {0}) ∉
      synA.cComponentsIn (Finset.univ \ {0}) := by
    rw [hDX, hC3]; decide
  rw [dite_eq_left h4yes, hmap]
  rfl

def synBOrder : Fin 3 ≃ Fin 3 := Equiv.swap 1 2

theorem synOrder_topological {u w : Fin 3} (h : synA.dir u w) : synOrder u < synOrder w := by
  have h' : (u, w) = (0, 1) ∨ (u, w) = (1, 2) := h
  rcases h' with h' | h' <;> rw [Prod.mk.injEq] at h' <;> obtain ⟨rfl, rfl⟩ := h' <;>
    decide

theorem synBOrder_topological {u w : Fin 3} (h : synB.dir u w) : synBOrder u < synBOrder w := by
  have h' : (u, w) = (0, 1) ∨ (u, w) = (2, 1) := h
  rcases h' with h' | h' <;> rw [Prod.mk.injEq] at h' <;> obtain ⟨rfl, rfl⟩ := h' <;>
    decide

theorem synB_ok : synB.ID synBOrder {2} {0} = .ok (.sum ∅ (.sum {0, 1} .obs)) := by
  have hB1 : synB.ancIn Finset.univ {2} = {2} := by
    ext x
    rw [synAncIn_mem]
    have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
    have hle : (synB.induce ↑(Finset.univ : Finset (Fin 3))).dir ≤
        (fun u w : Fin 3 => (u, w) = (0, 1) ∨ (u, w) = (2, 1)) := by
      intro a b hab
      exact (synInduceDir hab).2.2
    rcases hx3 with rfl | rfl | rfl
    · constructor
      · rintro ⟨-, y, hy, hr⟩
        have hy2 : y = 2 := Finset.mem_singleton.mp hy
        subst hy2
        have h02 := synReflTransGenB_eq ((Relation.ReflTransGen.mono hle) _ _ hr) rfl
        exact absurd h02 (by decide)
      · intro hcon; exact absurd hcon (by decide)
    · constructor
      · rintro ⟨-, y, hy, hr⟩
        have hy2 : y = 2 := Finset.mem_singleton.mp hy
        subst hy2
        have h12 := synReflTransGenB_eq ((Relation.ReflTransGen.mono hle) _ _ hr) rfl
        exact absurd h12 (by decide)
      · intro hcon; exact absurd hcon (by decide)
    · constructor
      · intro _; decide
      · intro _
        refine ⟨Finset.mem_univ _, 2, by decide, ?_⟩
        exact Relation.ReflTransGen.refl
  have heqB := fun (Y X D : Finset (Fin 3)) (P : IdExpr (Fin 3)) =>
    idRec.eq_def synB synBOrder Y X D P
  have hcap : ((({0} : Finset (Fin 3))) ∩ {2}) = ∅ := by decide
  have hsd : ((Finset.univ : Finset (Fin 3)) \ {2}) = {0, 1} := by decide
  have hXne : (({0} : Finset (Fin 3))) ≠ ∅ := by decide
  show synB.idRec synBOrder {2} {0} Finset.univ IdExpr.obs = .ok (.sum ∅ (.sum {0, 1} .obs))
  rw [heqB, ite_eq_right hXne]
  have h2yes : synB.ancIn Finset.univ {2} ≠ Finset.univ := by rw [hB1]; decide
  rw [dite_eq_left h2yes, hB1, hcap, hsd, heqB]
  have h1yes : ((∅ : Finset (Fin 3))) = ∅ := rfl
  rw [ite_eq_left h1yes]
  have hsd2 : ((({2} : Finset (Fin 3))) \ {2}) = ∅ := by decide
  rw [hsd2]

theorem chain2Dir_edge {u w : Fin 2} (h : (u, w) = (0, 1)) : u.val < w.val := by
  rw [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  decide

theorem chain2TransGen {u w : Fin 2}
    (h : Relation.TransGen (fun u w : Fin 2 => (u, w) = (0, 1)) u w) :
    u.val < w.val := by
  induction h with
  | single hd => exact chain2Dir_edge hd
  | tail _ hd ih => have h2 := chain2Dir_edge hd; omega

def chain2 : ADMG (Fin 2) where
  dir u w := (u, w) = (0, 1)
  bidir := ⊥
  acyclic := by
    show ∀ v : Fin 2,
      ¬ Relation.TransGen (fun u w : Fin 2 => (u, w) = (0, 1)) v v
    intro v h
    exact absurd (chain2TransGen h) (lt_irrefl _)

def chain2order : Fin 2 ≃ Fin 2 := Equiv.refl _

theorem chain2InduceBidir_false {D : Finset (Fin 2)} {a b : Fin 2}
    (h : (SimpleGraph.fromRel
      (fun x y : Fin 2 => x ∈ (↑D : Set (Fin 2)) ∧ y ∈ ↑D ∧ chain2.bidir.Adj x y)).Adj a b) :
    False := by
  rw [SimpleGraph.fromRel_adj] at h
  obtain ⟨-, h | h⟩ := h
  · exact h.2.2
  · exact h.2.2

theorem chain2_line6 : chain2.ID chain2order {1} {0} = .ok (.sum ∅ (condChain chain2order (Finset.univ : Finset (Fin 2)) ({1} : Finset (Fin 2)) .obs)) := by
  have hA1c : chain2.ancIn Finset.univ {1} = Finset.univ := by
    ext x
    rw [synAncIn_mem]
    have hx2 : x = 0 ∨ x = 1 := by fin_cases x <;> decide
    have h01 : (0 : Fin 2) ∈ (↑(Finset.univ : Finset (Fin 2)) : Set (Fin 2)) ∧
      (1 : Fin 2) ∈ (↑(Finset.univ : Finset (Fin 2)) : Set (Fin 2)) ∧ chain2.dir 0 1 := by
      refine ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩
      show ((0, 1) : Fin 2 × Fin 2) = (0, 1)
      rfl
    rcases hx2 with rfl | rfl
    · constructor
      · intro h; exact h.1
      · intro _
        refine ⟨Finset.mem_univ _, 1, by decide, ?_⟩
        exact Relation.ReflTransGen.single h01
    · constructor
      · intro h; exact h.1
      · intro _
        refine ⟨Finset.mem_univ _, 1, by decide, ?_⟩
        exact Relation.ReflTransGen.refl
  have hA2c : chain2.ancCut Finset.univ {0} {1} = Finset.univ := by
    ext x
    rw [synAncCut_mem]
    have hx2 : x = 0 ∨ x = 1 := by fin_cases x <;> decide
    have h01 : (chain2.induce ↑(Finset.univ : Finset (Fin 2))).dir 0 1 ∧
      (1 : Fin 2) ∉ ({0} : Finset (Fin 2)) := by
      refine ⟨?_, by decide⟩
      show (0 : Fin 2) ∈ (↑(Finset.univ : Finset (Fin 2)) : Set (Fin 2)) ∧
        (1 : Fin 2) ∈ (↑(Finset.univ : Finset (Fin 2)) : Set (Fin 2)) ∧ chain2.dir 0 1
      refine ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩
      show ((0, 1) : Fin 2 × Fin 2) = (0, 1)
      rfl
    rcases hx2 with rfl | rfl
    · constructor
      · intro h; exact h.1
      · intro _
        refine ⟨Finset.mem_univ _, 1, by decide, ?_⟩
        exact Relation.ReflTransGen.single h01
    · constructor
      · intro h; exact h.1
      · intro _
        refine ⟨Finset.mem_univ _, 1, by decide, ?_⟩
        exact Relation.ReflTransGen.refl
  have hreach : ∀ (D : Finset (Fin 2)) {v w : Fin 2},
    (chain2.induce ↑D).bidir.Reachable v w → v = w := by
    intro D v w h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => rfl
    | tail _ hstep ih =>
      rw [← ih] at hstep
      exact (chain2InduceBidir_false hstep).elim
  have hCc0 : chain2.compIn {0, 1} 0 = {0} := by
    ext x
    rw [synCompIn_mem]
    have hx2 : x = 0 ∨ x = 1 := by fin_cases x <;> decide
    rcases hx2 with rfl | rfl
    · constructor
      · intro _; decide
      · intro _
        refine ⟨by decide, ?_⟩
        rw [mem_cComponent_iff, SimpleGraph.reachable_iff_reflTransGen]
    · constructor
      · intro h
        obtain ⟨-, hc⟩ := h
        rw [mem_cComponent_iff] at hc
        exact absurd (hreach _ hc) (by decide)
      · intro hcon
        exact absurd hcon (by decide)
  have hCc1 : chain2.compIn {0, 1} 1 = {1} := by
    ext x
    rw [synCompIn_mem]
    have hx2 : x = 0 ∨ x = 1 := by fin_cases x <;> decide
    rcases hx2 with rfl | rfl
    · constructor
      · intro h
        obtain ⟨-, hc⟩ := h
        rw [mem_cComponent_iff] at hc
        exact absurd (hreach _ hc) (by decide)
      · intro hcon
        exact absurd hcon (by decide)
    · constructor
      · intro _; decide
      · intro _
        refine ⟨by decide, ?_⟩
        rw [mem_cComponent_iff, SimpleGraph.reachable_iff_reflTransGen]
  have hCcS : chain2.compIn {1} 1 = {1} := by
    ext x
    rw [synCompIn_mem]
    have hx2 : x = 0 ∨ x = 1 := by fin_cases x <;> decide
    rcases hx2 with rfl | rfl
    · constructor
      · intro h; exact h.1
      · intro hcon; exact absurd hcon (by decide)
    · constructor
      · intro _; decide
      · intro _
        refine ⟨by decide, ?_⟩
        rw [mem_cComponent_iff, SimpleGraph.reachable_iff_reflTransGen]
  have hCCu : chain2.cComponentsIn Finset.univ = {{0}, {1}} := by
    have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
    unfold cComponentsIn
    rw [huniv, Finset.image_insert, Finset.image_singleton, hCc0, hCc1]
  have hCC1 : chain2.cComponentsIn {1} = {{1}} := by
    unfold cComponentsIn
    rw [Finset.image_singleton, hCcS]
  have heq := fun (Y X D : Finset (Fin 2)) (P : IdExpr (Fin 2)) =>
    idRec.eq_def chain2 chain2order Y X D P
  have hXne : (({0} : Finset (Fin 2))) ≠ ∅ := by decide
  show chain2.idRec chain2order {1} {0} Finset.univ IdExpr.obs = .ok (.sum ∅ (condChain chain2order Finset.univ {1} .obs))
  rw [heq, ite_eq_right hXne]
  have h2no : ¬ chain2.ancIn Finset.univ {1} ≠ Finset.univ := fun h => h hA1c
  rw [dite_eq_right h2no]
  have hsd : ((Finset.univ : Finset (Fin 2)) \ {0}) = {1} := by decide
  have hsd2 : (({1} : Finset (Fin 2)) \ Finset.univ) = ∅ := by decide
  have h3no : ¬ (((Finset.univ : Finset (Fin 2)) \ {0}) \ chain2.ancCut Finset.univ {0} {1}).Nonempty := by
    rw [hsd, hA2c, hsd2]
    decide
  rw [dite_eq_right h3no]
  have h4no : ¬ ((Finset.univ : Finset (Fin 2)) \ {0}) ∉ chain2.cComponentsIn ((Finset.univ : Finset (Fin 2)) \ {0}) := by
    rw [hsd, hCC1]
    decide
  rw [dite_eq_right h4no]
  have h5no : ¬ (Finset.univ : Finset (Fin 2)) ∈ chain2.cComponentsIn Finset.univ := by
    rw [hCCu]
    decide
  rw [dite_eq_right h5no]
  have h6yes : ((Finset.univ : Finset (Fin 2)) \ {0}) ∈ chain2.cComponentsIn Finset.univ := by
    rw [hsd, hCCu]
    decide
  rw [ite_eq_left h6yes]
  have hsd3 : (({1} : Finset (Fin 2)) \ {1}) = ∅ := by decide
  rw [hsd, hsd3]

theorem chain2_condChain : condChain chain2order (Finset.univ : Finset (Fin 2)) ({1} : Finset (Fin 2)) .obs = .mul (.cond (Finset.univ : Finset (Fin 2)) ({1} : Finset (Fin 2)) ({0} : Finset (Fin 2)) .obs) .one := by
  have hfil : Finset.univ.filter (fun u => chain2order u < chain2order 1) = {0} := by decide
  have htl : (({1} : Finset (Fin 2)).toList) = [1] := Finset.toList_singleton 1
  have heq : condChain chain2order Finset.univ {1} IdExpr.obs =
      IdExpr.prodList ((({1} : Finset (Fin 2)).toList).map fun v =>
        .cond Finset.univ {v} (Finset.univ.filter fun u => chain2order u < chain2order v)
          IdExpr.obs) := rfl
  rw [heq, htl]
  simp only [List.map_cons, List.map_nil]
  rw [hfil]
  rfl

theorem filter_y0_true : Finset.univ.filter
    (fun y : Fin 2 → Bool => ∀ v ∈ ({0} : Set (Fin 2)), y v = true) =
    {(![true, true] : Fin 2 → Bool), (![true, false] : Fin 2 → Bool)} := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro h
    have hy0 : y 0 = true := h 0 (Set.mem_singleton_iff.mpr rfl)
    by_cases hy1 : y 1 = true
    · left
      funext i
      fin_cases i
      · exact hy0
      · exact hy1
    · right
      have hy1' : y 1 = false := by cases h1 : y 1 <;> simp_all
      funext i
      fin_cases i
      · exact hy0
      · exact hy1'
  · rintro (rfl | rfl)
    · intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      rfl
    · intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      rfl

theorem filter_univ_true : Finset.univ.filter
    (fun y : Fin 2 → Bool => ∀ v ∈ (Set.univ : Set (Fin 2)), y v = true) =
    {(![true, true] : Fin 2 → Bool)} := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    funext i
    fin_cases i
    · exact h 0 (Set.mem_univ 0)
    · exact h 1 (Set.mem_univ 1)
  · rintro rfl
    intro v _
    fin_cases v <;> rfl

theorem filter_y0_TT : Finset.univ.filter
    (fun y : Fin 2 → Bool => ∀ v ∈ ({0} : Set (Fin 2)),
      y v = (![true, true] : Fin 2 → Bool) v) =
    {(![true, true] : Fin 2 → Bool), (![true, false] : Fin 2 → Bool)} := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro h
    have hy0 : y 0 = true := h 0 (Set.mem_singleton_iff.mpr rfl)
    by_cases hy1 : y 1 = true
    · left
      funext i
      fin_cases i
      · exact hy0
      · exact hy1
    · right
      have hy1' : y 1 = false := by cases h1 : y 1 <;> simp_all
      funext i
      fin_cases i
      · exact hy0
      · exact hy1'
  · rintro (rfl | rfl)
    · intro v _
      rfl
    · intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      rfl

theorem filter_univ_TT : Finset.univ.filter
    (fun y : Fin 2 → Bool => ∀ v ∈ (Set.univ : Set (Fin 2)),
      y v = (![true, true] : Fin 2 → Bool) v) =
    {(![true, true] : Fin 2 → Bool)} := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    funext i
    fin_cases i
    · exact h 0 (Set.mem_univ 0)
    · exact h 1 (Set.mem_univ 1)
  · rintro rfl
    intro v _
    rfl

theorem filter_eval_sum : Finset.univ.filter
    (fun y : Fin 2 → Bool => ∀ v ∈ ((↑({1} : Finset (Fin 2)))ᶜ : Set (Fin 2)), y v = true) =
    {(![true, true] : Fin 2 → Bool), (![true, false] : Fin 2 → Bool)} := by
  have hU : ((↑({1} : Finset (Fin 2)))ᶜ : Set (Fin 2)) = {0} := by
    ext v
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_singleton,
      Set.mem_singleton_iff]
    fin_cases v <;> decide
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  rw [hU]
  constructor
  · intro h
    have hy0 : y 0 = true := h 0 (Set.mem_singleton_iff.mpr rfl)
    by_cases hy1 : y 1 = true
    · left
      funext i
      fin_cases i
      · exact hy0
      · exact hy1
    · right
      have hy1' : y 1 = false := by cases h1 : y 1 <;> simp_all
      funext i
      fin_cases i
      · exact hy0
      · exact hy1'
  · rintro (rfl | rfl)
    · intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      rfl
    · intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      rfl

theorem filter_eval_condnum : Finset.univ.filter
    (fun y : Fin 2 → Bool => ∀ v ∈ ((↑(({1} ∪ {0} : Finset (Fin 2))) ∪ (↑(Finset.univ : Finset (Fin 2)))ᶜ : Set (Fin 2))), y v = true) =
    {(![true, true] : Fin 2 → Bool)} := by
  have hUnum : ((↑(({1} ∪ {0} : Finset (Fin 2))) ∪ (↑(Finset.univ : Finset (Fin 2)))ᶜ : Set (Fin 2))) = Set.univ := by
    ext v
    simp only [Set.mem_union, Finset.mem_coe, Finset.mem_union, Finset.mem_singleton,
      Set.mem_compl_iff, Finset.mem_univ, Set.mem_univ]
    fin_cases v <;> decide
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [hUnum]
  constructor
  · intro h
    funext i
    fin_cases i
    · exact h 0 (Set.mem_univ 0)
    · exact h 1 (Set.mem_univ 1)
  · rintro rfl
    intro v _
    fin_cases v <;> rfl

theorem filter_eval_outer : Finset.univ.filter
    (fun y : Fin 2 → Bool => ∀ v ∈ ((↑(∅ : Finset (Fin 2)))ᶜ : Set (Fin 2)), y v = true) =
    {(![true, true] : Fin 2 → Bool)} := by
  have hUouter : ((↑(∅ : Finset (Fin 2)))ᶜ : Set (Fin 2)) = Set.univ := by simp
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [hUouter]
  constructor
  · intro h
    funext i
    fin_cases i
    · exact h 0 (Set.mem_univ 0)
    · exact h 1 (Set.mem_univ 1)
  · rintro rfl
    intro v _
    fin_cases v <;> rfl

theorem filter_eval_numTT : Finset.univ.filter
    (fun y : Fin 2 → Bool => ∀ v ∈ ((↑(({1} ∪ {0} : Finset (Fin 2))) ∪ (↑(Finset.univ : Finset (Fin 2)))ᶜ : Set (Fin 2))),
      y v = (![true, true] : Fin 2 → Bool) v) =
    {(![true, true] : Fin 2 → Bool)} := by
  have hUnum : ((↑(({1} ∪ {0} : Finset (Fin 2))) ∪ (↑(Finset.univ : Finset (Fin 2)))ᶜ : Set (Fin 2))) = Set.univ := by
    ext v
    simp only [Set.mem_union, Finset.mem_coe, Finset.mem_union, Finset.mem_singleton,
      Set.mem_compl_iff, Finset.mem_univ, Set.mem_univ]
    fin_cases v <;> decide
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [hUnum]
  constructor
  · intro h
    funext i
    fin_cases i
    · exact h 0 (Set.mem_univ 0)
    · exact h 1 (Set.mem_univ 1)
  · rintro rfl
    intro v _
    rfl

theorem filter_eval_denTT : Finset.univ.filter
    (fun y : Fin 2 → Bool => ∀ v ∈ ((↑({0} : Finset (Fin 2)) ∪ (↑(Finset.univ : Finset (Fin 2)))ᶜ : Set (Fin 2))),
      y v = (![true, true] : Fin 2 → Bool) v) =
    {(![true, true] : Fin 2 → Bool), (![true, false] : Fin 2 → Bool)} := by
  have hUden : ((↑({0} : Finset (Fin 2)) ∪ (↑(Finset.univ : Finset (Fin 2)))ᶜ : Set (Fin 2))) = {0} := by
    ext v
    simp only [Set.mem_union, Finset.mem_coe, Finset.mem_singleton,
      Set.mem_compl_iff, Finset.mem_univ, Set.mem_singleton_iff]
    fin_cases v <;> decide
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  rw [hUden]
  constructor
  · intro h
    have hy0 : y 0 = true := h 0 (Set.mem_singleton_iff.mpr rfl)
    by_cases hy1 : y 1 = true
    · left
      funext i
      fin_cases i
      · exact hy0
      · exact hy1
    · right
      have hy1' : y 1 = false := by cases h1 : y 1 <;> simp_all
      funext i
      fin_cases i
      · exact hy0
      · exact hy1'
  · rintro (rfl | rfl)
    · intro v _
      rfl
    · intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      rfl

theorem chain2_eval_sum : IdExpr.eval (fun x : Fin 2 → Bool => if x 0 then (if x 1 then (3 : ℝ) else 1) else 2) (.sum ({1} : Finset (Fin 2)) .obs) (fun _ => true) = 4 := by
  have hnem : (![true, true] : Fin 2 → Bool) ∉
      ({(![true, false] : Fin 2 → Bool)} : Finset (Fin 2 → Bool)) := by decide
  simp only [IdExpr.eval, MetaMathlibExt.FiniteWeight.marginal]
  rw [filter_eval_sum, Finset.sum_insert hnem, Finset.sum_singleton]
  simp
  norm_num

theorem chain2_eval_cond_zero : IdExpr.eval (fun x : Fin 2 → Bool => if x 0 then (0 : ℝ) else 1) (.cond (Finset.univ : Finset (Fin 2)) ({1} : Finset (Fin 2)) ({0} : Finset (Fin 2)) .obs) (fun _ => true) = 0 := by
  simp only [IdExpr.eval, MetaMathlibExt.FiniteWeight.marginal]
  rw [filter_eval_condnum, Finset.sum_singleton]
  rw [if_pos (show (![true, true] : Fin 2 → Bool) 0 = true from rfl)]
  exact zero_div _

theorem chain2_eval_line6 : IdExpr.eval (fun x : Fin 2 → Bool => if x 0 then (if x 1 then (3 : ℝ) else 1) else 2) (.sum ∅ (.mul (.cond (Finset.univ : Finset (Fin 2)) ({1} : Finset (Fin 2)) ({0} : Finset (Fin 2)) .obs) .one)) (fun _ => true) = 3 / 4 := by
  have hnem : (![true, true] : Fin 2 → Bool) ∉
      ({(![true, false] : Fin 2 → Bool)} : Finset (Fin 2 → Bool)) := by decide
  simp only [IdExpr.eval, MetaMathlibExt.FiniteWeight.marginal]
  rw [filter_eval_outer]
  simp only [Finset.sum_singleton]
  simp only [Set.mem_union]
  simp only [← Set.mem_union]
  rw [filter_eval_numTT, Finset.sum_singleton, filter_eval_denTT, Finset.sum_insert hnem,
    Finset.sum_singleton]
  simp
  norm_num

end Cslib.MachineLearning.GraphicalModels.ADMG

-- IDREC TESTS R2 BEGIN
namespace Cslib.MachineLearning.GraphicalModels.ADMG

variable {V : Type*} [Fintype V] [DecidableEq V] (G : ADMG V)
  (σ : V ≃ Fin (Fintype.card V))  -- π, "some topological ordering of nodes in G"

def gate4order : Fin 4 ≃ Fin 4 := Equiv.swap 2 3

theorem gate4Dir_edge {u w : Fin 4}
    (h : (u, w) = (1, 2) ∨ (u, w) = (0, 3) ∨ (u, w) = (3, 2)) :
    (gate4order u).val < (gate4order w).val := by
  rcases h with h | h | h <;> rw [Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> decide

theorem gate4TransGen {u w : Fin 4}
    (h : Relation.TransGen
      (fun u w : Fin 4 => (u, w) = (1, 2) ∨ (u, w) = (0, 3) ∨ (u, w) = (3, 2)) u w) :
    (gate4order u).val < (gate4order w).val := by
  induction h with
  | single hd => exact gate4Dir_edge hd
  | tail _ hd ih => have h2 := gate4Dir_edge hd; omega

def gate4 : ADMG (Fin 4) where
  dir u w := (u, w) = (1, 2) ∨ (u, w) = (0, 3) ∨ (u, w) = (3, 2)
  bidir := SimpleGraph.fromRel fun u w => (u, w) = (0, 1) ∨ (u, w) = (1, 2)
  acyclic := by
    show ∀ v : Fin 4,
      ¬ Relation.TransGen
        (fun u w : Fin 4 => (u, w) = (1, 2) ∨ (u, w) = (0, 3) ∨ (u, w) = (3, 2)) v v
    intro v h
    exact absurd (gate4TransGen h) (lt_irrefl _)

theorem gate4order_topological {u w : Fin 4} (h : gate4.dir u w) :
    gate4order u < gate4order w := by
  have h' : (u, w) = (1, 2) ∨ (u, w) = (0, 3) ∨ (u, w) = (3, 2) := h
  rcases h' with h' | h' | h' <;> rw [Prod.mk.injEq] at h' <;>
    obtain ⟨rfl, rfl⟩ := h' <;> decide

theorem gate4InduceDir {G : ADMG (Fin 4)} {D : Finset (Fin 4)} {a b : Fin 4}
    (h : (G.induce ↑D).dir a b) :
    a ∈ (↑D : Set (Fin 4)) ∧ b ∈ (↑D : Set (Fin 4)) ∧ G.dir a b := h

theorem gate4Bidir_adj {a b : Fin 4}
    (h : (SimpleGraph.fromRel
      (fun u w : Fin 4 => (u, w) = (0, 1) ∨ (u, w) = (1, 2))).Adj a b) :
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by
  rw [SimpleGraph.fromRel_adj] at h
  obtain ⟨-, h | h⟩ := h
  · rcases h with h | h <;> rw [Prod.mk.injEq] at h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases h with h | h <;> rw [Prod.mk.injEq] at h
    · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))

theorem gate4InduceBidir_adj {G : ADMG (Fin 4)}
    (hb : G.bidir = SimpleGraph.fromRel
      (fun u w : Fin 4 => (u, w) = (0, 1) ∨ (u, w) = (1, 2)))
    {D : Finset (Fin 4)} {a b : Fin 4}
    (h : (SimpleGraph.fromRel
      (fun x y : Fin 4 => x ∈ (↑D : Set (Fin 4)) ∧ y ∈ (↑D : Set (Fin 4)) ∧
        G.bidir.Adj x y)).Adj a b) :
    a ∈ (↑D : Set (Fin 4)) ∧ b ∈ (↑D : Set (Fin 4)) ∧
      ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)) := by
  rw [SimpleGraph.fromRel_adj, hb] at h
  obtain ⟨-, h | h⟩ := h
  · obtain ⟨ham, hbm, hadj⟩ := h
    exact ⟨ham, hbm, gate4Bidir_adj hadj⟩
  · obtain ⟨hbm, ham, hadj⟩ := h
    rcases gate4Bidir_adj hadj with h | h | h | h
    · exact ⟨ham, hbm, Or.inr (Or.inl ⟨h.2, h.1⟩)⟩
    · exact ⟨ham, hbm, Or.inl ⟨h.2, h.1⟩⟩
    · exact ⟨ham, hbm, Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))⟩
    · exact ⟨ham, hbm, Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))⟩

theorem gate4adjU {a b : Fin 4}
    (h : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)) :
    (SimpleGraph.fromRel (fun x y : Fin 4 =>
      x ∈ (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)) ∧
      y ∈ ↑(Finset.univ : Finset (Fin 4)) ∧ gate4.bidir.Adj x y)).Adj a b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hb01 : (SimpleGraph.fromRel
        (fun u w : Fin 4 => (u, w) = (0, 1) ∨ (u, w) = (1, 2))).Adj 0 1 := by
      rw [SimpleGraph.fromRel_adj]
      exact ⟨by decide, Or.inl (Or.inl rfl)⟩
    rw [SimpleGraph.fromRel_adj]
    exact ⟨by decide, Or.inl ⟨Finset.mem_coe.mpr (by decide),
      Finset.mem_coe.mpr (by decide), hb01⟩⟩
  · have hb01 : (SimpleGraph.fromRel
        (fun u w : Fin 4 => (u, w) = (0, 1) ∨ (u, w) = (1, 2))).Adj 0 1 := by
      rw [SimpleGraph.fromRel_adj]
      exact ⟨by decide, Or.inl (Or.inl rfl)⟩
    rw [SimpleGraph.fromRel_adj]
    exact ⟨by decide, Or.inr ⟨Finset.mem_coe.mpr (by decide),
      Finset.mem_coe.mpr (by decide), hb01⟩⟩
  · have hb12 : (SimpleGraph.fromRel
        (fun u w : Fin 4 => (u, w) = (0, 1) ∨ (u, w) = (1, 2))).Adj 1 2 := by
      rw [SimpleGraph.fromRel_adj]
      exact ⟨by decide, Or.inl (Or.inr rfl)⟩
    rw [SimpleGraph.fromRel_adj]
    exact ⟨by decide, Or.inl ⟨Finset.mem_coe.mpr (by decide),
      Finset.mem_coe.mpr (by decide), hb12⟩⟩
  · have hb12 : (SimpleGraph.fromRel
        (fun u w : Fin 4 => (u, w) = (0, 1) ∨ (u, w) = (1, 2))).Adj 1 2 := by
      rw [SimpleGraph.fromRel_adj]
      exact ⟨by decide, Or.inl (Or.inr rfl)⟩
    rw [SimpleGraph.fromRel_adj]
    exact ⟨by decide, Or.inr ⟨Finset.mem_coe.mpr (by decide),
      Finset.mem_coe.mpr (by decide), hb12⟩⟩

theorem gate4adjS {a b : Fin 4} (h : (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)) :
    (SimpleGraph.fromRel (fun x y : Fin 4 =>
      x ∈ (↑(({1, 2} : Finset (Fin 4))) : Set (Fin 4)) ∧
      y ∈ ↑(({1, 2} : Finset (Fin 4))) ∧ gate4.bidir.Adj x y)).Adj a b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hb12 : (SimpleGraph.fromRel
        (fun u w : Fin 4 => (u, w) = (0, 1) ∨ (u, w) = (1, 2))).Adj 1 2 := by
      rw [SimpleGraph.fromRel_adj]
      exact ⟨by decide, Or.inl (Or.inr rfl)⟩
    rw [SimpleGraph.fromRel_adj]
    exact ⟨by decide, Or.inl ⟨Finset.mem_coe.mpr (by decide),
      Finset.mem_coe.mpr (by decide), hb12⟩⟩
  · have hb12 : (SimpleGraph.fromRel
        (fun u w : Fin 4 => (u, w) = (0, 1) ∨ (u, w) = (1, 2))).Adj 1 2 := by
      rw [SimpleGraph.fromRel_adj]
      exact ⟨by decide, Or.inl (Or.inr rfl)⟩
    rw [SimpleGraph.fromRel_adj]
    exact ⟨by decide, Or.inr ⟨Finset.mem_coe.mpr (by decide),
      Finset.mem_coe.mpr (by decide), hb12⟩⟩

theorem gate4reachU {v w : Fin 4} (hv : v = 0 ∨ v = 1 ∨ v = 2)
    (h : (gate4.induce ↑(Finset.univ : Finset (Fin 4))).bidir.Reachable v w) :
    w = 0 ∨ w = 1 ∨ w = 2 := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  revert hv
  induction h with
  | refl => intro hv; exact hv
  | tail _ hstep ih =>
    intro hv
    have hm := ih hv
    rcases hm with rfl | rfl | rfl
    · obtain ⟨-, -, h | h | h | h⟩ := gate4InduceBidir_adj (G := gate4) rfl hstep
      · exact Or.inr (Or.inl h.2)
      · exact absurd h.1 (by decide)
      · exact absurd h.1 (by decide)
      · exact absurd h.1 (by decide)
    · obtain ⟨-, -, h | h | h | h⟩ := gate4InduceBidir_adj (G := gate4) rfl hstep
      · exact absurd h.1 (by decide)
      · exact Or.inl h.2
      · exact Or.inr (Or.inr h.2)
      · exact absurd h.1 (by decide)
    · obtain ⟨-, -, h | h | h | h⟩ := gate4InduceBidir_adj (G := gate4) rfl hstep
      · exact absurd h.1 (by decide)
      · exact absurd h.1 (by decide)
      · exact absurd h.1 (by decide)
      · exact Or.inr (Or.inl h.2)

theorem gate4reachU3 {v w : Fin 4} (hv : v = 3)
    (h : (gate4.induce ↑(Finset.univ : Finset (Fin 4))).bidir.Reachable v w) :
    w = 3 := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  revert hv
  induction h with
  | refl => intro hv; exact hv
  | tail _ hstep ih =>
    intro hv
    have hm := ih hv
    subst hm
    obtain ⟨-, -, h | h | h | h⟩ := gate4InduceBidir_adj (G := gate4) rfl hstep
    · exact absurd h.1 (by decide)
    · exact absurd h.1 (by decide)
    · exact absurd h.1 (by decide)
    · exact absurd h.1 (by decide)

theorem gate4reachS {v w : Fin 4} (hv : v = 1 ∨ v = 2)
    (h : (gate4.induce ↑(({1, 2} : Finset (Fin 4)))).bidir.Reachable v w) :
    w = 1 ∨ w = 2 := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  revert hv
  induction h with
  | refl => intro hv; exact hv
  | tail _ hstep ih =>
    intro hv
    have hm := ih hv
    rcases hm with rfl | rfl
    · obtain ⟨-, hwmem, h | h | h | h⟩ :=
        gate4InduceBidir_adj (G := gate4) rfl hstep
      · exact absurd h.1 (by decide)
      · have h0mem : (0 : Fin 4) ∈ (({1, 2} : Finset (Fin 4))) := by
          rw [← h.2]; exact Finset.mem_coe.mp hwmem
        exact absurd h0mem (by decide)
      · exact Or.inr h.2
      · exact absurd h.1 (by decide)
    · obtain ⟨-, -, h | h | h | h⟩ := gate4InduceBidir_adj (G := gate4) rfl hstep
      · exact absurd h.1 (by decide)
      · exact absurd h.1 (by decide)
      · exact absurd h.1 (by decide)
      · exact Or.inl h.2

theorem gate4compU0 : gate4.compIn Finset.univ 0 = {0, 1, 2} := by
  ext x
  rw [synCompIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · intro _; decide
    · intro _
      refine ⟨Finset.mem_univ _, ?_⟩
      unfold ADMG.cComponent
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  · constructor
    · intro _; decide
    · intro _
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [(gate4.induce ↑(Finset.univ : Finset (Fin 4))).mem_cComponent_iff,
        SimpleGraph.reachable_iff_reflTransGen]
      exact Relation.ReflTransGen.single (gate4adjU (Or.inl ⟨rfl, rfl⟩))
  · constructor
    · intro _; decide
    · intro _
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [(gate4.induce ↑(Finset.univ : Finset (Fin 4))).mem_cComponent_iff,
        SimpleGraph.reachable_iff_reflTransGen]
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (gate4adjU (Or.inl ⟨rfl, rfl⟩)))
        (Relation.ReflTransGen.single
          (gate4adjU (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
  · constructor
    · rintro ⟨-, hr⟩
      rw [(gate4.induce ↑(Finset.univ : Finset (Fin 4))).mem_cComponent_iff] at hr
      rcases gate4reachU (Or.inl rfl) hr with h | h | h
      · rw [h]; decide
      · rw [h]; decide
      · rw [h]; decide
    · intro hcon; exact absurd hcon (by decide)

theorem gate4compU1 : gate4.compIn Finset.univ 1 = {0, 1, 2} := by
  ext x
  rw [synCompIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · intro _; decide
    · intro _
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [(gate4.induce ↑(Finset.univ : Finset (Fin 4))).mem_cComponent_iff,
        SimpleGraph.reachable_iff_reflTransGen]
      exact Relation.ReflTransGen.single
        (gate4adjU (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · constructor
    · intro _; decide
    · intro _
      refine ⟨Finset.mem_univ _, ?_⟩
      unfold ADMG.cComponent
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  · constructor
    · intro _; decide
    · intro _
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [(gate4.induce ↑(Finset.univ : Finset (Fin 4))).mem_cComponent_iff,
        SimpleGraph.reachable_iff_reflTransGen]
      exact Relation.ReflTransGen.single
        (gate4adjU (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  · constructor
    · rintro ⟨-, hr⟩
      rw [(gate4.induce ↑(Finset.univ : Finset (Fin 4))).mem_cComponent_iff] at hr
      rcases gate4reachU (Or.inr (Or.inl rfl)) hr with h | h | h
      · rw [h]; decide
      · rw [h]; decide
      · rw [h]; decide
    · intro hcon; exact absurd hcon (by decide)

theorem gate4compU2 : gate4.compIn Finset.univ 2 = {0, 1, 2} := by
  ext x
  rw [synCompIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · intro _; decide
    · intro _
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [(gate4.induce ↑(Finset.univ : Finset (Fin 4))).mem_cComponent_iff,
        SimpleGraph.reachable_iff_reflTransGen]
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single
          (gate4adjU (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
        (Relation.ReflTransGen.single (gate4adjU (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  · constructor
    · intro _; decide
    · intro _
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [(gate4.induce ↑(Finset.univ : Finset (Fin 4))).mem_cComponent_iff,
        SimpleGraph.reachable_iff_reflTransGen]
      exact Relation.ReflTransGen.single
        (gate4adjU (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
  · constructor
    · intro _; decide
    · intro _
      refine ⟨Finset.mem_univ _, ?_⟩
      unfold ADMG.cComponent
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  · constructor
    · rintro ⟨-, hr⟩
      rw [(gate4.induce ↑(Finset.univ : Finset (Fin 4))).mem_cComponent_iff] at hr
      rcases gate4reachU (Or.inr (Or.inr rfl)) hr with h | h | h
      · rw [h]; decide
      · rw [h]; decide
      · rw [h]; decide
    · intro hcon; exact absurd hcon (by decide)

theorem gate4compU3 : gate4.compIn Finset.univ 3 = {3} := by
  ext x
  rw [synCompIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · rintro ⟨-, hr⟩
      rw [(gate4.induce ↑(Finset.univ : Finset (Fin 4))).mem_cComponent_iff] at hr
      have h03 := gate4reachU3 rfl hr
      exact absurd h03 (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · rintro ⟨-, hr⟩
      rw [(gate4.induce ↑(Finset.univ : Finset (Fin 4))).mem_cComponent_iff] at hr
      have h13 := gate4reachU3 rfl hr
      exact absurd h13 (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · rintro ⟨-, hr⟩
      rw [(gate4.induce ↑(Finset.univ : Finset (Fin 4))).mem_cComponent_iff] at hr
      have h23 := gate4reachU3 rfl hr
      exact absurd h23 (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · intro _; decide
    · intro _
      refine ⟨Finset.mem_univ _, ?_⟩
      unfold ADMG.cComponent
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl

theorem gate4_comp_univ (v : Fin 4) (hv : v = 1 ∨ v = 2) :
    gate4.compIn Finset.univ v = {0, 1, 2} := by
  rcases hv with rfl | rfl
  · exact gate4compU1
  · exact gate4compU2

theorem gate4_cComponents_univ :
    gate4.cComponentsIn Finset.univ = {{0, 1, 2}, {3}} := by
  have hU : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  unfold cComponentsIn
  rw [hU, Finset.image_insert, Finset.image_insert, Finset.image_insert,
    Finset.image_singleton, ← hU,
    gate4compU0, gate4compU1, gate4compU2, gate4compU3]
  decide

theorem gate4compS1 : gate4.compIn {1, 2} 1 = {1, 2} := by
  ext x
  rw [synCompIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  rcases hx4 with rfl | rfl | rfl | rfl
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
    · intro _; decide
    · intro _
      refine ⟨by decide, ?_⟩
      rw [(gate4.induce ↑(({1, 2} : Finset (Fin 4)))).mem_cComponent_iff,
        SimpleGraph.reachable_iff_reflTransGen]
      exact Relation.ReflTransGen.single (gate4adjS (Or.inl ⟨rfl, rfl⟩))
  · constructor
    · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
    · intro hcon; exact absurd hcon (by decide)

theorem gate4compS2 : gate4.compIn {1, 2} 2 = {1, 2} := by
  ext x
  rw [synCompIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · intro _; decide
    · intro _
      refine ⟨by decide, ?_⟩
      rw [(gate4.induce ↑(({1, 2} : Finset (Fin 4)))).mem_cComponent_iff,
        SimpleGraph.reachable_iff_reflTransGen]
      exact Relation.ReflTransGen.single (gate4adjS (Or.inr ⟨rfl, rfl⟩))
  · constructor
    · intro _; decide
    · intro _
      refine ⟨by decide, ?_⟩
      unfold ADMG.cComponent
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  · constructor
    · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
    · intro hcon; exact absurd hcon (by decide)

theorem gate4_cComponents_sdiff : gate4.cComponentsIn {1, 2} = {{1, 2}} := by
  unfold cComponentsIn
  rw [Finset.image_insert, Finset.image_singleton, gate4compS1, gate4compS2]
  decide

theorem gate4_ancIn_univ : gate4.ancIn Finset.univ {2} = Finset.univ := by
  ext x
  rw [synAncIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  have h12 : (1 : Fin 4) ∈ (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)) ∧
      (2 : Fin 4) ∈ (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)) ∧ gate4.dir 1 2 := by
    refine ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩
    show ((1, 2) : Fin 4 × Fin 4) = (1, 2) ∨ (1, 2) = (0, 3) ∨ (1, 2) = (3, 2)
    exact Or.inl rfl
  have h03 : (0 : Fin 4) ∈ (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)) ∧
      (3 : Fin 4) ∈ (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)) ∧ gate4.dir 0 3 := by
    refine ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩
    show ((0, 3) : Fin 4 × Fin 4) = (1, 2) ∨ (0, 3) = (0, 3) ∨ (0, 3) = (3, 2)
    exact Or.inr (Or.inl rfl)
  have h32 : (3 : Fin 4) ∈ (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)) ∧
      (2 : Fin 4) ∈ (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)) ∧ gate4.dir 3 2 := by
    refine ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩
    show ((3, 2) : Fin 4 × Fin 4) = (1, 2) ∨ (3, 2) = (0, 3) ∨ (3, 2) = (3, 2)
    exact Or.inr (Or.inr rfl)
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · intro h; exact h.1
    · intro _
      refine ⟨Finset.mem_univ _, 2, by decide, ?_⟩
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single h03)
        (Relation.ReflTransGen.single h32)
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
  · constructor
    · intro h; exact h.1
    · intro _
      refine ⟨Finset.mem_univ _, 2, by decide, ?_⟩
      exact Relation.ReflTransGen.single h32

theorem gate4cut0step {z : Fin 4}
    (h : (gate4.induce ↑(Finset.univ : Finset (Fin 4))).dir 0 z ∧
      z ∉ (({0, 3} : Finset (Fin 4)))) : False := by
  obtain ⟨hdir, hnot⟩ := h
  have hg := (gate4InduceDir hdir).2.2
  have hg' : ((0, z) : Fin 4 × Fin 4) = (1, 2) ∨ ((0, z) : Fin 4 × Fin 4) = (0, 3) ∨
      ((0, z) : Fin 4 × Fin 4) = (3, 2) := hg
  rcases hg' with hg | hg | hg <;> rw [Prod.mk.injEq] at hg
  · exact absurd hg.1 (by decide)
  · rw [hg.2] at hnot; exact absurd hnot (by decide)
  · exact absurd hg.1 (by decide)

theorem gate4cut0 {y : Fin 4}
    (h : Relation.ReflTransGen
      (fun a b => (gate4.induce ↑(Finset.univ : Finset (Fin 4))).dir a b ∧
        b ∉ (({0, 3} : Finset (Fin 4)))) 0 y) : 0 = y := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    rw [← ih] at hstep
    exact (gate4cut0step hstep).elim

theorem gate4ancS0step {z : Fin 4}
    (h : (gate4.induce ↑(({0, 1, 2} : Finset (Fin 4)))).dir 0 z) : False := by
  obtain ⟨-, hymem, hg⟩ := gate4InduceDir h
  have hg' : ((0, z) : Fin 4 × Fin 4) = (1, 2) ∨ ((0, z) : Fin 4 × Fin 4) = (0, 3) ∨
      ((0, z) : Fin 4 × Fin 4) = (3, 2) := hg
  rcases hg' with hg | hg | hg <;> rw [Prod.mk.injEq] at hg
  · exact absurd hg.1 (by decide)
  · rw [hg.2, Finset.mem_coe] at hymem
    exact absurd hymem (by decide)
  · exact absurd hg.1 (by decide)

theorem gate4ancS0 {y : Fin 4}
    (h : Relation.ReflTransGen
      (gate4.induce ↑(({0, 1, 2} : Finset (Fin 4)))).dir 0 y) : 0 = y := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    rw [← ih] at hstep
    exact (gate4ancS0step hstep).elim

theorem gate4_ancCut_univ :
    gate4.ancCut Finset.univ {0, 3} {2} = {1, 2, 3} := by
  ext x
  rw [synAncCut_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  have h12 : (gate4.induce ↑(Finset.univ : Finset (Fin 4))).dir 1 2 ∧
      (2 : Fin 4) ∉ (({0, 3} : Finset (Fin 4))) := by
    refine ⟨?_, by decide⟩
    show (1 : Fin 4) ∈ (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)) ∧
      (2 : Fin 4) ∈ (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)) ∧ gate4.dir 1 2
    refine ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩
    show ((1, 2) : Fin 4 × Fin 4) = (1, 2) ∨ (1, 2) = (0, 3) ∨ (1, 2) = (3, 2)
    exact Or.inl rfl
  have h32 : (gate4.induce ↑(Finset.univ : Finset (Fin 4))).dir 3 2 ∧
      (2 : Fin 4) ∉ (({0, 3} : Finset (Fin 4))) := by
    refine ⟨?_, by decide⟩
    show (3 : Fin 4) ∈ (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)) ∧
      (2 : Fin 4) ∈ (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)) ∧ gate4.dir 3 2
    refine ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩
    show ((3, 2) : Fin 4 × Fin 4) = (1, 2) ∨ (3, 2) = (0, 3) ∨ (3, 2) = (3, 2)
    exact Or.inr (Or.inr rfl)
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · rintro ⟨-, y, hy, hr⟩
      have hy2 : y = 2 := Finset.mem_singleton.mp hy
      subst hy2
      have h02 := gate4cut0 hr
      exact absurd h02 (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · intro _; decide
    · intro _
      refine ⟨Finset.mem_univ _, 2, by decide, ?_⟩
      exact Relation.ReflTransGen.single h12
  · constructor
    · intro _; decide
    · intro _
      refine ⟨Finset.mem_univ _, 2, by decide, ?_⟩
      exact Relation.ReflTransGen.refl
  · constructor
    · intro _; decide
    · intro _
      refine ⟨Finset.mem_univ _, 2, by decide, ?_⟩
      exact Relation.ReflTransGen.single h32

theorem gate4_ancIn_S' : gate4.ancIn {0, 1, 2} {2} = {1, 2} := by
  ext x
  rw [synAncIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  have h12 : (1 : Fin 4) ∈ (↑(({0, 1, 2} : Finset (Fin 4))) : Set (Fin 4)) ∧
      (2 : Fin 4) ∈ (↑(({0, 1, 2} : Finset (Fin 4))) : Set (Fin 4)) ∧
      gate4.dir 1 2 := by
    refine ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩
    show ((1, 2) : Fin 4 × Fin 4) = (1, 2) ∨ (1, 2) = (0, 3) ∨ (1, 2) = (3, 2)
    exact Or.inl rfl
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · rintro ⟨-, y, hy, hr⟩
      have hy2 : y = 2 := Finset.mem_singleton.mp hy
      subst hy2
      have h02 := gate4ancS0 hr
      exact absurd h02 (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · intro _; decide
    · intro _
      refine ⟨by decide, 2, by decide, ?_⟩
      exact Relation.ReflTransGen.single h12
  · constructor
    · intro _; decide
    · intro _
      refine ⟨by decide, 2, by decide, ?_⟩
      exact Relation.ReflTransGen.refl
  · constructor
    · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
    · intro hcon; exact absurd hcon (by decide)

theorem gate4_line7 : gate4.ID gate4order {2} {0, 3} =
    .ok (.sum {1} (.sum {0} (condChain gate4order
      (Finset.univ : Finset (Fin 4)) ({0, 1, 2} : Finset (Fin 4)) .obs))) := by
  have heqG := fun (Y X D : Finset (Fin 4)) (P : IdExpr (Fin 4)) =>
    idRec.eq_def gate4 gate4order Y X D P
  have hDX : ((Finset.univ : Finset (Fin 4)) \ ({0, 3} : Finset (Fin 4))) = {1, 2} := by
    decide
  have hS : ∀ h : ((Finset.univ : Finset (Fin 4)) \
      ({0, 3} : Finset (Fin 4))).Nonempty,
      gate4.compIn Finset.univ h.choose = {0, 1, 2} := by
    intro h
    apply gate4_comp_univ
    have hc : h.choose ∈ ({1, 2} : Finset (Fin 4)) := by
      rw [← hDX]
      exact h.choose_spec
    rw [Finset.mem_insert, Finset.mem_singleton] at hc
    exact hc
  have hL7 : ∀ h : ((Finset.univ : Finset (Fin 4)) \
      ({0, 3} : Finset (Fin 4))).Nonempty,
      (have hne := h;
        let S' := gate4.compIn Finset.univ hne.choose;
        gate4.idRec gate4order {2} (({0, 3} : Finset (Fin 4)) ∩ S') S'
          (condChain gate4order Finset.univ S' .obs)) =
      gate4.idRec gate4order {2} {0} {0, 1, 2}
        (condChain gate4order Finset.univ {0, 1, 2} .obs) := by
    intro h
    show (let S' := gate4.compIn Finset.univ h.choose;
      gate4.idRec gate4order {2} (({0, 3} : Finset (Fin 4)) ∩ S') S'
        (condChain gate4order Finset.univ S' .obs)) = _
    show gate4.idRec gate4order {2}
      ((({0, 3} : Finset (Fin 4))) ∩ gate4.compIn Finset.univ h.choose)
      (gate4.compIn Finset.univ h.choose)
      (condChain gate4order Finset.univ
        (gate4.compIn Finset.univ h.choose) .obs) = _
    rw [hS h]
    rw [show ((({0, 3} : Finset (Fin 4))) ∩ {0, 1, 2}) = {0} from by decide]
  have hXne : (({0, 3} : Finset (Fin 4))) ≠ ∅ := by decide
  show gate4.idRec gate4order {2} {0, 3} Finset.univ IdExpr.obs =
    .ok (.sum {1} (.sum {0} (condChain gate4order Finset.univ {0, 1, 2} .obs)))
  rw [heqG, ite_eq_right hXne]
  have h2no : ¬ (gate4.ancIn Finset.univ {2} ≠ Finset.univ) := by
    rw [gate4_ancIn_univ]; decide
  rw [dite_eq_right h2no]
  have h3no : ¬ ((((Finset.univ : Finset (Fin 4)) \ {0, 3}) \
      gate4.ancCut Finset.univ {0, 3} {2}).Nonempty) := by
    rw [hDX, gate4_ancCut_univ,
      show ((({1, 2} : Finset (Fin 4))) \ {1, 2, 3}) = ∅ from by decide]
    exact Finset.not_nonempty_empty
  rw [dite_eq_right h3no]
  have h4no : ¬ (((Finset.univ : Finset (Fin 4)) \ {0, 3}) ∉
      gate4.cComponentsIn ((Finset.univ : Finset (Fin 4)) \ {0, 3})) := by
    rw [hDX, gate4_cComponents_sdiff]; decide
  rw [dite_eq_right h4no]
  have h5no : ¬ ((Finset.univ : Finset (Fin 4)) ∈ gate4.cComponentsIn Finset.univ) := by
    rw [gate4_cComponents_univ]; decide
  rw [dite_eq_right h5no]
  have h6no : ¬ (((Finset.univ : Finset (Fin 4)) \ {0, 3}) ∈
      gate4.cComponentsIn Finset.univ) := by
    rw [hDX, gate4_cComponents_univ]; decide
  rw [ite_eq_right h6no, hL7]
  rw [heqG]
  have h1ne' : (({0} : Finset (Fin 4))) ≠ ∅ := by decide
  rw [ite_eq_right h1ne']
  have h2yes : gate4.ancIn {0, 1, 2} {2} ≠ {0, 1, 2} := by
    rw [gate4_ancIn_S']; decide
  rw [dite_eq_left h2yes, gate4_ancIn_S']
  have hcap : ((({0} : Finset (Fin 4))) ∩ {1, 2}) = ∅ := by decide
  have hsd : ((({0, 1, 2} : Finset (Fin 4))) \ {1, 2}) = {0} := by decide
  rw [hcap, hsd, heqG]
  have h1yes : ((∅ : Finset (Fin 4))) = ∅ := rfl
  rw [ite_eq_left h1yes]
  have hsd2 : ((({1, 2} : Finset (Fin 4))) \ {2}) = {1} := by decide
  rw [hsd2]

def g3order : Fin 3 ≃ Fin (Fintype.card (Fin 3)) := Equiv.swap 0 1

theorem g3Dir_edge {u w : Fin 3}
    (h : (u, w) = (1, 0) ∨ (u, w) = (0, 2)) :
    (g3order u).val < (g3order w).val := by
  rcases h with h | h <;> rw [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;> decide

theorem g3TransGen {u w : Fin 3}
    (h : Relation.TransGen (fun u w : Fin 3 => (u, w) = (1, 0) ∨ (u, w) = (0, 2)) u w) :
    (g3order u).val < (g3order w).val := by
  induction h with
  | single hd => exact g3Dir_edge hd
  | tail _ hd ih => have h2 := g3Dir_edge hd; omega

def G3 : ADMG (Fin 3) where
  dir u w := (u, w) = (1, 0) ∨ (u, w) = (0, 2)
  bidir := SimpleGraph.fromRel fun _ _ => False
  acyclic := by
    show ∀ v : Fin 3,
      ¬ Relation.TransGen (fun u w : Fin 3 => (u, w) = (1, 0) ∨ (u, w) = (0, 2)) v v
    intro v h
    exact absurd (g3TransGen h) (lt_irrefl _)

theorem g3Bidir_empty {a b : Fin 3}
    (h : (SimpleGraph.fromRel (fun _ _ : Fin 3 => False)).Adj a b) : False := by
  rw [SimpleGraph.fromRel_adj] at h
  obtain ⟨-, h | h⟩ := h
  · exact h
  · exact h

theorem g3InduceBidir_empty {D : Finset (Fin 3)} {a b : Fin 3}
    (h : (G3.induce ↑D).bidir.Adj a b) : False := by
  have h' : (SimpleGraph.fromRel
      (fun x y : Fin 3 => x ∈ (↑D : Set (Fin 3)) ∧ y ∈ ↑D ∧ G3.bidir.Adj x y)).Adj a b := h
  rw [SimpleGraph.fromRel_adj] at h'
  obtain ⟨-, h'' | h''⟩ := h'
  · exact g3Bidir_empty h''.2.2
  · exact g3Bidir_empty h''.2.2

theorem g3InduceReach_eq {D : Finset (Fin 3)} {u w : Fin 3}
    (h : (G3.induce ↑D).bidir.Reachable u w) : u = w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ hd _ => exact (g3InduceBidir_empty hd).elim

theorem g3InduceCComponent_eq {D : Finset (Fin 3)} (v : Fin 3) :
    (G3.induce ↑D).cComponent v = {v} := by
  ext w
  constructor
  · intro hw
    rw [Set.mem_singleton_iff]
    exact (g3InduceReach_eq ((G3.induce ↑D).mem_cComponent_iff.mp hw)).symm
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    apply (G3.induce ↑D).mem_cComponent_iff.mpr
    rw [SimpleGraph.reachable_iff_reflTransGen]

theorem g3CompIn_eq {D : Finset (Fin 3)} {v : Fin 3} (hv : v ∈ D) :
    G3.compIn D v = {v} := by
  ext x
  rw [synCompIn_mem, g3InduceCComponent_eq]
  constructor
  · rintro ⟨-, hxvc⟩
    rw [Set.mem_singleton_iff] at hxvc
    rw [hxvc]
    exact Finset.mem_singleton_self v
  · intro hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact ⟨hv, rfl⟩

theorem g3CC_single : G3.cComponentsIn {2} = {{2}} := by
  have h2 : G3.compIn {2} 2 = {2} := g3CompIn_eq (by decide)
  unfold cComponentsIn
  rw [Finset.image_singleton, h2]

theorem g3CC_univ : G3.cComponentsIn Finset.univ = {{0}, {1}, {2}} := by
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  have h0 : G3.compIn {0, 1, 2} 0 = {0} := g3CompIn_eq (by decide)
  have h1 : G3.compIn {0, 1, 2} 1 = {1} := g3CompIn_eq (by decide)
  have h2 : G3.compIn {0, 1, 2} 2 = {2} := g3CompIn_eq (by decide)
  unfold cComponentsIn
  rw [huniv, Finset.image_insert, Finset.image_insert, Finset.image_singleton, h0, h1, h2]

theorem g3AncIn : G3.ancIn Finset.univ {2} = Finset.univ := by
  ext x
  rw [synAncIn_mem]
  have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
  have h10 : (1 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧
      (0 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧ G3.dir 1 0 := by
    refine ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩
    show ((1, 0) : Fin 3 × Fin 3) = (1, 0) ∨ (1, 0) = (0, 2)
    exact Or.inl rfl
  have h02 : (0 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧
      (2 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧ G3.dir 0 2 := by
    refine ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩
    show ((0, 2) : Fin 3 × Fin 3) = (1, 0) ∨ (0, 2) = (0, 2)
    exact Or.inr rfl
  rcases hx3 with rfl | rfl | rfl
  · constructor
    · intro h; exact h.1
    · intro _
      refine ⟨Finset.mem_univ _, 2, by decide, ?_⟩
      exact Relation.ReflTransGen.single h02
  · constructor
    · intro h; exact h.1
    · intro _
      refine ⟨Finset.mem_univ _, 2, by decide, ?_⟩
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single h10)
        (Relation.ReflTransGen.single h02)
  · constructor
    · intro h; exact h.1
    · intro _
      refine ⟨Finset.mem_univ _, 2, by decide, ?_⟩
      exact Relation.ReflTransGen.refl

theorem g3CutFrom1 {X : Finset (Fin 3)} (h0X : (0 : Fin 3) ∈ X) {y : Fin 3}
    (h : Relation.ReflTransGen
      (fun a b : Fin 3 => ((a, b) = (1, 0) ∨ (a, b) = (0, 2)) ∧ b ∉ X) 1 y) :
    y = 1 := by
  induction h with
  | refl => rfl
  | tail _ hcb ih =>
    subst ih
    obtain ⟨hedge, hynot⟩ := hcb
    rcases hedge with hedge | hedge
    · rw [Prod.mk.injEq] at hedge
      obtain ⟨-, rfl⟩ := hedge
      exact absurd h0X hynot
    · rw [Prod.mk.injEq] at hedge
      obtain ⟨h10, -⟩ := hedge
      exact absurd h10 (by decide)

theorem g3AncCut {X : Finset (Fin 3)} (h0X : (0 : Fin 3) ∈ X) (h2X : (2 : Fin 3) ∉ X) :
    G3.ancCut Finset.univ X {2} = {0, 2} := by
  ext x
  rw [synAncCut_mem]
  have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
  have h02 : (G3.induce ↑(Finset.univ : Finset (Fin 3))).dir 0 2 ∧ (2 : Fin 3) ∉ X := by
    refine ⟨?_, h2X⟩
    show (0 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧
      (2 : Fin 3) ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) ∧ G3.dir 0 2
    refine ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), ?_⟩
    show ((0, 2) : Fin 3 × Fin 3) = (1, 0) ∨ (0, 2) = (0, 2)
    exact Or.inr rfl
  have hle : (fun a b : Fin 3 => (G3.induce ↑(Finset.univ : Finset (Fin 3))).dir a b ∧ b ∉ X)
      ≤ (fun a b : Fin 3 => ((a, b) = (1, 0) ∨ (a, b) = (0, 2)) ∧ b ∉ X) := by
    intro a b hab
    exact ⟨(synInduceDir hab.1).2.2, hab.2⟩
  rcases hx3 with rfl | rfl | rfl
  · constructor
    · intro _; decide
    · intro _
      refine ⟨Finset.mem_univ _, 2, by decide, ?_⟩
      exact Relation.ReflTransGen.single h02
  · constructor
    · rintro ⟨-, y, hy, hr⟩
      have hy2 : y = 2 := Finset.mem_singleton.mp hy
      subst hy2
      have hr' := (Relation.ReflTransGen.mono hle) _ _ hr
      have h21 : (2 : Fin 3) = 1 := g3CutFrom1 h0X hr'
      exact absurd h21 (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · intro _; decide
    · intro _
      refine ⟨Finset.mem_univ _, 2, by decide, ?_⟩
      exact Relation.ReflTransGen.refl

theorem g3AncCut1 : G3.ancCut Finset.univ {0} {2} = {0, 2} :=
  g3AncCut (by decide) (by decide)

theorem g3AncCut2 : G3.ancCut Finset.univ {0, 1} {2} = {0, 2} :=
  g3AncCut (by decide) (by decide)

theorem g3_line3 :
    G3.ID g3order {2} {0} = .ok (.sum ∅ (condChain g3order Finset.univ {2} .obs)) := by
  have hXne : ({0} : Finset (Fin 3)) ≠ ∅ := by decide
  have hA2 : ¬ (G3.ancIn Finset.univ {2} ≠ Finset.univ) := fun h => h g3AncIn
  have hW : ((Finset.univ \ {0}) \ G3.ancCut Finset.univ {0} {2}).Nonempty := by
    rw [g3AncCut1]
    exact ⟨1, by decide⟩
  have hX' : ({0} ∪ (Finset.univ \ {0}) \ G3.ancCut Finset.univ {0} {2}) = {0, 1} := by
    rw [g3AncCut1]
    decide
  have hXne2 : ({0, 1} : Finset (Fin 3)) ≠ ∅ := by decide
  have hW2 : ¬ (((Finset.univ \ {0, 1}) \ G3.ancCut Finset.univ {0, 1} {2}).Nonempty) := by
    rw [g3AncCut2]
    decide
  have hDX : (Finset.univ : Finset (Fin 3)) \ {0, 1} = {2} := by decide
  have hT : ¬ ((Finset.univ \ {0, 1}) ∉ G3.cComponentsIn (Finset.univ \ {0, 1})) := by
    rw [hDX, g3CC_single]
    exact fun h => h (by decide)
  have hD : ¬ (Finset.univ ∈ G3.cComponentsIn Finset.univ) := by
    rw [g3CC_univ]
    decide
  have h6 : (Finset.univ \ {0, 1}) ∈ G3.cComponentsIn Finset.univ := by
    rw [hDX, g3CC_univ]
    decide
  show G3.idRec g3order {2} {0} Finset.univ .obs =
    .ok (.sum ∅ (condChain g3order Finset.univ {2} .obs))
  rw [idRec.eq_def]
  simp only [ite_eq_right hXne, dite_eq_right hA2, dite_eq_left hW]
  rw [hX']
  rw [idRec.eq_def]
  simp only [ite_eq_right hXne2, dite_eq_right hA2, dite_eq_right hW2, dite_eq_right hT,
    dite_eq_right hD, ite_eq_left h6]
  rw [hDX]
  have hss : ({2} : Finset (Fin 3)) \ {2} = ∅ := by decide
  rw [hss]

theorem g4Dir_edge {u w : Fin 4}
    (h : (u, w) = (0, 1) ∨ (u, w) = (1, 3) ∨ (u, w) = (2, 3)) :
    u.val < w.val := by
  rcases h with h | h | h <;> rw [Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> decide

theorem g4TransGen {u w : Fin 4}
    (h : Relation.TransGen
      (fun u w : Fin 4 => (u, w) = (0, 1) ∨ (u, w) = (1, 3) ∨ (u, w) = (2, 3))
      u w) :
    u.val < w.val := by
  induction h with
  | single hd => exact g4Dir_edge hd
  | tail _ hd ih => have h2 := g4Dir_edge hd; omega

theorem g4ReflTransGen_le {u w : Fin 4}
    (h : Relation.ReflTransGen
      (fun u w : Fin 4 => (u, w) = (0, 1) ∨ (u, w) = (1, 3) ∨ (u, w) = (2, 3))
      u w) :
    u.val ≤ w.val := by
  induction h with
  | refl => exact le_refl _
  | tail _ hd ih => have h2 := g4Dir_edge hd; omega

theorem g4Bidir_adj {a b : Fin 4}
    (h : (SimpleGraph.fromRel (fun u w : Fin 4 => (u, w) = (1, 2))).Adj a b) :
    (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by
  rw [SimpleGraph.fromRel_adj] at h
  obtain ⟨-, h | h⟩ := h
  · left; rw [Prod.mk.injEq] at h; exact h
  · right; rw [Prod.mk.injEq] at h; exact ⟨h.2, h.1⟩

def G4 : ADMG (Fin 4) where
  dir u w := (u, w) = (0, 1) ∨ (u, w) = (1, 3) ∨ (u, w) = (2, 3)
  bidir := SimpleGraph.fromRel fun u w => (u, w) = (1, 2)
  acyclic := by
    show ∀ v : Fin 4,
      ¬ Relation.TransGen
        (fun u w : Fin 4 => (u, w) = (0, 1) ∨ (u, w) = (1, 3) ∨ (u, w) = (2, 3)) v v
    intro v h
    exact absurd (g4TransGen h) (lt_irrefl _)

def g4order : Fin 4 ≃ Fin (Fintype.card (Fin 4)) := Equiv.refl _

theorem g4InduceDir {D : Finset (Fin 4)} {a b : Fin 4}
    (h : (G4.induce ↑D).dir a b) :
    a ∈ (↑D : Set (Fin 4)) ∧ b ∈ ↑D ∧ G4.dir a b := h

theorem g4Dir_eq {a b : Fin 4} (h : G4.dir a b) :
    (a, b) = (0, 1) ∨ (a, b) = (1, 3) ∨ (a, b) = (2, 3) := h

theorem g4InduceBidir_adj {D : Finset (Fin 4)} {a b : Fin 4}
    (h : (G4.induce ↑D).bidir.Adj a b) :
    a ∈ (↑D : Set (Fin 4)) ∧ b ∈ ↑D ∧ ((a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)) := by
  have hb : G4.bidir = SimpleGraph.fromRel (fun u w : Fin 4 => (u, w) = (1, 2)) :=
    rfl
  have h' : (SimpleGraph.fromRel
      (fun x y : Fin 4 => x ∈ (↑D : Set (Fin 4)) ∧ y ∈ ↑D ∧ G4.bidir.Adj x y)).Adj
      a b := h
  rw [SimpleGraph.fromRel_adj, hb] at h'
  obtain ⟨-, h' | h'⟩ := h'
  · obtain ⟨ham, hbm, hadj⟩ := h'
    exact ⟨ham, hbm, g4Bidir_adj hadj⟩
  · obtain ⟨hbm, ham, hadj⟩ := h'
    obtain h'' | h'' := g4Bidir_adj hadj
    · exact ⟨ham, hbm, Or.inr ⟨h''.2, h''.1⟩⟩
    · exact ⟨ham, hbm, Or.inl ⟨h''.2, h''.1⟩⟩

theorem g4dir01 : G4.dir 0 1 := by
  show ((0, 1) : Fin 4 × Fin 4) = (0, 1) ∨ (0, 1) = (1, 3) ∨ (0, 1) = (2, 3)
  exact Or.inl rfl

theorem g4dir13 : G4.dir 1 3 := by
  show ((1, 3) : Fin 4 × Fin 4) = (0, 1) ∨ (1, 3) = (1, 3) ∨ (1, 3) = (2, 3)
  exact Or.inr (Or.inl rfl)

theorem g4dir23 : G4.dir 2 3 := by
  show ((2, 3) : Fin 4 × Fin 4) = (0, 1) ∨ (2, 3) = (1, 3) ∨ (2, 3) = (2, 3)
  exact Or.inr (Or.inr rfl)

theorem g4AncIn_univ3 : G4.ancIn Finset.univ {3} = Finset.univ := by
  ext x
  rw [synAncIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  have h01 : (G4.induce ↑(Finset.univ : Finset (Fin 4))).dir 0 1 :=
    ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), g4dir01⟩
  have h13 : (G4.induce ↑(Finset.univ : Finset (Fin 4))).dir 1 3 :=
    ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), g4dir13⟩
  have h23 : (G4.induce ↑(Finset.univ : Finset (Fin 4))).dir 2 3 :=
    ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), g4dir23⟩
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · intro h; exact h.1
    · intro _
      refine ⟨Finset.mem_univ _, 3, by decide, ?_⟩
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single h01)
        (Relation.ReflTransGen.single h13)
  · constructor
    · intro h; exact h.1
    · intro _
      refine ⟨Finset.mem_univ _, 3, by decide, ?_⟩
      exact Relation.ReflTransGen.single h13
  · constructor
    · intro h; exact h.1
    · intro _
      refine ⟨Finset.mem_univ _, 3, by decide, ?_⟩
      exact Relation.ReflTransGen.single h23
  · constructor
    · intro h; exact h.1
    · intro _
      refine ⟨Finset.mem_univ _, 3, by decide, ?_⟩
      exact Relation.ReflTransGen.refl

theorem g4AncCut_univ03 : G4.ancCut Finset.univ {0} {3} = Finset.univ := by
  ext x
  rw [synAncCut_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  have h01 : (G4.induce ↑(Finset.univ : Finset (Fin 4))).dir 0 1 ∧
      (1 : Fin 4) ∉ ({0} : Finset (Fin 4)) := by
    refine ⟨⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide),
      g4dir01⟩, by decide⟩
  have h13 : (G4.induce ↑(Finset.univ : Finset (Fin 4))).dir 1 3 ∧
      (3 : Fin 4) ∉ ({0} : Finset (Fin 4)) := by
    refine ⟨⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide),
      g4dir13⟩, by decide⟩
  have h23 : (G4.induce ↑(Finset.univ : Finset (Fin 4))).dir 2 3 ∧
      (3 : Fin 4) ∉ ({0} : Finset (Fin 4)) := by
    refine ⟨⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide),
      g4dir23⟩, by decide⟩
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · intro h; exact h.1
    · intro _
      refine ⟨Finset.mem_univ _, 3, by decide, ?_⟩
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single h01)
        (Relation.ReflTransGen.single h13)
  · constructor
    · intro h; exact h.1
    · intro _
      refine ⟨Finset.mem_univ _, 3, by decide, ?_⟩
      exact Relation.ReflTransGen.single h13
  · constructor
    · intro h; exact h.1
    · intro _
      refine ⟨Finset.mem_univ _, 3, by decide, ?_⟩
      exact Relation.ReflTransGen.single h23
  · constructor
    · intro h; exact h.1
    · intro _
      refine ⟨Finset.mem_univ _, 3, by decide, ?_⟩
      exact Relation.ReflTransGen.refl

theorem g4AncIn_univ12 : G4.ancIn Finset.univ {1, 2} = {0, 1, 2} := by
  ext x
  rw [synAncIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  have h01 : (G4.induce ↑(Finset.univ : Finset (Fin 4))).dir 0 1 :=
    ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), g4dir01⟩
  have hle : (G4.induce ↑(Finset.univ : Finset (Fin 4))).dir ≤
      (fun u w : Fin 4 => (u, w) = (0, 1) ∨ (u, w) = (1, 3) ∨ (u, w) = (2, 3)) := by
    intro a b hab
    exact g4Dir_eq (g4InduceDir hab).2.2
  rcases hx4 with rfl | rfl | rfl | rfl
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
    · intro _; decide
    · intro _
      refine ⟨Finset.mem_univ _, 2, by decide, ?_⟩
      exact Relation.ReflTransGen.refl
  · constructor
    · rintro ⟨-, y, hy, hr⟩
      have hle' := g4ReflTransGen_le ((Relation.ReflTransGen.mono hle) _ _ hr)
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> exact absurd hle' (by decide)
    · intro hcon; exact absurd hcon (by decide)

theorem g4AncIn_01212 : G4.ancIn {0, 1, 2} {1, 2} = {0, 1, 2} := by
  ext x
  rw [synAncIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  have h01 : (G4.induce ↑(({0, 1, 2} : Finset (Fin 4)))).dir 0 1 :=
    ⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide), g4dir01⟩
  rcases hx4 with rfl | rfl | rfl | rfl
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
    · intro h; exact h.1
    · intro _
      refine ⟨by decide, 2, by decide, ?_⟩
      exact Relation.ReflTransGen.refl
  · constructor
    · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
    · intro hcon; exact absurd hcon (by decide)

theorem g4CutConf0 {x : Fin 4}
    (h : Relation.ReflTransGen
      (fun a b => (G4.induce ↑(Finset.univ : Finset (Fin 4))).dir a b ∧
        b ∉ ({0, 1, 2} : Finset (Fin 4))) 0 x) :
    x = 0 := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    subst ih
    have hd := g4Dir_eq (g4InduceDir hstep.1).2.2
    rcases hd with hd | hd | hd <;> rw [Prod.mk.injEq] at hd
    · obtain ⟨-, hb⟩ := hd
      subst hb
      exact absurd hstep.2 (by decide)
    · exact absurd hd.1 (by decide)
    · exact absurd hd.1 (by decide)

theorem g4AncCut_univ0123 :
    G4.ancCut Finset.univ {0, 1, 2} {3} = {1, 2, 3} := by
  ext x
  rw [synAncCut_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  have h13 : (G4.induce ↑(Finset.univ : Finset (Fin 4))).dir 1 3 ∧
      (3 : Fin 4) ∉ ({0, 1, 2} : Finset (Fin 4)) := by
    refine ⟨⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide),
      g4dir13⟩, by decide⟩
  have h23 : (G4.induce ↑(Finset.univ : Finset (Fin 4))).dir 2 3 ∧
      (3 : Fin 4) ∉ ({0, 1, 2} : Finset (Fin 4)) := by
    refine ⟨⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide),
      g4dir23⟩, by decide⟩
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · rintro ⟨-, y, hy, hr⟩
      have hy3 : y = 3 := Finset.mem_singleton.mp hy
      subst hy3
      have h0 := g4CutConf0 hr
      exact absurd h0 (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · intro _; decide
    · intro _
      refine ⟨Finset.mem_univ _, 3, by decide, ?_⟩
      exact Relation.ReflTransGen.single h13
  · constructor
    · intro _; decide
    · intro _
      refine ⟨Finset.mem_univ _, 3, by decide, ?_⟩
      exact Relation.ReflTransGen.single h23
  · constructor
    · intro _; decide
    · intro _
      refine ⟨Finset.mem_univ _, 3, by decide, ?_⟩
      exact Relation.ReflTransGen.refl

theorem g4AncCut_012012 : G4.ancCut {0, 1, 2} {0} {1, 2} = {0, 1, 2} := by
  ext x
  rw [synAncCut_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  have h01 : (G4.induce ↑(({0, 1, 2} : Finset (Fin 4)))).dir 0 1 ∧
      (1 : Fin 4) ∉ ({0} : Finset (Fin 4)) := by
    refine ⟨⟨Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide),
      g4dir01⟩, by decide⟩
  rcases hx4 with rfl | rfl | rfl | rfl
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
    · intro h; exact h.1
    · intro _
      refine ⟨by decide, 2, by decide, ?_⟩
      exact Relation.ReflTransGen.refl
  · constructor
    · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
    · intro hcon; exact absurd hcon (by decide)

theorem g4bidir12 : G4.bidir.Adj 1 2 := by
  show (SimpleGraph.fromRel (fun u w : Fin 4 => (u, w) = (1, 2))).Adj 1 2
  rw [SimpleGraph.fromRel_adj]
  exact ⟨by decide, Or.inl rfl⟩

theorem g4bidir21 : G4.bidir.Adj 2 1 := by
  show (SimpleGraph.fromRel (fun u w : Fin 4 => (u, w) = (1, 2))).Adj 2 1
  rw [SimpleGraph.fromRel_adj]
  exact ⟨by decide, Or.inr rfl⟩

theorem g4Reach12 {D : Finset (Fin 4)} {x : Fin 4}
    (h : (G4.induce ↑D).bidir.Reachable 1 x) : x = 1 ∨ x = 2 := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hadj _ =>
    obtain ⟨-, -, h | h⟩ := g4InduceBidir_adj hadj
    · exact Or.inr h.2
    · exact Or.inl h.2

theorem g4Reach21 {D : Finset (Fin 4)} {x : Fin 4}
    (h : (G4.induce ↑D).bidir.Reachable 2 x) : x = 1 ∨ x = 2 := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inr rfl
  | tail _ hadj _ =>
    obtain ⟨-, -, h | h⟩ := g4InduceBidir_adj hadj
    · exact Or.inr h.2
    · exact Or.inl h.2

theorem g4Reach0 {D : Finset (Fin 4)} {x : Fin 4}
    (h : (G4.induce ↑D).bidir.Reachable 0 x) : x = 0 := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ hadj ih =>
    subst ih
    obtain ⟨-, -, h | h⟩ := g4InduceBidir_adj hadj
    · exact absurd h.1 (by decide)
    · exact absurd h.1 (by decide)

theorem g4Reach3 {D : Finset (Fin 4)} {x : Fin 4}
    (h : (G4.induce ↑D).bidir.Reachable 3 x) : x = 3 := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ hadj ih =>
    subst ih
    obtain ⟨-, -, h | h⟩ := g4InduceBidir_adj hadj
    · exact absurd h.1 (by decide)
    · exact absurd h.1 (by decide)

theorem g4InduceAdj12 {D : Finset (Fin 4)} (h1 : (1 : Fin 4) ∈ D)
    (h2 : (2 : Fin 4) ∈ D) : (G4.induce ↑D).bidir.Adj 1 2 := by
  show (SimpleGraph.fromRel (fun x y : Fin 4 =>
    x ∈ (↑D : Set (Fin 4)) ∧ y ∈ ↑D ∧ G4.bidir.Adj x y)).Adj 1 2
  rw [SimpleGraph.fromRel_adj]
  exact ⟨by decide,
    Or.inl ⟨Finset.mem_coe.mpr h1, Finset.mem_coe.mpr h2, g4bidir12⟩⟩

theorem g4InduceAdj21 {D : Finset (Fin 4)} (h2 : (2 : Fin 4) ∈ D)
    (h1 : (1 : Fin 4) ∈ D) : (G4.induce ↑D).bidir.Adj 2 1 := by
  show (SimpleGraph.fromRel (fun x y : Fin 4 =>
    x ∈ (↑D : Set (Fin 4)) ∧ y ∈ ↑D ∧ G4.bidir.Adj x y)).Adj 2 1
  rw [SimpleGraph.fromRel_adj]
  exact ⟨by decide,
    Or.inl ⟨Finset.mem_coe.mpr h2, Finset.mem_coe.mpr h1, g4bidir21⟩⟩

theorem g4CompIn_mem (D : Finset (Fin 4)) (v x : Fin 4) :
    x ∈ G4.compIn D v ↔ x ∈ D ∧ (G4.induce ↑D).bidir.Reachable v x := by
  rw [synCompIn_mem, (G4.induce ↑D).mem_cComponent_iff]

theorem g4CompIn_123_1 : G4.compIn {1, 2, 3} 1 = {1, 2} := by
  ext x
  rw [g4CompIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · intro _; decide
    · intro _; exact ⟨by decide, SimpleGraph.Reachable.rfl⟩
  · constructor
    · intro _; decide
    · intro _
      exact ⟨by decide, (g4InduceAdj12 (by decide) (by decide)).reachable⟩
  · constructor
    · rintro ⟨-, hr⟩
      have h := g4Reach12 hr
      rcases h with h | h <;> exact absurd h (by decide)
    · intro hcon; exact absurd hcon (by decide)

theorem g4CompIn_123_2 : G4.compIn {1, 2, 3} 2 = {1, 2} := by
  ext x
  rw [g4CompIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · intro _; decide
    · intro _
      exact ⟨by decide, (g4InduceAdj21 (by decide) (by decide)).reachable⟩
  · constructor
    · intro _; decide
    · intro _; exact ⟨by decide, SimpleGraph.Reachable.rfl⟩
  · constructor
    · rintro ⟨-, hr⟩
      have h := g4Reach21 hr
      rcases h with h | h <;> exact absurd h (by decide)
    · intro hcon; exact absurd hcon (by decide)

theorem g4CompIn_123_3 : G4.compIn {1, 2, 3} 3 = {3} := by
  ext x
  rw [g4CompIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · rintro ⟨-, hr⟩
      have h := g4Reach3 hr
      exact absurd h (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · rintro ⟨-, hr⟩
      have h := g4Reach3 hr
      exact absurd h (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · intro _; decide
    · intro _; exact ⟨by decide, SimpleGraph.Reachable.rfl⟩

theorem g4CompIn_12_1 : G4.compIn {1, 2} 1 = {1, 2} := by
  ext x
  rw [g4CompIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · intro _; decide
    · intro _; exact ⟨by decide, SimpleGraph.Reachable.rfl⟩
  · constructor
    · intro _; decide
    · intro _
      exact ⟨by decide, (g4InduceAdj12 (by decide) (by decide)).reachable⟩
  · constructor
    · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
    · intro hcon; exact absurd hcon (by decide)

theorem g4CompIn_12_2 : G4.compIn {1, 2} 2 = {1, 2} := by
  ext x
  rw [g4CompIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · intro _; decide
    · intro _
      exact ⟨by decide, (g4InduceAdj21 (by decide) (by decide)).reachable⟩
  · constructor
    · intro _; decide
    · intro _; exact ⟨by decide, SimpleGraph.Reachable.rfl⟩
  · constructor
    · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
    · intro hcon; exact absurd hcon (by decide)

theorem g4CompIn_012_0 : G4.compIn {0, 1, 2} 0 = {0} := by
  ext x
  rw [g4CompIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · intro _; decide
    · intro _; exact ⟨by decide, SimpleGraph.Reachable.rfl⟩
  · constructor
    · rintro ⟨-, hr⟩
      have h := g4Reach0 hr
      exact absurd h (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · rintro ⟨-, hr⟩
      have h := g4Reach0 hr
      exact absurd h (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
    · intro hcon; exact absurd hcon (by decide)

theorem g4CompIn_012_1 : G4.compIn {0, 1, 2} 1 = {1, 2} := by
  ext x
  rw [g4CompIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · rintro ⟨-, hr⟩
      have h := g4Reach12 hr
      rcases h with h | h <;> exact absurd h (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · intro _; decide
    · intro _; exact ⟨by decide, SimpleGraph.Reachable.rfl⟩
  · constructor
    · intro _; decide
    · intro _
      exact ⟨by decide, (g4InduceAdj12 (by decide) (by decide)).reachable⟩
  · constructor
    · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
    · intro hcon; exact absurd hcon (by decide)

theorem g4CompIn_012_2 : G4.compIn {0, 1, 2} 2 = {1, 2} := by
  ext x
  rw [g4CompIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · rintro ⟨-, hr⟩
      have h := g4Reach21 hr
      rcases h with h | h <;> exact absurd h (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · intro _; decide
    · intro _
      exact ⟨by decide, (g4InduceAdj21 (by decide) (by decide)).reachable⟩
  · constructor
    · intro _; decide
    · intro _; exact ⟨by decide, SimpleGraph.Reachable.rfl⟩
  · constructor
    · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
    · intro hcon; exact absurd hcon (by decide)

theorem g4CompIn_3_3 : G4.compIn {3} 3 = {3} := by
  ext x
  rw [g4CompIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · rintro ⟨hmem, -⟩; exact absurd hmem (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · intro _; decide
    · intro _; exact ⟨by decide, SimpleGraph.Reachable.rfl⟩

theorem g4CompIn_univ_0 : G4.compIn Finset.univ 0 = {0} := by
  ext x
  rw [g4CompIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · intro _; decide
    · intro _; exact ⟨Finset.mem_univ _, SimpleGraph.Reachable.rfl⟩
  · constructor
    · rintro ⟨-, hr⟩
      have h := g4Reach0 hr
      exact absurd h (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · rintro ⟨-, hr⟩
      have h := g4Reach0 hr
      exact absurd h (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · rintro ⟨-, hr⟩
      have h := g4Reach0 hr
      exact absurd h (by decide)
    · intro hcon; exact absurd hcon (by decide)

theorem g4CompIn_univ_1 : G4.compIn Finset.univ 1 = {1, 2} := by
  ext x
  rw [g4CompIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · rintro ⟨-, hr⟩
      have h := g4Reach12 hr
      rcases h with h | h <;> exact absurd h (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · intro _; decide
    · intro _; exact ⟨Finset.mem_univ _, SimpleGraph.Reachable.rfl⟩
  · constructor
    · intro _; decide
    · intro _
      exact ⟨Finset.mem_univ _, (g4InduceAdj12 (by decide) (by decide)).reachable⟩
  · constructor
    · rintro ⟨-, hr⟩
      have h := g4Reach12 hr
      rcases h with h | h <;> exact absurd h (by decide)
    · intro hcon; exact absurd hcon (by decide)

theorem g4CompIn_univ_2 : G4.compIn Finset.univ 2 = {1, 2} := by
  ext x
  rw [g4CompIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · rintro ⟨-, hr⟩
      have h := g4Reach21 hr
      rcases h with h | h <;> exact absurd h (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · intro _; decide
    · intro _
      exact ⟨Finset.mem_univ _, (g4InduceAdj21 (by decide) (by decide)).reachable⟩
  · constructor
    · intro _; decide
    · intro _; exact ⟨Finset.mem_univ _, SimpleGraph.Reachable.rfl⟩
  · constructor
    · rintro ⟨-, hr⟩
      have h := g4Reach21 hr
      rcases h with h | h <;> exact absurd h (by decide)
    · intro hcon; exact absurd hcon (by decide)

theorem g4CompIn_univ_3 : G4.compIn Finset.univ 3 = {3} := by
  ext x
  rw [g4CompIn_mem]
  have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> decide
  rcases hx4 with rfl | rfl | rfl | rfl
  · constructor
    · rintro ⟨-, hr⟩
      have h := g4Reach3 hr
      exact absurd h (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · rintro ⟨-, hr⟩
      have h := g4Reach3 hr
      exact absurd h (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · rintro ⟨-, hr⟩
      have h := g4Reach3 hr
      exact absurd h (by decide)
    · intro hcon; exact absurd hcon (by decide)
  · constructor
    · intro _; decide
    · intro _; exact ⟨Finset.mem_univ _, SimpleGraph.Reachable.rfl⟩

theorem g4CComp_123 : G4.cComponentsIn {1, 2, 3} = {{1, 2}, {3}} := by
  ext S
  simp only [cComponentsIn, Finset.mem_image]
  constructor
  · rintro ⟨v, hvD, rfl⟩
    have hx4 : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by fin_cases v <;> decide
    rcases hx4 with rfl | rfl | rfl | rfl
    · exact absurd hvD (by decide)
    · rw [g4CompIn_123_1]; decide
    · rw [g4CompIn_123_2]; decide
    · rw [g4CompIn_123_3]; decide
  · intro hS
    rw [Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl
    · exact ⟨1, by decide, g4CompIn_123_1⟩
    · exact ⟨3, by decide, g4CompIn_123_3⟩

theorem g4CComp_12 : G4.cComponentsIn {1, 2} = {{1, 2}} := by
  ext S
  simp only [cComponentsIn, Finset.mem_image]
  constructor
  · rintro ⟨v, hvD, rfl⟩
    have hx4 : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by fin_cases v <;> decide
    rcases hx4 with rfl | rfl | rfl | rfl
    · exact absurd hvD (by decide)
    · rw [g4CompIn_12_1]; decide
    · rw [g4CompIn_12_2]; decide
    · exact absurd hvD (by decide)
  · intro hS
    rw [Finset.mem_singleton] at hS
    subst hS
    exact ⟨1, by decide, g4CompIn_12_1⟩

theorem g4CComp_012 : G4.cComponentsIn {0, 1, 2} = {{0}, {1, 2}} := by
  ext S
  simp only [cComponentsIn, Finset.mem_image]
  constructor
  · rintro ⟨v, hvD, rfl⟩
    have hx4 : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by fin_cases v <;> decide
    rcases hx4 with rfl | rfl | rfl | rfl
    · rw [g4CompIn_012_0]; decide
    · rw [g4CompIn_012_1]; decide
    · rw [g4CompIn_012_2]; decide
    · exact absurd hvD (by decide)
  · intro hS
    rw [Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl
    · exact ⟨0, by decide, g4CompIn_012_0⟩
    · exact ⟨1, by decide, g4CompIn_012_1⟩

theorem g4CComp_3 : G4.cComponentsIn {3} = {{3}} := by
  ext S
  simp only [cComponentsIn, Finset.mem_image]
  constructor
  · rintro ⟨v, hvD, rfl⟩
    have hx4 : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by fin_cases v <;> decide
    rcases hx4 with rfl | rfl | rfl | rfl
    · exact absurd hvD (by decide)
    · exact absurd hvD (by decide)
    · exact absurd hvD (by decide)
    · rw [g4CompIn_3_3]; decide
  · intro hS
    rw [Finset.mem_singleton] at hS
    subst hS
    exact ⟨3, by decide, g4CompIn_3_3⟩

theorem g4CComp_univ : G4.cComponentsIn Finset.univ = {{0}, {1, 2}, {3}} := by
  ext S
  simp only [cComponentsIn, Finset.mem_image]
  constructor
  · rintro ⟨v, hvD, rfl⟩
    have hx4 : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by fin_cases v <;> decide
    rcases hx4 with rfl | rfl | rfl | rfl
    · rw [g4CompIn_univ_0]; decide
    · rw [g4CompIn_univ_1]; decide
    · rw [g4CompIn_univ_2]; decide
    · rw [g4CompIn_univ_3]; decide
  · intro hS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl
    · exact ⟨0, Finset.mem_univ _, g4CompIn_univ_0⟩
    · exact ⟨1, Finset.mem_univ _, g4CompIn_univ_1⟩
    · exact ⟨3, Finset.mem_univ _, g4CompIn_univ_3⟩

theorem g4ToList123 :
    (({{1, 2}, {3}} : Finset (Finset (Fin 4)))).toList = [{1, 2}, {3}] ∨
    (({{1, 2}, {3}} : Finset (Finset (Fin 4)))).toList = [{3}, {1, 2}] := by
  have hcard : (({{1, 2}, {3}} : Finset (Finset (Fin 4)))).card = 2 := by decide
  have hlen : (({{1, 2}, {3}} : Finset (Finset (Fin 4)))).toList.length = 2 := by
    rw [Finset.length_toList, hcard]
  obtain ⟨A, B, hAB⟩ := List.length_eq_two.mp hlen
  have hnodup : [A, B].Nodup := by rw [← hAB]; exact Finset.nodup_toList _
  have hmemA : A ∈ ({{1, 2}, {3}} : Finset (Finset (Fin 4))) := by
    rw [← Finset.mem_toList, hAB]; simp
  have hmemB : B ∈ ({{1, 2}, {3}} : Finset (Finset (Fin 4))) := by
    rw [← Finset.mem_toList, hAB]; simp
  have hne : A ≠ B := by
    have hn := (List.nodup_cons.mp hnodup).1
    intro hcon
    subst hcon
    exact hn (by simp)
  rw [Finset.mem_insert, Finset.mem_singleton] at hmemA hmemB
  rcases hmemA with rfl | rfl <;> rcases hmemB with rfl | rfl
  · exact absurd rfl hne
  · exact Or.inl hAB
  · exact Or.inr hAB
  · exact absurd rfl hne

theorem g4Call12b :
    G4.idRec g4order {1, 2} {0} {0, 1, 2} (IdExpr.sum {3} IdExpr.obs)
      = Except.ok (IdExpr.sum ∅
        (condChain g4order {0, 1, 2} {1, 2} (IdExpr.sum {3} IdExpr.obs))) := by
  rw [idRec.eq_def]
  rw [ite_eq_right (by decide : ({0} : Finset (Fin 4)) ≠ ∅)]
  have hA : ¬G4.ancIn {0, 1, 2} {1, 2} ≠ {0, 1, 2} := by
    rw [g4AncIn_01212]; exact fun h => h rfl
  simp only [dite_eq_right hA]
  have hW : ¬((((({0, 1, 2} : Finset (Fin 4)) \ {0}) \
      G4.ancCut {0, 1, 2} {0} {1, 2}).Nonempty)) := by
    rw [g4AncCut_012012,
      show ((({0, 1, 2} : Finset (Fin 4)) \ {0}) \ {0, 1, 2}) = ∅ from by decide]
    decide
  simp only [dite_eq_right hW]
  have hT : ¬((({0, 1, 2} : Finset (Fin 4)) \ {0}) ∉
      G4.cComponentsIn ((({0, 1, 2} : Finset (Fin 4)) \ {0}))) := by
    rw [show ((({0, 1, 2} : Finset (Fin 4)) \ {0})) = {1, 2} from by decide,
      g4CComp_12]
    decide
  simp only [dite_eq_right hT]
  have hD : ({0, 1, 2} : Finset (Fin 4)) ∉ G4.cComponentsIn {0, 1, 2} := by
    rw [g4CComp_012]; decide
  simp only [dite_eq_right hD]
  have h6 : ((({0, 1, 2} : Finset (Fin 4)) \ {0})) ∈
      G4.cComponentsIn {0, 1, 2} := by
    rw [show ((({0, 1, 2} : Finset (Fin 4)) \ {0})) = {1, 2} from by decide,
      g4CComp_012]
    decide
  rw [ite_eq_left h6]
  rw [show ((({0, 1, 2} : Finset (Fin 4)) \ {0})) = {1, 2} from by decide,
    show ((({1, 2} : Finset (Fin 4)) \ {1, 2})) = ∅ from by decide]

theorem g4Call12 :
    G4.idRec g4order {1, 2} {0, 3} Finset.univ IdExpr.obs
      = Except.ok (IdExpr.sum ∅
        (condChain g4order {0, 1, 2} {1, 2} (IdExpr.sum {3} IdExpr.obs))) := by
  rw [idRec.eq_def]
  rw [ite_eq_right (by decide : ({0, 3} : Finset (Fin 4)) ≠ ∅)]
  have hA : G4.ancIn Finset.univ {1, 2} ≠ Finset.univ := by
    rw [g4AncIn_univ12]; decide
  simp only [dite_eq_left hA]
  rw [g4AncIn_univ12,
    show ((({0, 3} : Finset (Fin 4)) ∩ {0, 1, 2})) = {0} from by decide,
    show (Finset.univ \ (({0, 1, 2} : Finset (Fin 4)))) = {3} from by decide]
  exact g4Call12b

theorem g4Call3 :
    G4.idRec g4order {3} {0, 1, 2} Finset.univ IdExpr.obs
      = Except.ok (IdExpr.sum ∅
        (condChain g4order Finset.univ {3} IdExpr.obs)) := by
  rw [idRec.eq_def]
  rw [ite_eq_right (by decide : ({0, 1, 2} : Finset (Fin 4)) ≠ ∅)]
  have hA : ¬G4.ancIn Finset.univ {3} ≠ Finset.univ := by
    rw [g4AncIn_univ3]; exact fun h => h rfl
  simp only [dite_eq_right hA]
  have hW : ¬(((((Finset.univ \ {0, 1, 2}) \
      G4.ancCut Finset.univ {0, 1, 2} {3}).Nonempty))) := by
    rw [g4AncCut_univ0123,
      show ((Finset.univ \ (({0, 1, 2} : Finset (Fin 4)))) \ {1, 2, 3}) = ∅
        from by decide]
    decide
  simp only [dite_eq_right hW]
  have hT : ¬((Finset.univ \ {0, 1, 2}) ∉
      G4.cComponentsIn (Finset.univ \ {0, 1, 2})) := by
    rw [show (Finset.univ \ (({0, 1, 2} : Finset (Fin 4)))) = {3} from by decide,
      g4CComp_3]
    decide
  simp only [dite_eq_right hT]
  have hD : Finset.univ ∉ G4.cComponentsIn Finset.univ := by
    rw [g4CComp_univ]; decide
  simp only [dite_eq_right hD]
  have h6 : (Finset.univ \ {0, 1, 2}) ∈ G4.cComponentsIn Finset.univ := by
    rw [show (Finset.univ \ (({0, 1, 2} : Finset (Fin 4)))) = {3} from by decide,
      g4CComp_univ]
    decide
  rw [ite_eq_left h6]
  rw [show (Finset.univ \ (({0, 1, 2} : Finset (Fin 4)))) = {3} from by decide,
    show ((({3} : Finset (Fin 4)) \ {3})) = ∅ from by decide]

theorem g4ID_line4_succ :
    G4.ID g4order {3} {0}
      = Except.ok (IdExpr.sum {1, 2} (IdExpr.prodList
        [IdExpr.sum ∅
          (condChain g4order {0, 1, 2} {1, 2} (IdExpr.sum {3} IdExpr.obs)),
         IdExpr.sum ∅ (condChain g4order Finset.univ {3} IdExpr.obs)]))
    ∨ G4.ID g4order {3} {0}
      = Except.ok (IdExpr.sum {1, 2} (IdExpr.prodList
        [IdExpr.sum ∅ (condChain g4order Finset.univ {3} IdExpr.obs),
         IdExpr.sum ∅
          (condChain g4order {0, 1, 2} {1, 2} (IdExpr.sum {3} IdExpr.obs))])) := by
  simp only [ID]
  rw [idRec.eq_def]
  rw [ite_eq_right (by decide : ({0} : Finset (Fin 4)) ≠ ∅)]
  have hA : ¬G4.ancIn Finset.univ {3} ≠ Finset.univ := by
    rw [g4AncIn_univ3]; exact fun h => h rfl
  simp only [dite_eq_right hA]
  have hW : ¬(((((Finset.univ \ {0}) \
      G4.ancCut Finset.univ {0} {3}).Nonempty))) := by
    rw [g4AncCut_univ03,
      show ((Finset.univ \ (({0} : Finset (Fin 4)))) \ Finset.univ) = ∅
        from by decide]
    decide
  simp only [dite_eq_right hW]
  have hT : (Finset.univ \ {0}) ∉ G4.cComponentsIn (Finset.univ \ {0}) := by
    rw [show (Finset.univ \ (({0} : Finset (Fin 4)))) = {1, 2, 3} from by decide,
      g4CComp_123]
    decide
  simp only [dite_eq_left hT]
  rw [show (Finset.univ \ (({0} : Finset (Fin 4)))) = {1, 2, 3} from by decide,
    g4CComp_123,
    show (Finset.univ \ ((({3} : Finset (Fin 4)) ∪ {0}))) = {1, 2} from by decide]
  rcases g4ToList123 with hto | hto <;> rw [hto]
  · left
    simp only [List.attach, List.attachWith, List.pmap_cons, List.pmap_nil,
      List.mapM_cons, List.mapM_nil,
      show (Finset.univ \ ((({1, 2} : Finset (Fin 4))))) = {0, 3} from by decide,
      show (Finset.univ \ ((({3} : Finset (Fin 4))))) = {0, 1, 2} from by decide,
      g4Call12, g4Call3, pure, Except.pure, bind, Except.bind]
  · right
    simp only [List.attach, List.attachWith, List.pmap_cons, List.pmap_nil,
      List.mapM_cons, List.mapM_nil,
      show (Finset.univ \ ((({1, 2} : Finset (Fin 4))))) = {0, 3} from by decide,
      show (Finset.univ \ ((({3} : Finset (Fin 4))))) = {0, 1, 2} from by decide,
      g4Call12, g4Call3, pure, Except.pure, bind, Except.bind]

theorem prodList_eval_pair_comm {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α]
    (e1 e2 : IdExpr V) (p : (V → α) → ℝ) (x : V → α) :
    (IdExpr.prodList [e1, e2]).eval p x = (IdExpr.prodList [e2, e1]).eval p x := by
  simp [IdExpr.prodList, IdExpr.eval]
  ring

theorem g4ID_line4_eval {α : Type*} [Fintype α] (p : (Fin 4 → α) → ℝ) :
    (G4.ID g4order {3} {0}).map (IdExpr.eval p)
      = Except.ok ((IdExpr.sum {1, 2} (IdExpr.prodList
        [IdExpr.sum ∅ (condChain g4order {0, 1, 2} {1, 2} (IdExpr.sum {3} IdExpr.obs)),
         IdExpr.sum ∅ (condChain g4order Finset.univ {3} IdExpr.obs)])).eval p) := by
  rcases g4ID_line4_succ with h | h
  · rw [h]
    rfl
  · rw [h]
    have hfun : (IdExpr.prodList
            [IdExpr.sum ∅ (condChain g4order {0, 1, 2} {1, 2} (IdExpr.sum {3} IdExpr.obs)),
             IdExpr.sum ∅ (condChain g4order Finset.univ {3} IdExpr.obs)]).eval p
          = (IdExpr.prodList
            [IdExpr.sum ∅ (condChain g4order Finset.univ {3} IdExpr.obs),
             IdExpr.sum ∅
              (condChain g4order {0, 1, 2} {1, 2} (IdExpr.sum {3} IdExpr.obs))]).eval p :=
        funext fun x => prodList_eval_pair_comm _ _ p x
    simp only [Except.map, IdExpr.eval]
    rw [hfun]

end Cslib.MachineLearning.GraphicalModels.ADMG
