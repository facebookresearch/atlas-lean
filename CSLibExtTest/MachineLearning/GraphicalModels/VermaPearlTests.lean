/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Kiezun
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.VermaPearl
import Mathlib.Tactic.FinCases

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset BayesianDirichlet Convexity

def chainPa : Fin 3 → Finset (Fin 3) := ![∅, {0}, {1}]

def forkPa : Fin 3 → Finset (Fin 3) := ![{1}, ∅, {1}]

theorem chainPa_apply : chainPa 0 = ∅ ∧ chainPa 1 = {0} ∧ chainPa 2 = {1} := by
  decide

theorem reversal_chainPa :
    Function.update (Function.update chainPa 1 (chainPa 0)) 0 (insert 1 (chainPa 0)) =
      forkPa := by
  funext v
  fin_cases v <;> decide

theorem chainPa_covered : IsAcyclic chainPa ∧ CoveredReversal chainPa forkPa := by
  constructor
  · intro v hv
    have hsingle : ∀ {a c : Fin 3}, a ∈ chainPa c → a.val < c.val := by
      decide
    have hmono : ∀ {a c : Fin 3},
        Relation.TransGen (fun u w => u ∈ chainPa w) a c → a.val < c.val := by
      intro a c h
      induction h with
      | single hmem => exact hsingle hmem
      | tail _ hmem ih => exact Nat.lt_trans ih (hsingle hmem)
    exact absurd (hmono hv) (lt_irrefl _)
  · exact ⟨0, 1, by decide, by decide, reversal_chainPa.symm⟩

theorem chain_reversal_dsep (X Y Z : Set (Fin 3)) :
    DSeparatedPa chainPa X Y Z ↔ DSeparatedPa forkPa X Y Z :=
  dSeparatedPa_iff_of_coveredReversal chainPa_covered.1 chainPa_covered.2 X Y Z

theorem relabel_chainPa :
    relabel (Equiv.swap (0 : Fin 3) 2) chainPa = ![{1}, {2}, ∅] := by
  funext v
  fin_cases v <;> decide

theorem chainPa_relabel_dsep :
    DSeparatedPa chainPa {0} {2} {1} ↔
      DSeparatedPa (relabel (Equiv.swap (0 : Fin 3) 2) chainPa) {2} {0} {1} := by
  have h := dSeparatedPa_relabel (Pa := chainPa) (X := ({0} : Set (Fin 3)))
    (Y := ({2} : Set (Fin 3))) (Z := ({1} : Set (Fin 3))) (Equiv.swap (0 : Fin 3) 2)
  have hswap0 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := by decide
  have hswap1 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
  have hswap2 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := by decide
  have h0 : (Equiv.swap (0 : Fin 3) 2) '' ({0} : Set (Fin 3)) = {2} := by
    rw [Set.image_singleton, hswap0]
  have h2 : (Equiv.swap (0 : Fin 3) 2) '' ({2} : Set (Fin 3)) = {0} := by
    rw [Set.image_singleton, hswap2]
  have h1 : (Equiv.swap (0 : Fin 3) 2) '' ({1} : Set (Fin 3)) = {1} := by
    rw [Set.image_singleton, hswap1]
  rw [h0, h2, h1] at h
  exact h.symm

noncomputable def chainNet : BayesNet Bool 3 where
  pa := fun k => match k with
    | 0 => ∅
    | 1 => {⟨0, by decide⟩}
    | 2 => {⟨1, by decide⟩}
  cpt := fun _ _ => StdSimplex.single false

theorem chainNet_toPa : chainNet.toPa = chainPa := by
  funext k
  fin_cases k <;> decide

theorem chainNet_bridge :
    chainNet.DSeparated {0} {2} {1} ↔ DSeparatedPa chainPa {0} {2} {1} := by
  rw [BayesNet.dSeparated_iff_dSeparatedPa_toPa, chainNet_toPa]

end Cslib.MachineLearning.GraphicalModels

namespace Cslib.MachineLearning.GraphicalModels

open Finset BayesianDirichlet Convexity

def colliderPa : Fin 3 → Finset (Fin 3) := ![∅, {0, 2}, ∅]

theorem path_shape_of_not_adjacent (Pa : Fin 3 → Finset (Fin 3))
    (h02 : ¬ Adjacent Pa 0 2) (p : List (Fin 3)) :
    IsPathPa Pa 0 2 p → p = [0, 1, 2] := by
  intro h
  obtain ⟨hnodup, hchain, hhead, hlast⟩ := h
  have hlen3 : p.length ≤ 3 := by
    have h := hnodup.length_le_card (α := Fin 3)
    rwa [Fintype.card_fin] at h
  have h02' : (0 : Fin 3) ≠ 2 := by decide
  have hlen2 : 2 ≤ p.length := by
    rcases Nat.lt_or_ge p.length 2 with hlt | hge
    · exfalso
      have h01 : p.length = 0 ∨ p.length = 1 := by omega
      rcases h01 with h0 | h1
      · have hp : p = [] := List.length_eq_zero_iff.mp h0
        subst hp
        simp at hhead
      · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h1
        simp at hhead hlast
        subst hhead
        exact h02' hlast
    · exact hge
  have h23 : p.length = 2 ∨ p.length = 3 := by omega
  rcases h23 with h2 | h3
  · obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp h2
    simp at hhead hlast
    subst hhead
    subst hlast
    rw [List.isChain_cons_cons] at hchain
    exact absurd hchain.1 h02
  · obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp h3
    simp at hhead hlast hnodup
    subst hhead
    subst hlast
    obtain ⟨⟨hab, -⟩, hbc⟩ := hnodup
    have hb : b = 1 := by
      have h0b : b ≠ 0 := Ne.symm hab
      revert h0b hbc
      fin_cases b <;> decide
    subst hb
    rfl

theorem chain_not_sep_empty : ¬ DSeparatedPa chainPa {0} {2} ∅ := by
  intro hsep
  have hpath : IsPathPa chainPa 0 2 [0, 1, 2] := by
    refine ⟨by decide, by unfold Adjacent; decide, by decide, by decide⟩
  have hblocked :=
    hsep 0 (Set.mem_singleton 0) 2 (Set.mem_singleton 2) [0, 1, 2] hpath
  obtain ⟨i, hi, hblock⟩ := hblocked
  simp at hi
  have hi0 : i = 0 := by omega
  subst hi0
  have hblock012 : BlockedAtPa chainPa ∅ 0 1 2 := hblock
  rcases hblock012 with ⟨-, h21, -⟩ | ⟨-, hmem⟩
  · exact (by decide : (2 : Fin 3) ∉ chainPa 1) h21
  · exact Set.notMem_empty 1 hmem

theorem chain_sep_mid : DSeparatedPa chainPa {0} {2} {1} := by
  intro x hx y hy p hp
  rw [Set.mem_singleton_iff] at hx hy
  subst hx hy
  have hshape := path_shape_of_not_adjacent chainPa (by unfold Adjacent; decide) p hp
  subst hshape
  refine ⟨0, by decide, ?_⟩
  show BlockedAtPa chainPa {1} 0 1 2
  refine Or.inr ⟨?_, Set.mem_singleton 1⟩
  intro hcon
  obtain ⟨-, h21⟩ := hcon
  exact (by decide : (2 : Fin 3) ∉ chainPa 1) h21

theorem fork_not_sep_empty : ¬ DSeparatedPa forkPa {0} {2} ∅ := by
  intro hsep
  have hpath : IsPathPa forkPa 0 2 [0, 1, 2] := by
    refine ⟨by decide, by unfold Adjacent; decide, by decide, by decide⟩
  have hblocked :=
    hsep 0 (Set.mem_singleton 0) 2 (Set.mem_singleton 2) [0, 1, 2] hpath
  obtain ⟨i, hi, hblock⟩ := hblocked
  simp at hi
  have hi0 : i = 0 := by omega
  subst hi0
  have hblock012 : BlockedAtPa forkPa ∅ 0 1 2 := hblock
  rcases hblock012 with ⟨h01, -, -⟩ | ⟨-, hmem⟩
  · exact (by decide : (0 : Fin 3) ∉ forkPa 1) h01
  · exact Set.notMem_empty 1 hmem

theorem fork_sep_mid : DSeparatedPa forkPa {0} {2} {1} := by
  intro x hx y hy p hp
  rw [Set.mem_singleton_iff] at hx hy
  subst hx hy
  have hshape := path_shape_of_not_adjacent forkPa (by unfold Adjacent; decide) p hp
  subst hshape
  refine ⟨0, by decide, ?_⟩
  show BlockedAtPa forkPa {1} 0 1 2
  refine Or.inr ⟨?_, Set.mem_singleton 1⟩
  intro hcon
  obtain ⟨h01, -⟩ := hcon
  exact (by decide : (0 : Fin 3) ∉ forkPa 1) h01

theorem collider_sep_empty : DSeparatedPa colliderPa {0} {2} ∅ := by
  intro x hx y hy p hp
  rw [Set.mem_singleton_iff] at hx hy
  subst hx hy
  have hshape := path_shape_of_not_adjacent colliderPa (by unfold Adjacent; decide) p hp
  subst hshape
  refine ⟨0, by decide, ?_⟩
  show BlockedAtPa colliderPa ∅ 0 1 2
  refine Or.inl ⟨by decide, by decide, fun d _ => Set.notMem_empty d⟩

theorem collider_not_sep_mid : ¬ DSeparatedPa colliderPa {0} {2} {1} := by
  intro hsep
  have hpath : IsPathPa colliderPa 0 2 [0, 1, 2] := by
    refine ⟨by decide, by unfold Adjacent; decide, by decide, by decide⟩
  have hblocked :=
    hsep 0 (Set.mem_singleton 0) 2 (Set.mem_singleton 2) [0, 1, 2] hpath
  obtain ⟨i, hi, hblock⟩ := hblocked
  simp at hi
  have hi0 : i = 0 := by omega
  subst hi0
  have hblock012 : BlockedAtPa colliderPa {1} 0 1 2 := hblock
  rcases hblock012 with ⟨-, -, hall⟩ | ⟨hneg, -⟩
  · exact (hall 1 Relation.ReflTransGen.refl) (Set.mem_singleton 1)
  · exact hneg ⟨by decide, by decide⟩

theorem chainNet_sep_mid : chainNet.DSeparated {0} {2} {1} :=
  chainNet_bridge.mpr chain_sep_mid

theorem chainNet_not_sep_empty : ¬ chainNet.DSeparated {0} {2} ∅ := by
  rw [BayesNet.dSeparated_iff_dSeparatedPa_toPa, chainNet_toPa]
  exact chain_not_sep_empty

end Cslib.MachineLearning.GraphicalModels
