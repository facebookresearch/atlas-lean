/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Positivity

/-!
# The Caro–Wei independence bound

Every finite graph has an independent set of size at least
`∑ v, 1 / (G.degree v + 1)`.

This is a port of the reusable Caro–Wei proof from Vilin97/lean-pool
(`LeanPool/Erdos132ThreeChain/CaroWei.lean`, theorem
`Erdos132ThreeChain.carowei`), revision
`faa8c032722c955187fae103c96e8e93066f4592`, released under Apache 2.0.
The upstream proof is stated for a raw symmetric irreflexive adjacency
relation on a vertex `Finset`; here it is adapted to Mathlib's native
`SimpleGraph`, `degree`, `IsIndepSet`, and `indepNum` APIs.

## Main results

- `SimpleGraph.exists_isIndepSet_caroWei`: existence of an independent set
  attaining the reciprocal degree-sum bound.
- `SimpleGraph.caroWei_le_indepNum`: the bound restated via `G.indepNum`.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

/-- Auxiliary Caro–Wei bound over an explicit vertex `Finset`, using global
degrees throughout. -/
private theorem caroWei_aux (t : Finset V) :
    ∃ s ⊆ t, G.IsIndepSet (s : Set V) ∧
      ∑ v ∈ t, (1 : ℝ) / (G.degree v + 1) ≤ s.card := by
  classical
  induction t using Finset.strongInduction with
  | _ t ih =>
    rcases t.eq_empty_or_nonempty with rfl | htne
    · exact ⟨∅, by simp, by simp, by simp⟩
    obtain ⟨v, hv, hmin⟩ := Finset.exists_min_image t (fun v => G.degree v) htne
    have hvN' : v ∉ t.filter (G.Adj v) :=
      fun h => G.irrefl (Finset.mem_filter.mp h).2
    set N : Finset V := t.filter (G.Adj v) with hN
    have hvN : v ∉ N := by rw [hN]; exact hvN'
    set NV : Finset V := insert v N with hNV
    have hmemNV : v ∈ NV := by rw [hNV]; exact Finset.mem_insert_self v N
    have hNVsub : NV ⊆ t := by
      rw [hNV]
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hv
      · exact (Finset.mem_filter.mp (hN ▸ hx)).1
    set W : Finset V := t \ NV with hW
    have hWsub : W ⊆ t := by rw [hW]; exact Finset.sdiff_subset
    have hvW : v ∉ W := fun h => (Finset.mem_sdiff.mp (hW ▸ h)).2 hmemNV
    have hWlt : W ⊂ t := ⟨hWsub, fun hc => hvW (hc hv)⟩
    obtain ⟨S', hS'W, hS'ind, hS'card⟩ := ih W hWlt
    have hS't : ∀ u ∈ S', u ∈ t := fun u hu => hWsub (hS'W hu)
    have hvS' : v ∉ S' := fun hc => hvW (hS'W hc)
    have hnadj : ∀ u ∈ S', ¬ G.Adj v u := by
      intro u hu hadj
      have hmem : u ∈ t \ NV := hW ▸ hS'W hu
      have huN : u ∈ N := hN ▸ Finset.mem_filter.mpr ⟨hS't u hu, hadj⟩
      have hmemNV' : u ∈ NV := hNV ▸ Finset.mem_insert_of_mem huN
      exact (Finset.mem_sdiff.mp hmem).2 hmemNV'
    refine ⟨insert v S', ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hv
      · exact hS't x hx
    · intro p hp q hq hpq hadj
      rw [Finset.mem_coe, Finset.mem_insert] at hp hq
      rcases hp with rfl | hp'
      · rcases hq with rfl | hq'
        · exact absurd rfl hpq
        · exact hnadj q hq' hadj
      · rcases hq with rfl | hq'
        · exact absurd (G.adj_symm hadj) (hnadj p hp')
        · exact hS'ind (Finset.mem_coe.mpr hp') (Finset.mem_coe.mpr hq') hpq hadj
    · have hcard : ((insert v S').card : ℝ) = (S'.card : ℝ) + 1 := by
        rw [Finset.card_insert_of_notMem hvS', Nat.cast_add, Nat.cast_one]
      rw [hcard]
      have hsplit : ∑ u ∈ t \ NV, (1 : ℝ) / (G.degree u + 1)
          + ∑ u ∈ NV, (1 : ℝ) / (G.degree u + 1)
          = ∑ u ∈ t, (1 : ℝ) / (G.degree u + 1) := Finset.sum_sdiff hNVsub
      have hS'card' : ∑ u ∈ t \ NV, (1 : ℝ) / (G.degree u + 1) ≤ S'.card := hW ▸ hS'card
      have hbound : ∀ u ∈ NV, (1 : ℝ) / (G.degree u + 1)
          ≤ 1 / (G.degree v + 1) := by
        intro u hu
        have hle : G.degree v ≤ G.degree u := hmin u (hNVsub hu)
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right hle 1
      have hNVcard : NV.card ≤ G.degree v + 1 := by
        have hNsub : t.filter (G.Adj v) ⊆ G.neighborFinset v := by
          intro x hx
          rw [Finset.mem_filter] at hx
          exact (G.mem_neighborFinset v x).mpr hx.2
        have hle : (t.filter (G.Adj v)).card ≤ (G.neighborFinset v).card :=
          Finset.card_le_card hNsub
        have hle' : (t.filter (G.Adj v)).card ≤ G.degree v := by
          rwa [G.card_neighborFinset_eq_degree v] at hle
        have hNVeq : NV.card = (t.filter (G.Adj v)).card + 1 := by
          rw [hNV, hN, Finset.card_insert_of_notMem hvN']
        omega
      have hhead : ∑ u ∈ NV, (1 : ℝ) / (G.degree u + 1) ≤ 1 := by
        have hle : (NV.card : ℝ) ≤ (G.degree v : ℝ) + 1 := by
          exact_mod_cast hNVcard
        have hpos : (0 : ℝ) < (G.degree v : ℝ) + 1 := by positivity
        calc ∑ u ∈ NV, (1 : ℝ) / (G.degree u + 1)
            ≤ NV.card • (1 / ((G.degree v : ℝ) + 1)) :=
              Finset.sum_le_card_nsmul _ _ _ hbound
          _ ≤ 1 := by
              rw [nsmul_eq_mul, mul_one_div, div_le_one hpos]
              exact hle
      linarith [hsplit, hhead, hS'card']

/-- **Caro–Wei bound.** Every finite graph has an independent set of size at
least the sum over its vertices of the reciprocal of one more than the
degree. -/
theorem exists_isIndepSet_caroWei :
    ∃ s : Finset V, G.IsIndepSet (s : Set V) ∧
      ∑ v, (1 : ℝ) / (G.degree v + 1) ≤ s.card := by
  obtain ⟨s, -, hs, hcard⟩ := G.caroWei_aux Finset.univ
  exact ⟨s, hs, by simpa using hcard⟩

/-- **Caro–Wei bound for the independence number.** For every finite simple graph $G$, the
independence number of $G$ is at least $\sum_{v} \frac{1}{\deg(v) + 1}$, the sum running over all
vertices $v$ of $G$. -/
theorem caroWei_le_indepNum :
    ∑ v, (1 : ℝ) / (G.degree v + 1) ≤ G.indepNum := by
  obtain ⟨s, hs, hsum⟩ := G.exists_isIndepSet_caroWei
  have hle : (s.card : ℝ) ≤ G.indepNum := by exact_mod_cast hs.card_le_indepNum
  exact hsum.trans hle

end SimpleGraph
