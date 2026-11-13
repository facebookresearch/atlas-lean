/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































import Mathlib
import Code.Walls.baearmexist
import Code.Walls.bauacyclicarm

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}







theorem bfin2_neighbor_in_box {d R : ℕ} (hR : 1 ≤ R) {x n : Site d}
    (hx : x ∈ box d (R - 1)) (hadj : (hypercubicLattice d).Adj x n) : n ∈ box d R := by
  rw [hypercubicLattice_adj] at hadj
  intro i
  have hxi : (x i).natAbs ≤ R - 1 := hx i
  have hdi : (x i - n i).natAbs ≤ 1 := by
    have hle := Finset.single_le_sum (f := fun j => (x j - n j).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [hadj] at hle
    exact hle
  have htri : (n i).natAbs ≤ (x i).natAbs + (x i - n i).natAbs := by
    have hid : n i = x i - (x i - n i) := by ring
    calc (n i).natAbs = (x i - (x i - n i)).natAbs := by rw [← hid]
      _ ≤ (x i).natAbs + (x i - n i).natAbs := Int.natAbs_sub_le _ _
  omega


theorem bfin2_trifSet_finite (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ) :
    {x : Site d | bft_FineTrif ω x ∧ x ∈ box d (R - 1)}.Finite :=
  (box_finite d (R - 1)).subset (fun _ hx => hx.2)















theorem bfin2_count (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ) (hR : 1 ≤ R) :
    (bfin2_trifSet_finite ω R).toFinset.card ≤ (vertexBoundary_finite d R).toFinset.card := by
  classical
  
  set Sfin := (bfin2_trifSet_finite ω R).toFinset with hSfin
  
  rcases Sfin.eq_empty_or_nonempty with hempty | hne
  · simp [hempty]
  
  obtain ⟨F, hF_le, hF_acyc, hF_reach⟩ :=
    (openSubgraph d ω).exists_isAcyclic_reachable_eq_le
  
  haveI hlf : LocallyFinite F := by
    intro v
    apply Set.Finite.fintype
    apply Set.Finite.subset (Set.toFinite ((hypercubicLattice d).neighborSet v))
    intro w hw
    exact (hF_le.trans (openSubgraph_le ω)) hw
  
  have hspan : ∀ (x z : Site d), (openSubgraph d ω).Reachable x z → F.Reachable x z := by
    intro x z h; rw [hF_reach]; exact h
  
  have harms : ∀ i : ↥Sfin, ∃ (rr : Fin 3 → ℕ → Site d) (ll : Fin 3 → ℕ),
      (∀ j, rr j 0 = (i : Site d)) ∧
      (rr 0 1 ≠ rr 1 1 ∧ rr 0 1 ≠ rr 2 1 ∧ rr 1 1 ≠ rr 2 1) ∧
      (∀ j, 1 ≤ ll j) ∧
      (∀ j, ∀ k < ll j, F.Adj (rr j k) (rr j (k + 1))) ∧
      (∀ j, Set.InjOn (rr j) {m | m ≤ ll j}) ∧
      (∀ j, rr j (ll j) ∈ vertexBoundary d R) := by
    intro i
    have h2 : (i : Site d) ∈ (bfin2_trifSet_finite ω R).toFinset := i.2
    have hmem := (Set.Finite.mem_toFinset (bfin2_trifSet_finite ω R)).mp h2
    obtain ⟨hfine, hbox⟩ := hmem
    have hnbox : ∀ n, F.Adj (i : Site d) n → n ∈ box d R := by
      intro n hn
      exact bfin2_neighbor_in_box hR hbox ((hF_le.trans (openSubgraph_le ω)) hn)
    obtain ⟨ρ₁, ρ₂, ρ₃, ℓ₁, ℓ₂, ℓ₃, ⟨hs1, hs2, hs3⟩, ⟨hd12, hd13, hd23⟩,
      ⟨hl1, hl2, hl3⟩, ⟨ha1, ha2, ha3⟩, ⟨hi1, hi2, hi3⟩, ⟨ht1, ht2, ht3⟩⟩ :=
      bae_trif_arms (i : Site d) F hF_le (hspan (i : Site d)) hR hnbox hfine
    refine ⟨![ρ₁, ρ₂, ρ₃], ![ℓ₁, ℓ₂, ℓ₃], ?_, ⟨hd12, hd13, hd23⟩, ?_, ?_, ?_, ?_⟩ <;>
      intro j <;> fin_cases j <;> assumption
  
  choose rr ll hrr using harms
  
  set rayS : (↥Sfin × Fin 3) → ℕ → Site d := fun a k => rr a.1 a.2 k with hrayS
  set lenS : (↥Sfin × Fin 3) → ℕ := fun a => ll a.1 a.2 with hlenS
  have hlenS_pos : ∀ a, 1 ≤ lenS a := fun a => (hrr a.1).2.2.1 a.2
  have hrayS_start : ∀ a, rayS a 0 = (a.1 : Site d) := fun a => (hrr a.1).1 a.2
  have hrayS_adj : ∀ a, ∀ k < lenS a, F.Adj (rayS a k) (rayS a (k + 1)) :=
    fun a => (hrr a.1).2.2.2.1 a.2
  have hrayS_inj : ∀ a, Set.InjOn (rayS a) {m | m ≤ lenS a} :=
    fun a => (hrr a.1).2.2.2.2.1 a.2
  have hrayS_tip : ∀ a, rayS a (lenS a) ∈ vertexBoundary d R :=
    fun a => (hrr a.1).2.2.2.2.2 a.2
  have hrayS_dist : ∀ (i : ↥Sfin) (j j' : Fin 3), j ≠ j' → rr i j 1 ≠ rr i j' 1 := by
    intro i j j' hjj'
    obtain ⟨d01, d02, d12⟩ := (hrr i).2.1
    fin_cases j <;> fin_cases j' <;> first
      | exact (hjj' rfl).elim
      | exact d01 | exact fun h => d01 h.symm
      | exact d02 | exact fun h => d02 h.symm
      | exact d12 | exact fun h => d12 h.symm
  
  set Vset : Finset (Site d) :=
    Finset.univ.biUnion (fun a : ↥Sfin × Fin 3 =>
      (Finset.range (lenS a + 1)).image (fun k => rayS a k)) with hVset
  have hmemVset : ∀ v, v ∈ Vset ↔ ∃ (a : ↥Sfin × Fin 3) (k : ℕ), k ≤ lenS a ∧ rayS a k = v := by
    intro v
    rw [hVset, Finset.mem_biUnion]
    constructor
    · rintro ⟨a, -, hk⟩
      rw [Finset.mem_image] at hk
      obtain ⟨k, hkr, hkv⟩ := hk
      rw [Finset.mem_range] at hkr
      exact ⟨a, k, by omega, hkv⟩
    · rintro ⟨a, k, hk, hkv⟩
      exact ⟨a, Finset.mem_univ _, by
        rw [Finset.mem_image]; exact ⟨k, Finset.mem_range.mpr (by omega), hkv⟩⟩
  
  obtain ⟨i₀, hi₀⟩ := hne
  have hhub_mem : ∀ i : ↥Sfin, (i : Site d) ∈ Vset := by
    intro i
    rw [hmemVset]
    exact ⟨(i, 0), 0, Nat.zero_le _, by rw [hrayS_start]⟩
  haveI hVne : Nonempty (↥Vset) := ⟨⟨(⟨i₀, hi₀⟩ : ↥Sfin), hhub_mem ⟨i₀, hi₀⟩⟩⟩
  
  set ray : (↥Sfin × Fin 3) → ℕ → ↥Vset := fun a k =>
    ⟨rayS a (min k (lenS a)), by
      rw [hmemVset]; exact ⟨a, min k (lenS a), min_le_right _ _, rfl⟩⟩ with hray
  set len : (↥Sfin × Fin 3) → ℕ := lenS with hlen
  
  have hray_val : ∀ a k, k ≤ len a → (ray a k : Site d) = rayS a k := by
    intro a k hk
    change rayS a (min k (lenS a)) = rayS a k
    rw [min_eq_left hk]
  
  have hlen1 : ∀ a, 1 ≤ len a := hlenS_pos
  have hinj : ∀ a, Set.InjOn (ray a) {m | m ≤ len a} := by
    intro a m hm m' hm' hmm'
    have hm2 : m ≤ len a := hm
    have hm'2 : m' ≤ len a := hm'
    apply hrayS_inj a hm2 hm'2
    have := congrArg Subtype.val hmm'
    rwa [hray_val a m hm2, hray_val a m' hm'2] at this
  have hcover : ∀ v : ↥Vset, ∃ (a : ↥Sfin × Fin 3) (k : ℕ), k ≤ len a ∧ ray a k = v := by
    intro v
    obtain ⟨a, k, hk, hkv⟩ := (hmemVset (v : Site d)).mp v.2
    refine ⟨a, k, hk, ?_⟩
    apply Subtype.ext
    rw [hray_val a k hk]; exact hkv
  
  set f : ↥Sfin → ↥Vset := fun i => ⟨(i : Site d), hhub_mem i⟩ with hf
  have hf_inj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun w : ↥Vset => (w : Site d)) h
  set arm3 : ↥Sfin → Fin 3 → (↥Sfin × Fin 3) := fun i j => (i, j) with harm3
  have harm3start : ∀ i j, ray (arm3 i j) 0 = f i := by
    intro i j
    apply Subtype.ext
    change rayS (i, j) (min 0 (lenS (i, j))) = (i : Site d)
    rw [min_eq_left (Nat.zero_le _)]
    exact hrayS_start (i, j)
  have harm3dist : ∀ i (j j' : Fin 3), j ≠ j' → ray (arm3 i j) 1 ≠ ray (arm3 i j') 1 := by
    intro i j j' hjj' heq
    have hval : ∀ (j0 : Fin 3), (ray (arm3 i j0) 1 : Site d) = rr i j0 1 := by
      intro j0
      change rayS (i, j0) (min 1 (lenS (i, j0))) = rr i j0 1
      rw [min_eq_left (hlenS_pos (i, j0))]
    have hkey : rr i j 1 = rr i j' 1 := by
      have := congrArg Subtype.val heq
      rwa [hval, hval] at this
    exact hrayS_dist i j j' hjj' hkey
  have hhub : ∀ a, ∃ i, ray a 0 = f i := fun a => ⟨a.1, harm3start a.1 a.2⟩
  
  set B : Finset (↥Vset) :=
    Finset.univ.filter (fun v : ↥Vset => (v : Site d) ∈ vertexBoundary d R) with hB
  have htip : ∀ a, ray a (len a) ∈ B := by
    intro a
    rw [hB, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    change rayS a (min (lenS a) (lenS a)) ∈ vertexBoundary d R
    rw [min_self]
    exact hrayS_tip a
  
  haveI hdec : DecidableRel (bgf3_G ray len).Adj := Classical.decRel _
  
  have hcomap_acyc : (F.comap (⇑(Function.Embedding.subtype (fun v => v ∈ Vset)))).IsAcyclic :=
    hF_acyc.of_comap (Function.Embedding.subtype _)
  have hadjT : ∀ a, ∀ k < len a,
      (F.comap (⇑(Function.Embedding.subtype (fun v => v ∈ Vset)))).Adj (ray a k) (ray a (k + 1)) := by
    intro a k hk
    change F.Adj (ray a k : Site d) (ray a (k + 1) : Site d)
    rw [hray_val a k (le_of_lt hk), hray_val a (k + 1) hk]
    exact hrayS_adj a k hk
  have hacyc : (bgf3_G ray len).IsAcyclic :=
    bau_isAcyclic_of_le_acyclic hcomap_acyc (bgf3_le_tree ray len _ hadjT)
  
  have hcount : Fintype.card (↥Sfin) ≤ B.card :=
    bfk_forestCount (bgf3_G ray len) hacyc
      (bgf3_min_deg1 ray len hlen1 hinj hcover)
      f hf_inj
      (fun i => bgf3_deg3 ray len hlen1 hinj f arm3 harm3start harm3dist i)
      B
      (fun v hv => bgf3_leaves_on_boundary ray len hlen1 hinj htip f arm3 harm3start harm3dist hhub hv)
  
  have hB_le : B.card ≤ (vertexBoundary_finite d R).toFinset.card := by
    apply Finset.card_le_card_of_injOn (fun v : ↥Vset => (v : Site d))
    · intro v hv
      rw [Finset.mem_coe, hB, Finset.mem_filter] at hv
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      exact hv.2
    · intro a _ b _ h; exact Subtype.ext h
  calc Sfin.card = Fintype.card (↥Sfin) := (Fintype.card_coe Sfin).symm
    _ ≤ B.card := hcount
    _ ≤ (vertexBoundary_finite d R).toFinset.card := hB_le

end StatMech.Walls
