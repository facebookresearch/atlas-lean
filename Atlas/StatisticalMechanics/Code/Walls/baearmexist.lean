/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































import Mathlib
import Code.Walls.bgf3armunion
import Code.Walls.bflleafclose

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







theorem bae_neighbour_of_reach {V : Type*} [DecidableEq V] (T : SimpleGraph V) {x z : V}
    (hzx : z ≠ x) (hreach : T.Reachable x z) :
    ∃ n, T.Adj x n ∧ ray34_AvoidReach T {x} n z := by
  obtain ⟨p⟩ := hreach
  set q := p.toPath with hq
  have hqpath : (q : T.Walk x z).IsPath := q.2
  obtain ⟨n, hadj, q', hcons⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne (Ne.symm hzx) (q : T.Walk x z)
  have hpath' : (SimpleGraph.Walk.cons hadj q').IsPath := hcons ▸ hqpath
  have hxnotin : x ∉ q'.support := ((SimpleGraph.Walk.cons_isPath_iff hadj q').mp hpath').2
  refine ⟨n, hadj, q', ?_⟩
  intro u hu
  simp only [Set.mem_singleton_iff]
  rintro rfl
  exact hxnotin hu




theorem bae_branch_lift {ω : ConfigSpace (Sym2 (Site d))} (T : SimpleGraph (Site d))
    (hle : T ≤ openSubgraph d ω) {x n z : Site d} (h : ray34_AvoidReach T {x} n z) :
    (bkg_deleteVertex (openSubgraph d ω) x).Reachable n z := by
  obtain ⟨p, hp⟩ := h
  have hxns : x ∉ p.support := by
    intro hx; exact hp x hx rfl
  exact bkg_walkReach_free hle x n z p hxns




theorem bae_cluster_eq (ω : ConfigSpace (Sym2 (Site d))) (x a : Site d) :
    cluster d (removeSites ({x} : Finset (Site d)) ω) a
      = ray34_AvoidCluster (bkg_deleteVertex (openSubgraph d ω) x) ∅ a := by
  have hbox : bc61_boxAround d 0 x = {x} := bft_boxAround_zero x
  have hgeq : openSubgraph d (removeSites ({x} : Finset (Site d)) ω)
      = bkg_deleteVertex (openSubgraph d ω) x := by
    rw [← hbox]; exact bft_contractedLattice_zero ω x
  rw [← ray34_avoidCluster_empty_eq_cluster, hgeq]










theorem bae_one_branch {ω : ConfigSpace (Sym2 (Site d))} (x : Site d) (T : SimpleGraph (Site d))
    [LocallyFinite T] (hle : T ≤ openSubgraph d ω)
    (hspan : ∀ z, (openSubgraph d ω).Reachable x z → T.Reachable x z)
    {a : Site d} (hxa : (openSubgraph d ω).Adj x a)
    (hinf : (ray34_AvoidCluster (bkg_deleteVertex (openSubgraph d ω) x) ∅ a).Infinite) :
    ∃ n, T.Adj x n ∧ (ray34_AvoidCluster T {x} n).Infinite ∧
      n ∈ ray34_AvoidCluster (bkg_deleteVertex (openSubgraph d ω) x) ∅ a := by
  classical
  set D := bkg_deleteVertex (openSubgraph d ω) x with hDdef
  
  have hxiso : ∀ u, ¬ D.Adj u x := fun u hu => hu.2.2 rfl
  have hreach_x : ∀ {u}, D.Reachable u x → u = x := by
    intro u hux
    obtain ⟨p⟩ := hux.symm
    cases p with
    | nil => rfl
    | cons hadj q => exact absurd hadj.symm (hxiso _)
  have hDle : D ≤ openSubgraph d ω := fun u v huv => huv.1
  
  have hcover : ray34_AvoidCluster D ∅ a ⊆
      ⋃ n ∈ (↑(T.neighborFinset x) : Set (Site d)), ray34_AvoidCluster T {x} n := by
    intro z hz
    have hzD : D.Reachable a z := by obtain ⟨p, _⟩ := hz; exact p.reachable
    have hzx : z ≠ x := by
      intro hzeq; subst hzeq
      exact hxa.ne' (hreach_x hzD)
    have hzopen : (openSubgraph d ω).Reachable x z :=
      (hxa.reachable).trans (hzD.mono hDle)
    have hTreach : T.Reachable x z := hspan z hzopen
    obtain ⟨n, hadj, havoid⟩ := bae_neighbour_of_reach T hzx hTreach
    rw [Set.mem_iUnion₂]
    refine ⟨n, ?_, havoid⟩
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset]; exact hadj
  
  have hexinf : ∃ n ∈ T.neighborFinset x,
      (ray34_AvoidCluster T {x} n ∩ ray34_AvoidCluster D ∅ a).Infinite := by
    by_contra hcon
    push Not at hcon
    have hfin : ∀ n ∈ (↑(T.neighborFinset x) : Set (Site d)),
        (ray34_AvoidCluster T {x} n ∩ ray34_AvoidCluster D ∅ a).Finite := by
      intro n hn; rw [Finset.mem_coe] at hn; exact hcon n hn
    have hunionfin : (⋃ n ∈ (↑(T.neighborFinset x) : Set (Site d)),
        ray34_AvoidCluster T {x} n ∩ ray34_AvoidCluster D ∅ a).Finite :=
      Set.Finite.biUnion (Finset.finite_toSet _) hfin
    have hsub : ray34_AvoidCluster D ∅ a ⊆
        ⋃ n ∈ (↑(T.neighborFinset x) : Set (Site d)),
          ray34_AvoidCluster T {x} n ∩ ray34_AvoidCluster D ∅ a := by
      intro z hz
      obtain ⟨n, hn, hzn⟩ := Set.mem_iUnion₂.mp (hcover hz)
      rw [Set.mem_iUnion₂]
      exact ⟨n, hn, hzn, hz⟩
    exact hinf (hunionfin.subset hsub)
  obtain ⟨n, hnmem, hninf⟩ := hexinf
  refine ⟨n, (SimpleGraph.mem_neighborFinset T x n).mp hnmem, hninf.mono Set.inter_subset_left, ?_⟩
  
  obtain ⟨w, hwbranch, hwC⟩ := hninf.nonempty
  have hnw : D.Reachable n w := bae_branch_lift T hle (ray34_mem_avoidCluster.mp hwbranch)
  have haw : D.Reachable a w := by obtain ⟨p, _⟩ := hwC; exact p.reachable
  have han : D.Reachable a n := haw.trans hnw.symm
  refine ray34_mem_avoidCluster.mpr ?_
  obtain ⟨p⟩ := han
  exact ⟨p, fun u _ => Set.notMem_empty u⟩










theorem bae_three_infinite_branches {ω : ConfigSpace (Sym2 (Site d))} (x : Site d)
    (T : SimpleGraph (Site d)) [LocallyFinite T] (hle : T ≤ openSubgraph d ω)
    (hspan : ∀ z, (openSubgraph d ω).Reachable x z → T.Reachable x z)
    (h : bft_FineTrif ω x) :
    ∃ n₁ n₂ n₃ : Site d,
      (T.Adj x n₁ ∧ T.Adj x n₂ ∧ T.Adj x n₃) ∧
      (n₁ ≠ n₂ ∧ n₁ ≠ n₃ ∧ n₂ ≠ n₃) ∧
      ((ray34_AvoidCluster T {x} n₁).Infinite ∧
       (ray34_AvoidCluster T {x} n₂).Infinite ∧
       (ray34_AvoidCluster T {x} n₃).Infinite) := by
  classical
  obtain ⟨a₁, a₂, a₃, ⟨hxa₁, hxa₂, hxa₃⟩, ⟨hinf1, hinf2, hinf3⟩, ⟨hsep12, hsep13, hsep23⟩⟩ :=
    (bft_fineTrif_iff ω x).mp h
  have hI : ∀ a, (cluster d (removeSites ({x} : Finset (Site d)) ω) a).Infinite →
      (ray34_AvoidCluster (bkg_deleteVertex (openSubgraph d ω) x) ∅ a).Infinite := by
    intro a ha; rw [← bae_cluster_eq]; exact ha
  obtain ⟨n₁, hadj1, hbr1, hmem1⟩ := bae_one_branch x T hle hspan hxa₁ (hI a₁ hinf1)
  obtain ⟨n₂, hadj2, hbr2, hmem2⟩ := bae_one_branch x T hle hspan hxa₂ (hI a₂ hinf2)
  obtain ⟨n₃, hadj3, hbr3, hmem3⟩ := bae_one_branch x T hle hspan hxa₃ (hI a₃ hinf3)
  have toReach : ∀ {a n}, n ∈ ray34_AvoidCluster (bkg_deleteVertex (openSubgraph d ω) x) ∅ a →
      (bkg_deleteVertex (openSubgraph d ω) x).Reachable a n := by
    intro a n hn; obtain ⟨p, _⟩ := hn; exact p.reachable
  refine ⟨n₁, n₂, n₃, ⟨hadj1, hadj2, hadj3⟩, ⟨?_, ?_, ?_⟩, ⟨hbr1, hbr2, hbr3⟩⟩
  · intro heq; apply hsep12
    have h2 : (bkg_deleteVertex (openSubgraph d ω) x).Reachable a₂ n₁ := by
      rw [heq]; exact toReach hmem2
    exact (toReach hmem1).trans h2.symm
  · intro heq; apply hsep13
    have h2 : (bkg_deleteVertex (openSubgraph d ω) x).Reachable a₃ n₁ := by
      rw [heq]; exact toReach hmem3
    exact (toReach hmem1).trans h2.symm
  · intro heq; apply hsep23
    have h2 : (bkg_deleteVertex (openSubgraph d ω) x).Reachable a₃ n₂ := by
      rw [heq]; exact toReach hmem3
    exact (toReach hmem2).trans h2.symm












theorem bae_arm {ω : ConfigSpace (Sym2 (Site d))} (x : Site d) (T : SimpleGraph (Site d))
    [LocallyFinite T] (hle : T ≤ openSubgraph d ω) {n : Site d} {R : ℕ} (hR : 1 ≤ R)
    (hadjxn : T.Adj x n) (hn : n ∈ box d R) (hbr : (ray34_AvoidCluster T {x} n).Infinite) :
    ∃ (armRay : ℕ → Site d) (armLen : ℕ),
      armRay 0 = x ∧ armRay 1 = n ∧ 1 ≤ armLen ∧
      (∀ k < armLen, T.Adj (armRay k) (armRay (k + 1))) ∧
      Set.InjOn armRay {m | m ≤ armLen} ∧
      armRay armLen ∈ vertexBoundary d R := by
  classical
  have hnx : n ≠ x := hadjxn.ne'
  obtain ⟨r, hr0, hrinj, hradj, hravoid, hcross⟩ :=
    bfl_fineArm_reaches_boundary T hle hR hnx hn hbr
  set K := Nat.find hcross with hKdef
  have hKspec : r K ∈ vertexBoundary d R := Nat.find_spec hcross
  set armRay : ℕ → Site d := fun k => if k = 0 then x else r (k - 1) with harmdef
  have harm0 : armRay 0 = x := by simp [harmdef]
  have hval : ∀ m, armRay (m + 1) = r m := by intro m; simp [harmdef]
  refine ⟨armRay, K + 1, harm0, ?_, by omega, ?_, ?_, ?_⟩
  · rw [hval 0]; exact hr0
  · 
    intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      rw [harm0, hval 0, hr0]; exact hadjxn
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [hval m, hval (m + 1)]; exact hradj m
  · 
    intro a ha b hb hab
    rcases a with _ | p <;> rcases b with _ | m
    · rfl
    · rw [harm0, hval m] at hab; exact absurd hab.symm (hravoid m)
    · rw [harm0, hval p] at hab; exact absurd hab (hravoid p)
    · rw [hval p, hval m] at hab; rw [hrinj hab]
  · 
    rw [hval K]; exact hKspec







theorem bae_trif_arms {ω : ConfigSpace (Sym2 (Site d))} (x : Site d) (T : SimpleGraph (Site d))
    [LocallyFinite T] (hle : T ≤ openSubgraph d ω)
    (hspan : ∀ z, (openSubgraph d ω).Reachable x z → T.Reachable x z)
    {R : ℕ} (hR : 1 ≤ R) (hnbox : ∀ n, T.Adj x n → n ∈ box d R) (h : bft_FineTrif ω x) :
    ∃ (ρ₁ ρ₂ ρ₃ : ℕ → Site d) (ℓ₁ ℓ₂ ℓ₃ : ℕ),
      (ρ₁ 0 = x ∧ ρ₂ 0 = x ∧ ρ₃ 0 = x) ∧
      (ρ₁ 1 ≠ ρ₂ 1 ∧ ρ₁ 1 ≠ ρ₃ 1 ∧ ρ₂ 1 ≠ ρ₃ 1) ∧
      (1 ≤ ℓ₁ ∧ 1 ≤ ℓ₂ ∧ 1 ≤ ℓ₃) ∧
      ((∀ k < ℓ₁, T.Adj (ρ₁ k) (ρ₁ (k + 1))) ∧
       (∀ k < ℓ₂, T.Adj (ρ₂ k) (ρ₂ (k + 1))) ∧
       (∀ k < ℓ₃, T.Adj (ρ₃ k) (ρ₃ (k + 1)))) ∧
      (Set.InjOn ρ₁ {m | m ≤ ℓ₁} ∧ Set.InjOn ρ₂ {m | m ≤ ℓ₂} ∧ Set.InjOn ρ₃ {m | m ≤ ℓ₃}) ∧
      (ρ₁ ℓ₁ ∈ vertexBoundary d R ∧ ρ₂ ℓ₂ ∈ vertexBoundary d R ∧ ρ₃ ℓ₃ ∈ vertexBoundary d R) := by
  obtain ⟨n₁, n₂, n₃, ⟨ha1, ha2, ha3⟩, ⟨hd12, hd13, hd23⟩, ⟨hi1, hi2, hi3⟩⟩ :=
    bae_three_infinite_branches x T hle hspan h
  obtain ⟨ρ₁, ℓ₁, hρ1_0, hρ1_1, hℓ1, hadj1, hinj1, htip1⟩ :=
    bae_arm x T hle hR ha1 (hnbox n₁ ha1) hi1
  obtain ⟨ρ₂, ℓ₂, hρ2_0, hρ2_1, hℓ2, hadj2, hinj2, htip2⟩ :=
    bae_arm x T hle hR ha2 (hnbox n₂ ha2) hi2
  obtain ⟨ρ₃, ℓ₃, hρ3_0, hρ3_1, hℓ3, hadj3, hinj3, htip3⟩ :=
    bae_arm x T hle hR ha3 (hnbox n₃ ha3) hi3
  refine ⟨ρ₁, ρ₂, ρ₃, ℓ₁, ℓ₂, ℓ₃, ⟨hρ1_0, hρ2_0, hρ3_0⟩, ⟨?_, ?_, ?_⟩,
    ⟨hℓ1, hℓ2, hℓ3⟩, ⟨hadj1, hadj2, hadj3⟩, ⟨hinj1, hinj2, hinj3⟩, ⟨htip1, htip2, htip3⟩⟩
  · rw [hρ1_1, hρ2_1]; exact hd12
  · rw [hρ1_1, hρ3_1]; exact hd13
  · rw [hρ2_1, hρ3_1]; exact hd23




theorem bae_fineTrifs_finite (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ) :
    {x : Site d | x ∈ box d R ∧ bft_FineTrif ω x}.Finite :=
  (box_finite d R).subset (fun x hx => hx.1)







































theorem bae_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2) (T : SimpleGraph (Site 2))
      [_i : LocallyFinite T], T ≤ openSubgraph 2 ω →
      (∀ z, (openSubgraph 2 ω).Reachable x z → T.Reachable x z) →
      bft_FineTrif ω x →
      ∃ n₁ n₂ n₃ : Site 2, (T.Adj x n₁ ∧ T.Adj x n₂ ∧ T.Adj x n₃) ∧
        (n₁ ≠ n₂ ∧ n₁ ≠ n₃ ∧ n₂ ≠ n₃) ∧
        ((ray34_AvoidCluster T {x} n₁).Infinite ∧ (ray34_AvoidCluster T {x} n₂).Infinite ∧
         (ray34_AvoidCluster T {x} n₃).Infinite)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2) (T : SimpleGraph (Site 2))
      [_i : LocallyFinite T], T ≤ openSubgraph 2 ω → ∀ {n : Site 2} {R : ℕ}, 1 ≤ R →
      T.Adj x n → n ∈ box 2 R → (ray34_AvoidCluster T {x} n).Infinite →
      ∃ (armRay : ℕ → Site 2) (armLen : ℕ), armRay 0 = x ∧ armRay 1 = n ∧ 1 ≤ armLen ∧
        (∀ k < armLen, T.Adj (armRay k) (armRay (k + 1))) ∧
        Set.InjOn armRay {m | m ≤ armLen} ∧ armRay armLen ∈ vertexBoundary 2 R) ∧
    
    (Fintype.card (Fin 1) ≤ ({1, 2, 3} : Finset (Fin 4)).card) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω x T _i hle hspan h; exact bae_three_infinite_branches x T hle hspan h
  · intro ω x T _i hle n R hR hadj hn hbr; exact bae_arm x T hle hR hadj hn hbr
  · exact bgf3_star_witness

end StatMech.Walls
