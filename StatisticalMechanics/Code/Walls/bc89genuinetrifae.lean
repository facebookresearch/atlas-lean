/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































































import Mathlib
import Code.Walls.bc88genuinecount
import Code.Walls.bc85bootstrap

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}














def bc89_GenuineTrif (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) : Prop :=
  ∃ a₁ a₂ a₃ : Site d,
    (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    (a₁ ≠ x ∧ a₂ ≠ x ∧ a₃ ≠ x) ∧
    ((openSubgraph d ω).Adj x a₁ ∧ (openSubgraph d ω).Adj x a₂ ∧ (openSubgraph d ω).Adj x a₃) ∧
    ((cluster d (removeSite x ω) a₁).Infinite ∧ (cluster d (removeSite x ω) a₂).Infinite ∧
      (cluster d (removeSite x ω) a₃).Infinite) ∧
    (¬ Connected d (removeSite x ω) a₁ a₂ ∧
      ¬ Connected d (removeSite x ω) a₁ a₃ ∧
      ¬ Connected d (removeSite x ω) a₂ a₃)


noncomputable def bc89_genuineTrifFinset (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    Finset (Site d) := by
  classical
  exact (boxFinsetBK d n).filter (fun x => bc89_GenuineTrif d ω x)


noncomputable def bc89_genuineTcount (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : ℕ :=
  (bc89_genuineTrifFinset ω n).card













theorem bc89_genuine_imp_isTrif (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (h : bc89_GenuineTrif d ω x) : IsTrifurcation d ω x := by
  obtain ⟨a₁, a₂, a₃, hne, hnx, hadj, hinf, hsep⟩ := h
  refine ⟨a₁, a₂, a₃, hne, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, hsep⟩
  · exact hadj.1.reachable
  · exact hadj.2.1.reachable
  · exact hadj.2.2.reachable
  
  · exact Set.Infinite.mono (cluster_mono (removeSite_le x ω) a₁) hinf.1
  · exact Set.Infinite.mono (cluster_mono (removeSite_le x ω) a₂) hinf.2.1
  · exact Set.Infinite.mono (cluster_mono (removeSite_le x ω) a₃) hinf.2.2


theorem bc89_genuineTrifFinset_subset (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc89_genuineTrifFinset ω n ⊆ tfc_trifFinset ω n := by
  classical
  intro x hx
  rw [bc89_genuineTrifFinset, Finset.mem_filter] at hx
  rw [tfc_mem_trifFinset]
  refine ⟨?_, bc89_genuine_imp_isTrif ω x hx.2⟩
  have := hx.1
  rw [boxFinsetBK, Set.Finite.mem_toFinset] at this
  exact this




theorem bc89_genuineTcount_le_Tcount (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc89_genuineTcount ω n ≤ Tcount d ω n := by
  rw [bc89_genuineTcount, ← tfc_trifFinset_card]
  exact Finset.card_le_card (bc89_genuineTrifFinset_subset ω n)











theorem bc89_removeSite_no_open_nbr (x y : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    ¬ (openSubgraph d (removeSite x ω)).Adj x y := by
  intro hadj
  obtain ⟨_, hopen⟩ := hadj
  rw [removeSite_apply_of_mem (Sym2.mem_mk_left x y)] at hopen
  exact absurd hopen (by decide)




theorem bc89_removeSite_connected_center_iff (x y : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    Connected d (removeSite x ω) x y ↔ y = x := by
  constructor
  · rintro ⟨walk⟩
    cases walk with
    | nil => rfl
    | cons hadj w' => exact absurd hadj (bc89_removeSite_no_open_nbr x _ ω)
  · rintro rfl; exact connected_refl _ _


theorem bc89_center_removeSite_cluster_eq (x : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    cluster d (removeSite x ω) x = {x} := by
  ext y
  rw [mem_cluster, bc89_removeSite_connected_center_iff, Set.mem_singleton_iff]





theorem bc89_center_removeSite_cluster_finite (x : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    ¬ (cluster d (removeSite x ω) x).Infinite := by
  rw [bc89_center_removeSite_cluster_eq]
  exact fun h => h (Set.finite_singleton x)














theorem bc89_three_open_nbrs_of_genuine (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (h : bc89_GenuineTrif d ω x) :
    ∃ a₁ a₂ a₃ : Site d, (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
      (openSubgraph d ω).Adj x a₁ ∧ (openSubgraph d ω).Adj x a₂ ∧ (openSubgraph d ω).Adj x a₃ := by
  obtain ⟨a₁, a₂, a₃, hne, _, hadj, _, _⟩ := h
  exact ⟨a₁, a₂, a₃, hne, hadj⟩

open Classical in







theorem bc89_genuineTrif_open_degree_ge_three {Vset : Finset (Site d)}
    (F : SimpleGraph (↑Vset : Type)) [DecidableRel F.Adj]
    (vx : (↑Vset : Type)) (b : Fin 3 → (↑Vset : Type))
    (hbne : b 0 ≠ b 1 ∧ b 0 ≠ b 2 ∧ b 1 ≠ b 2)
    (hnbr : ∀ i, F.Adj vx (b i)) :
    3 ≤ F.degree vx := by
  classical
  
  have hsub : ({b 0, b 1, b 2} : Finset (↑Vset : Type)) ⊆ F.neighborFinset vx := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rw [F.mem_neighborFinset]
    rcases hw with h | h | h <;> (subst h; first | exact hnbr 0 | exact hnbr 1 | exact hnbr 2)
  have hcard3 : ({b 0, b 1, b 2} : Finset (↑Vset : Type)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]; exact hbne.2.2
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hbne.1, hbne.2.1⟩
  rw [← F.card_neighborFinset_eq_degree]
  calc 3 = ({b 0, b 1, b 2} : Finset (↑Vset : Type)).card := hcard3.symm
    _ ≤ (F.neighborFinset vx).card := Finset.card_le_card hsub






















theorem bc89_upperLines_open_nbr {x v : Site 2}
    (hadj : (openSubgraph 2 bc60_upperLines).Adj x v) :
    v 1 = x 1 ∧ (v 0 - x 0).natAbs = 1 := by
  obtain ⟨hlat, hopen⟩ := hadj
  obtain ⟨_, _, hh⟩ := bc60_open_edge_heights hopen
  refine ⟨hh.symm, ?_⟩
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hlat
  omega





theorem bc89_upperLines_no_three_open_nbrs (x a₁ a₂ a₃ : Site 2)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (openSubgraph 2 bc60_upperLines).Adj x a₁ ∧ (openSubgraph 2 bc60_upperLines).Adj x a₂ ∧
      (openSubgraph 2 bc60_upperLines).Adj x a₃) : False := by
  obtain ⟨h1h, h1c⟩ := bc89_upperLines_open_nbr hadj.1
  obtain ⟨h2h, h2c⟩ := bc89_upperLines_open_nbr hadj.2.1
  obtain ⟨h3h, h3c⟩ := bc89_upperLines_open_nbr hadj.2.2
  
  
  have hc1 : a₁ 0 = x 0 - 1 ∨ a₁ 0 = x 0 + 1 := by
    rcases (Int.natAbs_eq_iff).mp h1c with h | h <;> omega
  have hc2 : a₂ 0 = x 0 - 1 ∨ a₂ 0 = x 0 + 1 := by
    rcases (Int.natAbs_eq_iff).mp h2c with h | h <;> omega
  have hc3 : a₃ 0 = x 0 - 1 ∨ a₃ 0 = x 0 + 1 := by
    rcases (Int.natAbs_eq_iff).mp h3c with h | h <;> omega
  
  have hsite_eq : ∀ u w : Site 2, u 0 = w 0 → u 1 = w 1 → u = w := by
    intro u w h0 h1
    funext i; fin_cases i
    · exact h0
    · exact h1
  
  
  rcases hc1 with c1 | c1 <;> rcases hc2 with c2 | c2 <;> rcases hc3 with c3 | c3
  
  · exact hne.1 (hsite_eq a₁ a₂ (by omega) (by omega))
  · exact hne.1 (hsite_eq a₁ a₂ (by omega) (by omega))
  · exact hne.2.1 (hsite_eq a₁ a₃ (by omega) (by omega))
  · exact hne.2.2 (hsite_eq a₂ a₃ (by omega) (by omega))
  · exact hne.2.2 (hsite_eq a₂ a₃ (by omega) (by omega))
  · exact hne.2.1 (hsite_eq a₁ a₃ (by omega) (by omega))
  · exact hne.1 (hsite_eq a₁ a₂ (by omega) (by omega))
  · exact hne.1 (hsite_eq a₁ a₂ (by omega) (by omega))








theorem bc89_upperLines_not_genuineTrif (x : Site 2) :
    ¬ bc89_GenuineTrif 2 bc60_upperLines x := by
  intro h
  obtain ⟨a₁, a₂, a₃, hne, hadj⟩ := bc89_three_open_nbrs_of_genuine bc60_upperLines x h
  exact bc89_upperLines_no_three_open_nbrs x a₁ a₂ a₃ hne hadj







theorem bc89_upperLines_genuineTcount_zero (n : ℕ) :
    bc89_genuineTcount bc60_upperLines n = 0 := by
  classical
  rw [bc89_genuineTcount, bc89_genuineTrifFinset, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _
  exact bc89_upperLines_not_genuineTrif x






theorem bc89_upperLines_genuine_le_boundary (n : ℕ) :
    bc89_genuineTcount bc60_upperLines n ≤ boxSV_boundaryCard 2 n := by
  rw [bc89_upperLines_genuineTcount_zero]; exact Nat.zero_le _

















theorem bc89_genuineTcount_le_boundary_of_openForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bst_BoxOpenForest ω n) :
    bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n :=
  le_trans (bc89_genuineTcount_le_Tcount ω n) (bst_Tcount_le_boundary_of_boxOpenForest ω n h)
















theorem bc89_coarse_target_faithful {L : ℕ} (hL : 3 ≤ L) :
    bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) :=
  bc61_wholeBox_severs_upperLines hL



































theorem bc89_audit (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
    
    (∃ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1) ∧
    
    (∀ R : ℕ, ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
      = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ) ∧
    
    ((∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) → bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧
    
    ((∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) → bc61_CoarseTrifExistence μ L →
      (∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 →
        ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) →
      μ {ω | numInfiniteClusters d ω ≤ 1} = 1) := by
  refine ⟨bc78_numInfinite_ae_const μ herg, fun R => bc85_expectation_identity μ hinv L R, ?_, ?_⟩
  · intro hforest_ae hexist; exact bc85_dc_bootstrap μ hd L hinv hforest_ae hexist
  · intro hforest_ae hexist hmergeGeom
    exact bc85_dc_step1_uniqueness μ hd L herg hfe hinv hforest_ae hexist hmergeGeom



















































theorem bc89_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2),
      bc89_GenuineTrif 2 ω x → IsTrifurcation 2 ω x) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), bc89_genuineTcount ω n ≤ Tcount 2 ω n) ∧
    
    (∀ x : Site 2, ¬ bc89_GenuineTrif 2 bc60_upperLines x) ∧
    (∀ n : ℕ, bc89_genuineTcount bc60_upperLines n = 0) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2), bc89_GenuineTrif 2 ω x →
      ∃ a₁ a₂ a₃ : Site 2, (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
        (openSubgraph 2 ω).Adj x a₁ ∧ (openSubgraph 2 ω).Adj x a₂ ∧ (openSubgraph 2 ω).Adj x a₃) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ),
      bst_BoxOpenForest ω n → bc89_genuineTcount ω n ≤ boxSV_boundaryCard 2 n) ∧
    
    (∀ {L : ℕ}, 3 ≤ L → bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω x h; exact bc89_genuine_imp_isTrif ω x h
  · intro ω n; exact bc89_genuineTcount_le_Tcount ω n
  · intro x; exact bc89_upperLines_not_genuineTrif x
  · intro n; exact bc89_upperLines_genuineTcount_zero n
  · intro ω x h; exact bc89_three_open_nbrs_of_genuine ω x h
  · intro ω n h; exact bc89_genuineTcount_le_boundary_of_openForest ω n h
  · intro L hL; exact bc89_coarse_target_faithful hL

end StatMech.Walls
