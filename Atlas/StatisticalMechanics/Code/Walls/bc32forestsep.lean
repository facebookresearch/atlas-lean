/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.BoxSurfaceVolume
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeane
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.TrifurcationCount
import Code.Percolation.ArmReachComponentClose
import Code.Percolation.DisjointArmEndsProve
import Code.Percolation.DisjointArmEndsProve2
import Code.Walls.bc26forest
import Code.Walls.bc30armforest
import Code.Walls.bc31globalarm

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}



















theorem bc32_not_tfree_of_branchTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a aⱼ y : Site d} (hmeet : Connected d (removeSite x₀ ω) a aⱼ)
    (hyj : Connected d (removeSite x₀ ω) aⱼ y) (hyT : y ∈ tfc_trifFinset ω n) :
    ¬ (∀ z, Connected d (removeSite x₀ ω) a z → z ∉ tfc_trifFinset ω n) := by
  intro hTfree
  exact hTfree y (hmeet.trans hyj) hyT











theorem bc32_no_tfreeArm_of_armTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a₁ a₂ a₃ : Site d} (y : Fin 3 → Site d)
    (htrifArm : ∀ i, y i ∈ tfc_trifFinset ω n ∧
      Connected d (removeSite x₀ ω) (![a₁, a₂, a₃] i) (y i))
    {a : Site d}
    (hcover : Connected d (removeSite x₀ ω) a a₁ ∨
      Connected d (removeSite x₀ ω) a a₂ ∨ Connected d (removeSite x₀ ω) a a₃) :
    ¬ (∀ z, Connected d (removeSite x₀ ω) a z → z ∉ tfc_trifFinset ω n) := by
  rcases hcover with h | h | h
  · exact bc32_not_tfree_of_branchTrif ω n h (htrifArm 0).2 (htrifArm 0).1
  · exact bc32_not_tfree_of_branchTrif ω n h (htrifArm 1).2 (htrifArm 1).1
  · exact bc32_not_tfree_of_branchTrif ω n h (htrifArm 2).2 (htrifArm 2).1













theorem bc32_not_tfreeDownArmData_of_clawTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) {x₀ a₁ a₂ a₃ : Site d} (y : Fin 3 → Site d)
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (htrifArm : ∀ i, y i ∈ tfc_trifFinset ω n ∧
      Connected d (removeSite x₀ ω) (![a₁, a₂, a₃] i) (y i))
    (hcover : ∀ a : Site d, (cluster d (removeSite x₀ ω) a).Infinite →
      Connected d ω x₀ a →
      Connected d (removeSite x₀ ω) a a₁ ∨
        Connected d (removeSite x₀ ω) a a₂ ∨ Connected d (removeSite x₀ ω) a a₃) :
    ¬ bc31_TfreeDownArmData ω n rank := by
  rintro ⟨b, hbdata, _⟩
  obtain ⟨_, hbconn, hbinf, hbTfree⟩ := hbdata x₀ hx0box htri0
  exact bc32_no_tfreeArm_of_armTrif ω n y htrifArm (hcover (b x₀) hbinf hbconn) hbTfree



























def bc32_EscapingDownArmData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (∀ m : ℕ, ∃ z, z ∉ box d m ∧
        ∃ w : (openSubgraph d (removeSite x ω)).Walk (b x) z,
          ∀ v ∈ w.support, v ∉ tfc_trifFinset ω n)) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x < rank y →
      ¬ Connected d (removeSite y ω) (b y) (b x))







theorem bc32_escapingRay_of_tfree (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) {x a : Site d}
    (hinf : (cluster d (removeSite x ω) a).Infinite)
    (hTfree : ∀ z, Connected d (removeSite x ω) a z → z ∉ tfc_trifFinset ω n) :
    ∀ m : ℕ, ∃ z, z ∉ box d m ∧
      ∃ w : (openSubgraph d (removeSite x ω)).Walk a z,
        ∀ v ∈ w.support, v ∉ tfc_trifFinset ω n := by
  intro m
  obtain ⟨z, hz, hzconn⟩ := (cluster_infinite_iff (removeSite x ω) a).mp hinf m
  obtain ⟨w⟩ := hzconn
  exact ⟨z, hz, w, fun v hv => hTfree v (bc31_support_connected ω w hv)⟩










theorem bc32_escapingDownArmData_of_tfreeDownArmData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (h : bc31_TfreeDownArmData ω n rank) :
    bc32_EscapingDownArmData ω n rank := by
  obtain ⟨b, hbdata, hsplit⟩ := h
  refine ⟨b, ?_, hsplit⟩
  intro x hxbox htri
  obtain ⟨hbbox, hbconn, hbinf, hbTfree⟩ := hbdata x hxbox htri
  exact ⟨hbbox, hbconn, bc32_escapingRay_of_tfree ω n hbinf hbTfree⟩





theorem bc32_globalCutDownArmData_of_escapingDownArmData (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (rank : Site d → ℕ ×ₗ ℕ) (h : bc32_EscapingDownArmData ω n rank) :
    bc30_GlobalCutDownArmData ω n rank := by
  obtain ⟨b, hbdata, hsplit⟩ := h
  rw [bc30_globalCutDownArmData_iff_rootedDownArmForest]
  refine ⟨b, ?_, hsplit⟩
  intro x hxbox htri
  obtain ⟨hbbox, hbconn, hesc⟩ := hbdata x hxbox htri
  exact ⟨hbbox, hbconn, bc31_globalCut_infinite_of_escaping ω hesc⟩



theorem bc32_bundledRootedDownArmForest_of_escapingDownArmData (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (rank : Site d → ℕ ×ₗ ℕ)
    (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x ≠ rank y)
    (h : bc32_EscapingDownArmData ω n rank) :
    bc29_BundledRootedDownArmForest ω n :=
  bc30_bundledRootedDownArmForest_of_data ω n rank hinj
    (bc32_globalCutDownArmData_of_escapingDownArmData ω n rank h)


theorem bc32_Tcount_le_boundary_of_escapingDownArmData (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n) (rank : Site d → ℕ ×ₗ ℕ)
    (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x ≠ rank y)
    (h : bc32_EscapingDownArmData ω n rank) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc30_Tcount_le_boundary_of_data ω n hn rank hinj
    (bc32_globalCutDownArmData_of_escapingDownArmData ω n rank h)





















theorem bc32_escapingDownArmData_of_threeChain (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ m g : Site d} (b : Site d → Site d)
    (hx0box : x₀ ∈ box d n) (hmbox : m ∈ box d n) (hgbox : g ∈ box d n)
    (hx0m : x₀ ≠ m) (hx0g : x₀ ≠ g) (hmg : m ≠ g)
    (hthree : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (∀ mm : ℕ, ∃ z, z ∉ box d mm ∧
        ∃ w : (openSubgraph d (removeSite x₀ ω)).Walk (b x₀) z,
          ∀ v ∈ w.support, v ∉ tfc_trifFinset ω n))
    (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧
      (∀ mm : ℕ, ∃ z, z ∉ box d mm ∧
        ∃ w : (openSubgraph d (removeSite m ω)).Walk (b m) z,
          ∀ v ∈ w.support, v ∉ tfc_trifFinset ω n))
    (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧
      (∀ mm : ℕ, ∃ z, z ∉ box d mm ∧
        ∃ w : (openSubgraph d (removeSite g ω)).Walk (b g) z,
          ∀ v ∈ w.support, v ∉ tfc_trifFinset ω n))
    (hsxm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
    (hsxg : ¬ Connected d (removeSite g ω) (b g) (b x₀))
    (hsmg : ¬ Connected d (removeSite g ω) (b g) (b m)) :
    bc32_EscapingDownArmData ω n
      (fun z => if z = x₀ then toLex (0, 0)
                else if z = m then toLex (1, 0) else toLex (2, 0)) := by
  classical
  set dep : Site d → ℕ := fun z => if z = x₀ then 0 else if z = m then 1 else 2 with hdep
  have hdepx0 : dep x₀ = 0 := by simp [hdep]
  have hdepm : dep m = 1 := by simp [hdep, hx0m.symm]
  have hdepg : dep g = 2 := by simp [hdep, hx0g.symm, hmg.symm]
  have hrankeq : (fun z : Site d => if z = x₀ then toLex (0, 0)
        else if z = m then toLex (1, 0) else toLex (2, 0))
      = fun z => toLex (dep z, 0) := by
    funext z; simp only [hdep]; split_ifs <;> rfl
  rw [show (fun z : Site d => if z = x₀ then toLex (0, 0)
        else if z = m then toLex (1, 0) else toLex (2, 0))
      = fun z => toLex (dep z, 0) from hrankeq]
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    rcases hthree x hxbox htri with rfl | rfl | rfl
    · exact hbx0
    · exact hbm
    · exact hbg
  · intro x hxbox htri y hybox htriy hxy _ hlt
    rcases hthree x hxbox htri with rfl | rfl | rfl <;>
      rcases hthree y hybox htriy with rfl | rfl | rfl
    · exact absurd rfl hxy
    · exact hsxm
    · exact hsxg
    · simp only [] at hlt; rw [hdepm, hdepx0] at hlt
      exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · exact absurd rfl hxy
    · exact hsmg
    · simp only [] at hlt; rw [hdepg, hdepx0] at hlt
      exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · simp only [] at hlt; rw [hdepg, hdepm] at hlt
      exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · exact absurd rfl hxy



















theorem bc32_escapingDownArmData_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (b : Site d → Site d)
    (hx0box : x₀ ∈ box d n)
    (hydata : ∀ i, y i ∈ box d n ∧ x₀ ≠ y i ∧ Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (∀ mm : ℕ, ∃ z, z ∉ box d mm ∧
        ∃ w : (openSubgraph d (removeSite x₀ ω)).Walk (b x₀) z,
          ∀ v ∈ w.support, v ∉ tfc_trifFinset ω n))
    (hby : ∀ i, b (y i) ∈ box d n ∧ Connected d ω (y i) (b (y i)) ∧
      (∀ mm : ℕ, ∃ z, z ∉ box d mm ∧
        ∃ w : (openSubgraph d (removeSite (y i) ω)).Walk (b (y i)) z,
          ∀ v ∈ w.support, v ∉ tfc_trifFinset ω n))
    (hsx0 : ∀ i, ¬ Connected d (removeSite (y i) ω) (b (y i)) (b x₀))
    (hssib : ∀ i j : Fin 3, (j : ℕ) < i →
      ¬ Connected d (removeSite (y i) ω) (b (y i)) (b (y j))) :
    bc32_EscapingDownArmData ω n
      (fun z => if z = x₀ then toLex (0, 0)
                else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0)) := by
  classical
  set rank : Site d → ℕ ×ₗ ℕ := fun z =>
    if z = x₀ then toLex (0, 0)
    else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0) with hrank
  have hrx0 : rank x₀ = toLex (0, 0) := by simp only [hrank, if_pos rfl]
  have hry : ∀ i, rank (y i) = toLex (1, (i : ℕ)) := by
    intro i
    have hne : y i ≠ x₀ := (hydata i).2.1.symm
    have hex : ∃ k, y i = y k := ⟨i, rfl⟩
    have hchoose : hex.choose = i := hyinj hex.choose_spec.symm
    simp only [hrank, if_neg hne, dif_pos hex, hchoose]
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    rcases hsingle x hxbox htri with rfl | ⟨i, rfl⟩
    · exact hbx0
    · exact hby i
  · intro x hxbox htri yv hyvbox htriv hxy hconn hlt
    rcases hsingle yv hyvbox htriv with rfl | ⟨i, rfl⟩
    · rcases hsingle x hxbox htri with rfl | ⟨j, rfl⟩
      · exact absurd rfl hxy
      · rw [hry j, hrx0] at hlt; exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · rcases hsingle x hxbox htri with rfl | ⟨j, rfl⟩
      · exact hsx0 i
      · rw [hry j, hry i] at hlt
        have hji : (j : ℕ) < i := by
          rw [Prod.Lex.toLex_lt_toLex] at hlt
          rcases hlt with h | ⟨_, h⟩
          · exact absurd h (lt_irrefl 1)
          · exact h
        exact hssib i j hji





















theorem bc32_pos_edge_open (k : ℤ) (hk : 1 ≤ k) :
    (openSubgraph 2 (removeSite (arc_p (-2)) arc_rayConfig)).Adj (arc_p k) (arc_p (k+1)) := by
  refine ⟨arc_p_adj k, ?_⟩
  have hnm : arc_p (-2) ∉ (s(arc_p k, arc_p (k+1)) : Sym2 (Site 2)) := by
    rw [Sym2.mem_iff]
    rintro (h | h)
    · have := arc_p_inj h; omega
    · have := arc_p_inj h; omega
  rw [removeSite_apply_of_notMem hnm]
  exact arc_ray_open k (by omega)




theorem bc32_pos_walk (j : ℕ) :
    ∃ w : (openSubgraph 2 (removeSite (arc_p (-2)) arc_rayConfig)).Walk
        (arc_p 1) (arc_p (1 + (j:ℤ))),
      ∀ v ∈ w.support, ∃ k : ℤ, 1 ≤ k ∧ v = arc_p k := by
  induction j with
  | zero =>
    refine ⟨(SimpleGraph.Walk.nil).copy rfl (by norm_num), ?_⟩
    intro v hv
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
    exact ⟨1, by norm_num, by rw [hv]⟩
  | succ i ih =>
    obtain ⟨w, hw⟩ := ih
    have hadj : (openSubgraph 2 (removeSite (arc_p (-2)) arc_rayConfig)).Adj
        (arc_p (1 + (i:ℤ))) (arc_p (1 + (i:ℤ) + 1)) := bc32_pos_edge_open (1 + i) (by omega)
    have hcast : (arc_p (1 + (i:ℤ) + 1)) = arc_p (1 + ((i : ℕ) + 1 : ℤ)) := by
      norm_cast
    refine ⟨(w.concat hadj).copy rfl hcast, ?_⟩
    intro v hv
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_concat, List.mem_append] at hv
    rcases hv with hv | hv
    · exact hw v hv
    · simp only [List.mem_singleton] at hv
      exact ⟨1 + (i:ℤ) + 1, by omega, by rw [hv]⟩


theorem bc32_arc_outside (j : ℕ) : arc_p (1 + (j:ℤ)) ∉ box 2 j := by
  rw [mem_box, not_forall]; refine ⟨0, ?_⟩
  rw [not_le]; simp only [arc_p, Matrix.cons_val_zero]
  have : ((1 + (j:ℤ))).natAbs = 1 + j := by omega
  omega










theorem bc32_escapingClause_nonvacuous :
    ∃ (ω : ConfigSpace (Sym2 (Site 2))) (x a : Site 2) (T : Finset (Site 2)),
      a ∉ T ∧ x ∈ T ∧
      (∀ m : ℕ, ∃ z, z ∉ box 2 m ∧
        ∃ w : (openSubgraph 2 (removeSite x ω)).Walk a z, ∀ v ∈ w.support, v ∉ T) := by
  classical
  refine ⟨arc_rayConfig, arc_p (-2), arc_p 1, {arc_p (-2)}, ?_, ?_, ?_⟩
  · simp only [Finset.mem_singleton]; intro h; have := arc_p_inj h; omega
  · simp
  · intro m
    obtain ⟨w, hw⟩ := bc32_pos_walk m
    refine ⟨arc_p (1 + (m:ℤ)), bc32_arc_outside m, w, ?_⟩
    intro v hv
    obtain ⟨k, _hk, rfl⟩ := hw v hv
    simp only [Finset.mem_singleton]; intro h; have := arc_p_inj h; omega

end StatMech.Walls
