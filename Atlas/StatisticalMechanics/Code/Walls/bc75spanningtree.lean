/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































































































import Mathlib
import Code.Walls.bc74disjointforest
import Code.Percolation.OpenSpanningForestClose
import Code.Percolation.SingleLeafHallClose

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








open Classical in



noncomputable def bc75_collapseFiber (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) : Site d → Site d :=
  fun x => if h : ∃ y ∈ bc73_fiber ω L R c, x ∈ bc61_boxAround d L y
           then h.choose else x



theorem bc75_collapseFiber_eq {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {c : Fin d → Fin (2 * L + 1)} {x y : Site d}
    (hy : y ∈ bc73_fiber ω L R c) (hx : x ∈ bc61_boxAround d L y) :
    bc75_collapseFiber ω L R c x = y := by
  classical
  have hex : ∃ y' ∈ bc73_fiber ω L R c, x ∈ bc61_boxAround d L y' := ⟨y, hy, hx⟩
  unfold bc75_collapseFiber
  rw [dif_pos hex]
  
  obtain ⟨hzmem, hzx⟩ := hex.choose_spec
  by_contra hne
  exact Finset.disjoint_left.mp
    (bc73_fiber_pairwise_disjoint ω L R c hzmem hy hne) hzx hx


theorem bc75_collapseFiber_id {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {c : Fin d → Fin (2 * L + 1)} {x : Site d}
    (hx : ∀ y ∈ bc73_fiber ω L R c, x ∉ bc61_boxAround d L y) :
    bc75_collapseFiber ω L R c x = x := by
  classical
  unfold bc75_collapseFiber
  rw [dif_neg]
  rintro ⟨y, hy, hxy⟩
  exact hx y hy hxy


theorem bc75_collapseFiber_center {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {c : Fin d → Fin (2 * L + 1)} {y : Site d} (hy : y ∈ bc73_fiber ω L R c) :
    bc75_collapseFiber ω L R c y = y :=
  bc75_collapseFiber_eq hy (bc72_y_mem_box L y)




theorem bc75_collapseFiber_mem_box_of_eq_center {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {c : Fin d → Fin (2 * L + 1)} {x y : Site d} (hy : y ∈ bc73_fiber ω L R c)
    (hxy : bc75_collapseFiber ω L R c x = y) :
    x ∈ bc61_boxAround d L y := by
  classical
  by_cases hex : ∃ y' ∈ bc73_fiber ω L R c, x ∈ bc61_boxAround d L y'
  · 
    obtain ⟨hzmem, hzx⟩ := hex.choose_spec
    have : bc75_collapseFiber ω L R c x = hex.choose := by
      unfold bc75_collapseFiber; rw [dif_pos hex]
    rw [this] at hxy
    rw [← hxy]; exact hzx
  · 
    have hex' : ∀ y' ∈ bc73_fiber ω L R c, x ∉ bc61_boxAround d L y' := by
      intro y' hy' hxy'; exact hex ⟨y', hy', hxy'⟩
    have hxx : bc75_collapseFiber ω L R c x = x := bc75_collapseFiber_id hex'
    rw [hxx] at hxy; rw [hxy]; exact bc72_y_mem_box L y











noncomputable def bc75_fiberQuot (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) : SimpleGraph (Site d) :=
  bc72_quotGraph (openSubgraph d ω) (bc75_collapseFiber ω L R c)






theorem bc75_arm_adjacent_hub {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {c : Fin d → Fin (2 * L + 1)} {y a : Site d}
    (hy : y ∈ bc73_fiber ω L R c) (hinc : bc67_GnIncident ω L y a)
    (hane : bc75_collapseFiber ω L R c a = a) (hay : a ≠ y) :
    (bc75_fiberQuot ω L R c).Adj y a := by
  obtain ⟨b, hbbox, hadj⟩ := hinc
  refine ⟨hay.symm, b, a, ?_, hane, hadj⟩
  exact bc75_collapseFiber_eq hy hbbox




theorem bc75_fiberQuot_adj_iff {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {c : Fin d → Fin (2 * L + 1)} {u v : Site d} :
    (bc75_fiberQuot ω L R c).Adj u v ↔
      u ≠ v ∧ ∃ p q, bc75_collapseFiber ω L R c p = u ∧
        bc75_collapseFiber ω L R c q = v ∧ (openSubgraph d ω).Adj p q :=
  Iff.rfl














theorem bc75_gnCut_of_doubleInduce {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {c : Fin d → Fin (2 * L + 1)} {y : Site d} {S : Set (Site d)} (hyS : y ∈ S)
    {a₁ a₂ : (↑S : Type)} (h1 : a₁ ≠ ⟨y, hyS⟩) (h2 : a₂ ≠ ⟨y, hyS⟩)
    (h : (((bc75_fiberQuot ω L R c).induce S).induce
        ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
      ⟨a₁, by simpa using h1⟩ ⟨a₂, by simpa using h2⟩) :
    ((bc75_fiberQuot ω L R c).induce ({y}ᶜ : Set (Site d))).Reachable
      ⟨(a₁ : Site d), by simpa using fun hh => h1 (Subtype.ext hh)⟩
      ⟨(a₂ : Site d), by simpa using fun hh => h2 (Subtype.ext hh)⟩ := by
  obtain ⟨w⟩ := h
  set Q := bc75_fiberQuot ω L R c with hQ
  
  set g : (((Q.induce S).induce ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type)))) →g
        (Q.induce ({y}ᶜ : Set (Site d))) :=
    { toFun := fun u => ⟨(u.1.1 : Site d), by
        have : u.1 ≠ (⟨y, hyS⟩ : (↑S : Type)) := u.2
        simpa using fun hh => this (Subtype.ext hh)⟩
      map_rel' := fun {u v} huv => huv } with hg
  exact ⟨w.map g⟩













noncomputable def bc75_fiberQuotBox (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) : SimpleGraph (↑S : Type) :=
  (bc75_fiberQuot ω L R c).induce S



noncomputable def bc75_spanForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] :
    SimpleGraph (↑S : Type) :=
  osf_spanForest (bc75_fiberQuotBox ω L R c S)


theorem bc75_spanForest_acyclic (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] :
    (bc75_spanForest ω L R c S).IsAcyclic :=
  osf_spanForest_acyclic (bc75_fiberQuotBox ω L R c S)


theorem bc75_spanForest_le (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] :
    bc75_spanForest ω L R c S ≤ bc75_fiberQuotBox ω L R c S :=
  osf_spanForest_le (bc75_fiberQuotBox ω L R c S)


theorem bc75_spanForest_reachable_of (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)]
    {u v : (↑S : Type)} (h : (bc75_fiberQuotBox ω L R c S).Reachable u v) :
    (bc75_spanForest ω L R c S).Reachable u v :=
  osf_spanForest_reachable_of (bc75_fiberQuotBox ω L R c S) h

open Classical in








theorem bc75_deg3_in_spanForest_of_gnCut (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) {y : Site d} {S : Set (Site d)} [Fintype (↑S : Type)]
    (hyS : y ∈ S) {v₁ v₂ v₃ : (↑S : Type)}
    (hadj₁ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS⟩ v₁)
    (hadj₂ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS⟩ v₂)
    (hadj₃ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS⟩ v₃)
    (hcut₁₂ : ¬ ((bc75_fiberQuotBox ω L R c S).induce
        ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
      ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₁).symm⟩
      ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₂).symm⟩)
    (hcut₁₃ : ¬ ((bc75_fiberQuotBox ω L R c S).induce
        ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
      ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₁).symm⟩
      ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₃).symm⟩)
    (hcut₂₃ : ¬ ((bc75_fiberQuotBox ω L R c S).induce
        ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
      ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₂).symm⟩
      ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₃).symm⟩) :
    3 ≤ (bc75_spanForest ω L R c S).degree ⟨y, hyS⟩ := by
  classical
  set F := bc75_spanForest ω L R c S with hF
  set Q := bc75_fiberQuotBox ω L R c S with hQ
  
  have hne₁ : (⟨y, hyS⟩ : (↑S : Type)) ≠ v₁ := Q.ne_of_adj hadj₁
  have hne₂ : (⟨y, hyS⟩ : (↑S : Type)) ≠ v₂ := Q.ne_of_adj hadj₂
  have hne₃ : (⟨y, hyS⟩ : (↑S : Type)) ≠ v₃ := Q.ne_of_adj hadj₃
  
  have hr₁ : F.Reachable ⟨y, hyS⟩ v₁ := bc75_spanForest_reachable_of ω L R c S hadj₁.reachable
  have hr₂ : F.Reachable ⟨y, hyS⟩ v₂ := bc75_spanForest_reachable_of ω L R c S hadj₂.reachable
  have hr₃ : F.Reachable ⟨y, hyS⟩ v₃ := bc75_spanForest_reachable_of ω L R c S hadj₃.reachable
  
  refine slh_deg_ge_three_of_cut hr₁ hr₂ hr₃ hne₁ hne₂ hne₃ ?_ ?_ ?_
  · intro hr; exact hcut₁₂ (hr.mono (fun a b hab => (bc75_spanForest_le ω L R c S) hab))
  · intro hr; exact hcut₁₃ (hr.mono (fun a b hab => (bc75_spanForest_le ω L R c S) hab))
  · intro hr; exact hcut₂₃ (hr.mono (fun a b hab => (bc75_spanForest_le ω L R c S) hab))














open Classical in











def bc75_FiberGnTrifData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) : Prop :=
  ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (_ : Nonempty (↑S : Type))
    (hyS : ∀ y ∈ bc73_fiber ω L R c, y ∈ S),
    (∀ y (hy : y ∈ bc73_fiber ω L R c),
      ∃ (v₁ v₂ v₃ : (↑S : Type))
        (h₁ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS y hy⟩ v₁)
        (h₂ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS y hy⟩ v₂)
        (h₃ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS y hy⟩ v₃),
        ¬ (((bc75_fiberQuotBox ω L R c S).induce
              ({(⟨y, hyS y hy⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
            ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₁).symm⟩
            ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₂).symm⟩) ∧
        ¬ (((bc75_fiberQuotBox ω L R c S).induce
              ({(⟨y, hyS y hy⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
            ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₁).symm⟩
            ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₃).symm⟩) ∧
        ¬ (((bc75_fiberQuotBox ω L R c S).induce
              ({(⟨y, hyS y hy⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
            ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₂).symm⟩
            ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₃).symm⟩)) ∧
    (∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v) ∧
    (∀ v : (↑S : Type), (bc75_spanForest ω L R c S).degree v = 1 → (v : Site d) ∈ vertexBoundary d R)









open Classical in






theorem bc75_fiberForest_of_gnTrifData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (h : bc75_FiberGnTrifData ω L R c) :
    bc74_FiberForest ω L R c := by
  classical
  obtain ⟨S, hSfin, hSne, hyS, htriData, hmin, hleaf⟩ := h
  
  set w₀ : (↑S : Type) := hSne.some with hw₀
  set ιU : Site d → (↑S : Type) :=
    fun y => if hy : y ∈ bc73_fiber ω L R c then ⟨y, hyS y hy⟩ else w₀ with hιU
  have hιUeq : ∀ y (hy : y ∈ bc73_fiber ω L R c), ιU y = ⟨y, hyS y hy⟩ := by
    intro y hy; simp only [hιU, dif_pos hy]
  refine ⟨S, hSfin, hSne, bc75_spanForest ω L R c S, Classical.decRel _, ιU,
    bc75_spanForest_acyclic ω L R c S, hmin, ?_, ?_, hleaf⟩
  · 
    intro y hy
    rw [hιUeq y hy]
    obtain ⟨v₁, v₂, v₃, h₁, h₂, h₃, hc₁₂, hc₁₃, hc₂₃⟩ := htriData y hy
    exact bc75_deg3_in_spanForest_of_gnCut ω L R c (hyS y hy) h₁ h₂ h₃ hc₁₂ hc₁₃ hc₂₃
  · 
    intro y hy z hz hyz
    rw [hιUeq y hy, hιUeq z hz] at hyz
    exact congrArg Subtype.val hyz




theorem bc75_fiber_count_of_gnTrifData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (h : bc75_FiberGnTrifData ω L R c) :
    (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R :=
  bc74_fiber_count_of_fiberForest ω L R c (bc75_fiberForest_of_gnTrifData ω L R c h)





theorem bc75_sublatticeForest_of_gnTrifData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : ∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) :
    bc73_SublatticeForest ω L R :=
  fun c => bc75_fiber_count_of_gnTrifData ω L R c (h c)













theorem bc75_emptyFiber_collapse_id (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (hempty : bc73_fiber ω L R c = ∅) (x : Site d) :
    bc75_collapseFiber ω L R c x = x := by
  apply bc75_collapseFiber_id
  intro y hy; rw [hempty] at hy; exact absurd hy (Finset.notMem_empty y)




theorem bc75_emptyFiber_box_adj (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (hempty : bc73_fiber ω L R c = ∅)
    {z₀ z₁ : Site d} (hopen : (openSubgraph d ω).Adj z₀ z₁)
    (hz₀ : z₀ ∈ ({z₀, z₁} : Set (Site d))) (hz₁ : z₁ ∈ ({z₀, z₁} : Set (Site d))) :
    (bc75_fiberQuotBox ω L R c ({z₀, z₁} : Set (Site d))).Adj ⟨z₀, hz₀⟩ ⟨z₁, hz₁⟩ := by
  have hne : z₀ ≠ z₁ := (openSubgraph d ω).ne_of_adj hopen
  
  change (bc75_fiberQuot ω L R c).Adj z₀ z₁
  exact ⟨hne, z₀, z₁, bc75_emptyFiber_collapse_id ω L R c hempty z₀,
    bc75_emptyFiber_collapse_id ω L R c hempty z₁, hopen⟩

open Classical in






theorem bc75_fiberGnTrifData_of_emptyFiber (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (hempty : bc73_fiber ω L R c = ∅)
    {z₀ z₁ : Site d} (hz₀b : z₀ ∈ vertexBoundary d R) (hz₁b : z₁ ∈ vertexBoundary d R)
    (hopen : (openSubgraph d ω).Adj z₀ z₁) :
    bc75_FiberGnTrifData ω L R c := by
  classical
  set S : Set (Site d) := {z₀, z₁} with hSdef
  have hz₀S : z₀ ∈ S := by rw [hSdef]; left; rfl
  have hz₁S : z₁ ∈ S := by rw [hSdef]; right; rfl
  have hne : z₀ ≠ z₁ := (openSubgraph d ω).ne_of_adj hopen
  haveI hSfin : Fintype (↑S : Type) := (Set.toFinite S).fintype
  
  have hVall : ∀ v : (↑S : Type), v = ⟨z₀, hz₀S⟩ ∨ v = ⟨z₁, hz₁S⟩ := by
    intro v; obtain ⟨x, hx⟩ := v
    rw [hSdef, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · left; rfl
    · right; rfl
  
  have hcard2 : ENat.card (↑S : Type) ≤ 2 := by
    rw [ENat.card_eq_coe_natCard]
    have : Nat.card (↑S : Type) ≤ 2 := by
      have hle : (S : Set (Site d)).ncard ≤ 2 := by
        rw [hSdef]; exact (Set.ncard_insert_le _ _).trans (by simp [Set.ncard_singleton])
      simpa [Nat.card_coe_set_eq] using hle
    exact_mod_cast this
  have hGac : (bc75_fiberQuotBox ω L R c S).IsAcyclic := SimpleGraph.IsAcyclic.of_card_le_two hcard2
  
  have hSF : bc75_spanForest ω L R c S = bc75_fiberQuotBox ω L R c S :=
    osf_spanForest_of_acyclic (bc75_fiberQuotBox ω L R c S) hGac
  
  have hedge : (bc75_fiberQuotBox ω L R c S).Adj ⟨z₀, hz₀S⟩ ⟨z₁, hz₁S⟩ :=
    bc75_emptyFiber_box_adj ω L R c hempty hopen hz₀S hz₁S
  haveI hGdec : DecidableRel (bc75_fiberQuotBox ω L R c S).Adj := Classical.decRel _
  have hne' : (⟨z₀, hz₀S⟩ : (↑S : Type)) ≠ ⟨z₁, hz₁S⟩ := fun h => hne (Subtype.ext_iff.mp h)
  
  have hns₀ : (bc75_fiberQuotBox ω L R c S).neighborSet ⟨z₀, hz₀S⟩ = {⟨z₁, hz₁S⟩} := by
    ext w; rw [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
    rcases hVall w with rfl | rfl
    · exact ⟨fun h => absurd rfl ((bc75_fiberQuotBox ω L R c S).ne_of_adj h), fun h =>
        absurd h fun hh => hne' (by rw [hh])⟩
    · exact ⟨fun _ => rfl, fun _ => hedge⟩
  have hns₁ : (bc75_fiberQuotBox ω L R c S).neighborSet ⟨z₁, hz₁S⟩ = {⟨z₀, hz₀S⟩} := by
    ext w; rw [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
    rcases hVall w with rfl | rfl
    · exact ⟨fun _ => rfl, fun _ => hedge.symm⟩
    · exact ⟨fun h => absurd rfl ((bc75_fiberQuotBox ω L R c S).ne_of_adj h), fun h =>
        absurd h fun hh => hne' (by rw [hh])⟩
  
  have hdeg : ∀ v : (↑S : Type), (bc75_spanForest ω L R c S).degree v = 1 := by
    intro v
    rw [hSF, SimpleGraph.degree, SimpleGraph.neighborFinset_def]
    rcases hVall v with rfl | rfl
    · simp only [hns₀, Set.toFinset_singleton, Finset.card_singleton]
    · simp only [hns₁, Set.toFinset_singleton, Finset.card_singleton]
  refine ⟨S, hSfin, ⟨⟨z₀, hz₀S⟩⟩, ?_, ?_, ?_, ?_⟩
  · 
    intro y hy; rw [hempty] at hy; exact absurd hy (Finset.notMem_empty y)
  · 
    intro y hy; rw [hempty] at hy; exact absurd hy (Finset.notMem_empty y)
  · 
    intro v; rw [hdeg v]
  · 
    intro v _
    rcases hVall v with rfl | rfl
    · exact hz₀b
    · exact hz₁b




theorem bc75_sublatticeForest_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀b : z₀ ∈ vertexBoundary d R) (hz₁b : z₁ ∈ vertexBoundary d R)
    (hopen : (openSubgraph d ω).Adj z₀ z₁) (hno : bc61_coarseTrifFinset ω L R = ∅) :
    bc73_SublatticeForest ω L R := by
  classical
  refine bc75_sublatticeForest_of_gnTrifData ω L R (fun c => ?_)
  have hfib : bc73_fiber ω L R c = ∅ := by rw [bc73_fiber, hno]; simp
  exact bc75_fiberGnTrifData_of_emptyFiber ω L R c hfib hz₀b hz₁b hopen















theorem bc75_bk_count_closed_of_gnTrifData
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hexp : ∀ R : ℕ,
      ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
    (hData : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ) (c : Fin d → Fin (2 * L + 1)),
      bc75_FiberGnTrifData ω L R c)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc73_infiniteClusters_top_null μ hd L hexp
    (fun ω R => bc75_sublatticeForest_of_gnTrifData ω L R (fun c => hData ω R c)) hexist

















theorem bc75_upperLines_openBoundaryEdge {R : ℕ} (hR : 1 ≤ R) :
    (bc57_pt 0 (R : ℤ) ∈ vertexBoundary 2 R) ∧ (bc57_pt 1 (R : ℤ) ∈ vertexBoundary 2 R) ∧
      (openSubgraph 2 bc60_upperLines).Adj (bc57_pt 0 (R : ℤ)) (bc57_pt 1 (R : ℤ)) := by
  refine ⟨?_, ?_, ?_⟩
  · 
    rw [vertexBoundary, Set.mem_diff]
    refine ⟨?_, ?_⟩
    · rw [mem_box]; intro i; fin_cases i
      · change ((bc57_pt 0 (R : ℤ)) 0).natAbs ≤ R; rw [bc57_pt_fst]; simp
      · change ((bc57_pt 0 (R : ℤ)) 1).natAbs ≤ R; rw [bc57_pt_snd]; simp
    · rw [mem_box]; simp only [not_forall, not_le]
      refine ⟨1, ?_⟩
      have : ((bc57_pt 0 (R : ℤ)) 1).natAbs = R := by rw [bc57_pt_snd]; exact Int.natAbs_natCast R
      rw [this]; omega
  · 
    rw [vertexBoundary, Set.mem_diff]
    refine ⟨?_, ?_⟩
    · rw [mem_box]; intro i; fin_cases i
      · change ((bc57_pt 1 (R : ℤ)) 0).natAbs ≤ R; rw [bc57_pt_fst]; simp; omega
      · change ((bc57_pt 1 (R : ℤ)) 1).natAbs ≤ R; rw [bc57_pt_snd]; simp
    · rw [mem_box]; simp only [not_forall, not_le]
      refine ⟨1, ?_⟩
      have : ((bc57_pt 1 (R : ℤ)) 1).natAbs = R := by rw [bc57_pt_snd]; exact Int.natAbs_natCast R
      rw [this]; omega
  · 
    rw [openSubgraph_adj]
    refine ⟨?_, ?_⟩
    · 
      rw [hypercubicLattice_adj]
      rw [Fin.sum_univ_two]
      simp only [bc57_pt_fst, bc57_pt_snd]
      norm_num
    · 
      have := bc60_open 0 (h := (R : ℤ)) (by exact_mod_cast hR)
      simpa using this





theorem bc75_upperLines_emptyFiber_gnTrifData {L R : ℕ} (hR : 1 ≤ R)
    (c : Fin 2 → Fin (2 * L + 1)) (hempty : bc73_fiber bc60_upperLines L R c = ∅) :
    bc75_FiberGnTrifData bc60_upperLines L R c := by
  obtain ⟨hb0, hb1, hopen⟩ := bc75_upperLines_openBoundaryEdge hR
  exact bc75_fiberGnTrifData_of_emptyFiber bc60_upperLines L R c hempty hb0 hb1 hopen











theorem bc75_upperLines_gnCut_needs_buffer (L : ℕ) :
    Disjoint (bc61_boxAround 2 L (0 : Site 2))
        (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
      Connected 2 bc60_upperLines
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) :=
  bc74_upperLines_arms_can_share_boundary L


























theorem bc75_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (c : Fin d → Fin (2 * L + 1))
      (S : Set (Site d)) (_ : Fintype (↑S : Type)), (bc75_spanForest ω L R c S).IsAcyclic) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (c : Fin d → Fin (2 * L + 1)),
      bc75_FiberGnTrifData ω L R c → (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      (∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) →
      bc73_SublatticeForest ω L R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω L R c S _; exact bc75_spanForest_acyclic ω L R c S
  · intro ω L R c h; exact bc75_fiber_count_of_gnTrifData ω L R c h
  · intro ω L R h; exact bc75_sublatticeForest_of_gnTrifData ω L R h

end StatMech.Walls
