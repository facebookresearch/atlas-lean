/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































































import Mathlib
import Code.Walls.bc63coarseforest

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}












theorem bc64_boxAround_disjoint_of_farCoord {L : ℕ} {y y' : Site d} (i : Fin d)
    (hfar : 2 * L < ((y - y') i).natAbs) :
    Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y') := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [bc61_mem_boxAround, mem_box] at hx hx'
  have h1 : ((x - y) i).natAbs ≤ L := hx i
  have h2 : ((x - y') i).natAbs ≤ L := hx' i
  
  have hsub : (y - y') i = (x - y') i - (x - y) i := by
    simp only [Pi.sub_apply]; ring
  have hle : ((y - y') i).natAbs ≤ ((x - y') i).natAbs + ((x - y) i).natAbs := by
    rw [hsub]; exact Int.natAbs_sub_le _ _
  omega





theorem bc64_boxAround_disjoint_of_far {L : ℕ} {y y' : Site d}
    (hfar : ∃ i, 2 * L < ((y - y') i).natAbs) :
    Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y') := by
  obtain ⟨i, hi⟩ := hfar
  exact bc64_boxAround_disjoint_of_farCoord i hi



theorem bc64_notMem_both_of_far {L : ℕ} {y y' x : Site d} (i : Fin d)
    (hfar : 2 * L < ((y - y') i).natAbs)
    (hx : x ∈ bc61_boxAround d L y) : x ∉ bc61_boxAround d L y' := by
  intro hx'
  exact (Finset.disjoint_left.mp (bc64_boxAround_disjoint_of_farCoord i hfar) hx) hx'














def bc64_starE (i j : Fin 4) : Prop := (i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0)

instance : DecidableRel bc64_starE := fun i j => by unfold bc64_starE; infer_instance


def bc64_starG : SimpleGraph (Fin 4) := SimpleGraph.fromRel bc64_starE

instance : DecidableRel bc64_starG.Adj := by unfold bc64_starG fromRel; intro a b; infer_instance


theorem bc64_starG_isTree : bc64_starG.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  exact ⟨by rw [SimpleGraph.connected_iff_exists_forall_reachable]; exact ⟨0, by decide⟩,
    by rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide⟩


theorem bc64_starG_centre_deg : bc64_starG.degree 0 = 3 := by decide


theorem bc64_starG_leaf_deg : ∀ i : Fin 4, i ≠ 0 → bc64_starG.degree i = 1 := by decide


theorem bc64_starG_deg1_iff (i : Fin 4) : bc64_starG.degree i = 1 ↔ i ≠ 0 := by
  constructor
  · intro h; rintro rfl; rw [bc64_starG_centre_deg] at h; exact absurd h (by decide)
  · exact bc64_starG_leaf_deg i




def bc64_starForest (β : Type) : SimpleGraph (β × Fin 4) :=
  SimpleGraph.fromRel (fun p q => p.1 = q.1 ∧ bc64_starG.Adj p.2 q.2)

noncomputable instance (β : Type) : DecidableRel (bc64_starForest β).Adj := Classical.decRel _



theorem bc64_starForest_adj_iff {β : Type} {p q : β × Fin 4} :
    (bc64_starForest β).Adj p q ↔ (p.1 = q.1 ∧ bc64_starG.Adj p.2 q.2) := by
  unfold bc64_starForest SimpleGraph.fromRel
  constructor
  · rintro ⟨hne, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact ⟨h1, h2⟩
    · exact ⟨h1.symm, bc64_starG.symm h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun hpq => (bc64_starG.ne_of_adj h2) (by rw [hpq]), Or.inl ⟨h1, h2⟩⟩


theorem bc64_starForest_fst {β : Type} {p q : β × Fin 4} (h : (bc64_starForest β).Adj p q) :
    p.1 = q.1 := (bc64_starForest_adj_iff.mp h).1


def bc64_sndHom (β : Type) : bc64_starForest β →g bc64_starG where
  toFun := Prod.snd
  map_rel' := fun h => (bc64_starForest_adj_iff.mp h).2


theorem bc64_walk_fst_const {β : Type} {p q : β × Fin 4} (w : (bc64_starForest β).Walk p q) :
    ∀ v ∈ w.support, v.1 = p.1 := by
  induction w with
  | nil => intro v hv; simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv; rw [hv]
  | @cons a b c hadj w' ih =>
    intro v hv
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · rfl
    · rw [ih v hv]; exact (bc64_starForest_fst hadj).symm



theorem bc64_snd_injOn_support {β : Type} {v : β × Fin 4} (c : (bc64_starForest β).Walk v v) :
    Set.InjOn (Prod.snd : β × Fin 4 → Fin 4) {x | x ∈ c.support} := by
  intro a ha b hb hab
  exact Prod.ext ((bc64_walk_fst_const c a ha).trans (bc64_walk_fst_const c b hb).symm) hab





theorem bc64_starForest_acyclic (β : Type) : (bc64_starForest β).IsAcyclic := by
  intro v c hc
  have hinj := bc64_snd_injOn_support c
  have hcm : (c.map (bc64_sndHom β)).IsCycle := by
    rw [SimpleGraph.Walk.isCycle_def] at hc ⊢
    obtain ⟨htr, hne, hnodup⟩ := hc
    refine ⟨?_, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isTrail_def] at htr ⊢
      rw [SimpleGraph.Walk.edges_map]
      apply List.Nodup.map_on _ htr
      intro e1 he1 e2 he2 hee
      induction e1 using Sym2.ind with | _ a1 b1 =>
      induction e2 using Sym2.ind with | _ a2 b2 =>
      simp only [Sym2.map_mk] at hee
      have ha1 : a1 ∈ c.support := c.fst_mem_support_of_mem_edges he1
      have hb1 : b1 ∈ c.support := c.snd_mem_support_of_mem_edges he1
      have ha2 : a2 ∈ c.support := c.fst_mem_support_of_mem_edges he2
      have hb2 : b2 ∈ c.support := c.snd_mem_support_of_mem_edges he2
      rw [Sym2.eq_iff] at hee ⊢
      rcases hee with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · left; exact ⟨hinj ha1 ha2 e1, hinj hb1 hb2 e2⟩
      · right; exact ⟨hinj ha1 hb2 e1, hinj hb1 ha2 e2⟩
    · intro h
      apply hne
      cases c with
      | nil => rfl
      | cons hh w => simp [SimpleGraph.Walk.map_cons] at h
    · rw [SimpleGraph.Walk.support_map, ← List.map_tail]
      apply List.Nodup.map_on _ hnodup
      intro x hx y hy hxy
      exact hinj (List.mem_of_mem_tail hx) (List.mem_of_mem_tail hy) hxy
  exact bc64_starG_isTree.isAcyclic (c.map (bc64_sndHom β)) hcm


theorem bc64_starForest_neighborFinset {β : Type} [DecidableEq β] [Fintype β] (t : β) (i : Fin 4) :
    (bc64_starForest β).neighborFinset (t, i) = ({t} : Finset β) ×ˢ (bc64_starG.neighborFinset i) := by
  classical
  ext ⟨t', j⟩
  simp only [SimpleGraph.mem_neighborFinset, bc64_starForest_adj_iff, Finset.mem_product,
    Finset.mem_singleton]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩⟩



theorem bc64_starForest_degree {β : Type} [DecidableEq β] [Fintype β] (t : β) (i : Fin 4) :
    (bc64_starForest β).degree (t, i) = bc64_starG.degree i := by
  classical
  rw [SimpleGraph.degree, bc64_starForest_neighborFinset, Finset.card_product,
    Finset.card_singleton, one_mul, SimpleGraph.degree]


theorem bc64_starForest_min_degree {β : Type} [DecidableEq β] [Fintype β] (v : β × Fin 4) :
    1 ≤ (bc64_starForest β).degree v := by
  obtain ⟨t, i⟩ := v
  rw [bc64_starForest_degree]
  by_cases hi : i = 0
  · rw [hi, bc64_starG_centre_deg]; omega
  · rw [bc64_starG_leaf_deg i hi]


theorem bc64_starForest_deg1_iff {β : Type} [DecidableEq β] [Fintype β] (t : β) (i : Fin 4) :
    (bc64_starForest β).degree (t, i) = 1 ↔ i ≠ 0 := by
  rw [bc64_starForest_degree]; exact bc64_starG_deg1_iff i






















def bc64_CoarseBoundaryInjection (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  ∃ lam : (↑(bc61_coarseTrifFinset ω L R) : Type) × Fin 4 → Site d,
    (∀ p : (↑(bc61_coarseTrifFinset ω L R) : Type) × Fin 4, p.2 ≠ 0 →
      lam p ∈ vertexBoundary d R) ∧
    Set.InjOn lam {p | p.2 ≠ 0}

open Classical in











theorem bc64_coarseArmEmbedding_of_boundaryInjection (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁) (hinj : bc64_CoarseBoundaryInjection ω L R) :
    bc63_CoarseArmEmbedding ω L R := by
  classical
  rw [bc63_coarseArmEmbedding_iff_forestLeafCount]
  set Tf := bc61_coarseTrifFinset ω L R with hTf
  rcases Finset.eq_empty_or_nonempty Tf with hemp | hne
  · 
    apply bc63_coarseForestLeafCount_of_noTrif ω L R hz₀ hz₁ hzne
    intro y hybox htri
    have hymem : y ∈ Tf := by rw [hTf, bc61_mem_coarseTrifFinset]; exact ⟨hybox, htri⟩
    rw [hemp] at hymem; exact absurd hymem (Finset.notMem_empty y)
  · 
    obtain ⟨lam, hlamB, hlamInj⟩ := hinj
    have hTfne : Nonempty (↑Tf : Type) := hne.to_subtype
    obtain ⟨t0, ht0⟩ := hne
    let W := (↑Tf : Type) × Fin 4
    let ιT : Site d → W := fun y =>
      if hy : y ∈ Tf then (⟨y, hy⟩, 0) else (⟨t0, ht0⟩, 0)
    refine ⟨W, inferInstance, ⟨(⟨t0, ht0⟩, 0)⟩, inferInstance, bc64_starForest (↑Tf : Type),
      inferInstance, ιT, lam, bc64_starForest_acyclic _, ?_, ?_, ?_, ?_, ?_⟩
    · 
      intro v; obtain ⟨t, i⟩ := v; exact bc64_starForest_min_degree (t, i)
    · 
      intro y hybox htri
      have hy : y ∈ Tf := by rw [hTf, bc61_mem_coarseTrifFinset]; exact ⟨hybox, htri⟩
      change 3 ≤ (bc64_starForest (↑Tf : Type)).degree (ιT y)
      have hιT : ιT y = (⟨y, hy⟩, (0 : Fin 4)) := dif_pos hy
      rw [hιT, bc64_starForest_degree, bc64_starG_centre_deg]
    · 
      intro y hybox htri z hzbox htriz hyz
      have hy : y ∈ Tf := by rw [hTf, bc61_mem_coarseTrifFinset]; exact ⟨hybox, htri⟩
      have hz : z ∈ Tf := by rw [hTf, bc61_mem_coarseTrifFinset]; exact ⟨hzbox, htriz⟩
      simp only [ιT, dif_pos hy, dif_pos hz] at hyz
      exact Subtype.ext_iff.mp (Prod.ext_iff.mp hyz).1
    · 
      intro v hv; obtain ⟨t, i⟩ := v
      rw [bc64_starForest_deg1_iff] at hv
      exact hlamB (t, i) hv
    · 
      intro u hu v hv huv
      rw [Finset.mem_coe, Finset.mem_filter] at hu hv
      obtain ⟨t1, i1⟩ := u; obtain ⟨t2, i2⟩ := v
      rw [bc64_starForest_deg1_iff] at hu hv
      exact hlamInj hu.2 hv.2 huv




theorem bc64_coarseTcount_le_boundary_of_boundaryInjection (ω : ConfigSpace (Sym2 (Site d)))
    (L R : ℕ) {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁) (hinj : bc64_CoarseBoundaryInjection ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc63_coarseTcount_le_boundary_of_armEmbedding ω L R
    (bc64_coarseArmEmbedding_of_boundaryInjection ω L R hz₀ hz₁ hzne hinj)











theorem bc64_disjointBoxes_multiTrif (L : ℕ) :
    Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) := by
  refine bc64_boxAround_disjoint_of_farCoord 0 ?_
  have hcoord : ((0 : Site 2) - bc57_pt (2 * (L : ℤ) + 1) 0) 0 = -(2 * (L : ℤ) + 1) := by
    simp only [Pi.sub_apply]; rw [bc57_pt_fst]; simp
  rw [hcoord, Int.natAbs_neg]
  have hval : (2 * (L : ℤ) + 1).natAbs = 2 * L + 1 := by
    have : (2 * (L : ℤ) + 1) = ((2 * L + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.natAbs_natCast]
  omega






theorem bc64_disjointBoxes_sublattice (L : ℕ) {m m' : ℤ} (hmm : m ≠ m') :
    Disjoint (bc61_boxAround 2 L (bc57_pt ((2 * (L : ℤ) + 1) * m) 0))
      (bc61_boxAround 2 L (bc57_pt ((2 * (L : ℤ) + 1) * m') 0)) := by
  refine bc64_boxAround_disjoint_of_farCoord 0 ?_
  have hcoord : (bc57_pt ((2 * (L : ℤ) + 1) * m) 0 - bc57_pt ((2 * (L : ℤ) + 1) * m') 0) 0
      = (2 * (L : ℤ) + 1) * (m - m') := by
    simp only [Pi.sub_apply]; rw [bc57_pt_fst, bc57_pt_fst]; ring
  rw [hcoord]
  have hne : m - m' ≠ 0 := sub_ne_zero.mpr hmm
  have h1 : 1 ≤ (m - m').natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hne)
  have hfactor : (2 * (L : ℤ) + 1).natAbs = 2 * L + 1 := by
    have hcast : (2 * (L : ℤ) + 1) = ((2 * L + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, Int.natAbs_natCast]
  have habs : ((2 * (L : ℤ) + 1) * (m - m')).natAbs = (2 * L + 1) * (m - m').natAbs := by
    rw [Int.natAbs_mul, hfactor]
  rw [habs]; nlinarith [h1]













theorem bc64_line1_connected_right (a : ℤ) (j : ℕ) :
    Connected 2 bc60_upperLines (bc57_pt a 1) (bc57_pt (a + (j : ℤ)) 1) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt a 1)
  | succ i ih =>
    have hstep : Connected 2 bc60_upperLines (bc57_pt (a + (i : ℤ)) 1) (bc57_pt (a + (i : ℤ) + 1) 1) :=
      IsOpenEdge.connected ⟨bc57_pt_adj (a + (i : ℤ)) 1, bc60_open (a + (i : ℤ)) (by norm_num)⟩
    have hcast : a + ((i + 1 : ℕ) : ℤ) = a + (i : ℤ) + 1 := by push_cast; ring
    rw [hcast]; exact ih.trans hstep




theorem bc64_line1_connected (a b : ℤ) :
    Connected 2 bc60_upperLines (bc57_pt a 1) (bc57_pt b 1) := by
  rcases le_total a b with hab | hab
  · have hj : b = a + ((b - a).toNat : ℤ) := by rw [Int.toNat_of_nonneg (by omega)]; ring
    rw [hj]; exact bc64_line1_connected_right a (b - a).toNat
  · have hj : a = b + ((a - b).toNat : ℤ) := by rw [Int.toNat_of_nonneg (by omega)]; ring
    rw [hj]; exact (bc64_line1_connected_right b (a - b).toNat).symm










theorem bc64_arms_can_share_boundary (L : ℕ) :
    Disjoint (bc61_boxAround 2 L (0 : Site 2))
        (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
      Connected 2 bc60_upperLines
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) :=
  ⟨bc64_disjointBoxes_multiTrif L,
   bc64_line1_connected ((L : ℤ) + 1) (2 * (L : ℤ) + 1 + ((L : ℤ) + 1))⟩




















theorem bc64_infiniteClusters_top_null_of_boundaryInjection_route
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ)
    (hbdvertices : ∀ R : ℕ, ∃ z₀ z₁ : Site d,
      z₀ ∈ vertexBoundary d R ∧ z₁ ∈ vertexBoundary d R ∧ z₀ ≠ z₁)
    (hbinj : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc64_CoarseBoundaryInjection ω L R)
    (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
  refine bc63_infiniteClusters_top_null_of_armEmbedding_route μ hd hinv hfe L (fun ω R => ?_)
    hcoarseRoute
  obtain ⟨z₀, z₁, hz₀, hz₁, hzne⟩ := hbdvertices R
  exact bc64_coarseArmEmbedding_of_boundaryInjection ω L R hz₀ hz₁ hzne (hbinj ω R)

























theorem bc64_status :
    
    (∀ {L : ℕ} {y y' : Site d}, (∃ i, 2 * L < ((y - y') i).natAbs) →
      Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y')) ∧
    
    (∀ (β : Type), (bc64_starForest β).IsAcyclic) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d),
      z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
      bc64_CoarseBoundaryInjection ω L R → bc63_CoarseArmEmbedding ω L R) ∧
    
    (∀ (L : ℕ),
      Disjoint (bc61_boxAround 2 L (0 : Site 2))
          (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
        Connected 2 bc60_upperLines
          (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) :=
  ⟨fun hfar => bc64_boxAround_disjoint_of_far hfar,
   fun β => bc64_starForest_acyclic β,
   fun ω L R z₀ z₁ hz₀ hz₁ hzne hinj =>
     bc64_coarseArmEmbedding_of_boundaryInjection ω L R hz₀ hz₁ hzne hinj,
   fun L => bc64_arms_can_share_boundary L⟩

end StatMech.Walls
