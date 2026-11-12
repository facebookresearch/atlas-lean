/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































































import Mathlib
import Code.Walls.bc71spanningtree
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







def bc72_quotGraph {V B : Type*} (G : SimpleGraph V) (f : V → B) : SimpleGraph B where
  Adj u v := u ≠ v ∧ ∃ a b, f a = u ∧ f b = v ∧ G.Adj a b
  symm := by rintro u v ⟨hne, a, b, ha, hb, hab⟩; exact ⟨hne.symm, b, a, hb, ha, hab.symm⟩
  loopless := ⟨by rintro u ⟨h, _⟩; exact h rfl⟩

@[simp] theorem bc72_quotGraph_adj {V B : Type*} (G : SimpleGraph V) (f : V → B) (u v : B) :
    (bc72_quotGraph G f).Adj u v ↔ u ≠ v ∧ ∃ a b, f a = u ∧ f b = v ∧ G.Adj a b := Iff.rfl






noncomputable def bc72_collapseBox (L : ℕ) (y : Site d) : Site d → Site d :=
  fun x => if x ∈ bc61_boxAround d L y then y else x

theorem bc72_collapseBox_outside {L : ℕ} {y x : Site d} (hx : x ∉ bc61_boxAround d L y) :
    bc72_collapseBox L y x = x := by unfold bc72_collapseBox; rw [if_neg hx]

theorem bc72_collapseBox_inside {L : ℕ} {y x : Site d} (hx : x ∈ bc61_boxAround d L y) :
    bc72_collapseBox L y x = y := by unfold bc72_collapseBox; rw [if_pos hx]


theorem bc72_collapseBox_center (L : ℕ) (y : Site d) : bc72_collapseBox L y y = y :=
  bc72_collapseBox_inside (by rw [bc61_mem_boxAround]; simp)

theorem bc72_y_mem_box (L : ℕ) (y : Site d) : y ∈ bc61_boxAround d L y := by
  rw [bc61_mem_boxAround]; simp



theorem bc72_collapse_ne_center {L : ℕ} {y p : Site d} (h : bc72_collapseBox L y p ≠ y) :
    p ∉ bc61_boxAround d L y ∧ bc72_collapseBox L y p = p := by
  by_cases hp : p ∈ bc61_boxAround d L y
  · exact absurd (bc72_collapseBox_inside hp) h
  · exact ⟨hp, bc72_collapseBox_outside hp⟩




theorem bc72_notMem_of_removeSites_open {T : Finset (Site d)} {ω : ConfigSpace (Sym2 (Site d))}
    {a b : Site d} (h : removeSites T ω s(a, b) = true) : a ∉ T ∧ b ∉ T := by
  unfold removeSites at h
  by_cases hc : ∃ t ∈ T, t ∈ (s(a, b) : Sym2 (Site d))
  · rw [if_pos hc] at h; exact absurd h (by simp)
  · refine ⟨fun ha => hc ⟨a, ha, by simp⟩, fun hb => hc ⟨b, hb, by simp⟩⟩


theorem bc72_notMem_box_of_cut_adj {L : ℕ} {y a b : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (hadj : (openSubgraph d (removeSites (bc61_boxAround d L y) ω)).Adj a b) :
    a ∉ bc61_boxAround d L y ∧ b ∉ bc61_boxAround d L y :=
  bc72_notMem_of_removeSites_open hadj.2


















theorem bc72_quot_edge_to_removeSites {L : ℕ} {y u v : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (hadj : (bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).Adj u v)
    (huy : u ≠ y) (hvy : v ≠ y) :
    (openSubgraph d (removeSites (bc61_boxAround d L y) ω)).Adj u v := by
  obtain ⟨hne, p, q, hp, hq, hpq⟩ := hadj
  obtain ⟨hpbox, hpself⟩ := bc72_collapse_ne_center (by rw [hp]; exact huy)
  obtain ⟨hqbox, hqself⟩ := bc72_collapse_ne_center (by rw [hq]; exact hvy)
  have hpu' : p = u := by rw [← hp, hpself]
  have hqv' : q = v := by rw [← hq, hqself]
  subst hpu' hqv'
  obtain ⟨hlat, hopen⟩ := hpq
  exact ⟨hlat, by rw [bc61_removeBox_apply_of_notMem hpbox hqbox]; exact hopen⟩




theorem bc72_quot_reachable_of_reachable {L : ℕ} {y a b : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (h : Connected d ω a b) :
    (bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).Reachable
      (bc72_collapseBox L y a) (bc72_collapseBox L y b) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact Reachable.refl _
  | cons hadj p ih =>
    rename_i u v _
    by_cases hfe : bc72_collapseBox L y u = bc72_collapseBox L y v
    · rw [hfe]; exact ih
    · have hq : (bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).Adj
          (bc72_collapseBox L y u) (bc72_collapseBox L y v) := ⟨hfe, u, v, rfl, rfl, hadj⟩
      exact hq.reachable.trans ih





theorem bc72_removeSites_reachable_of_quot_avoid {L : ℕ} {y u v : Site d}
    {ω : ConfigSpace (Sym2 (Site d))}
    (w : (bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).Walk u v)
    (hw : y ∉ w.support) :
    Connected d (removeSites (bc61_boxAround d L y) ω) u v := by
  induction w with
  | nil => exact Reachable.refl _
  | @cons a b c hab w ih =>
    rw [Walk.support_cons, List.mem_cons, not_or] at hw
    obtain ⟨hay, hw'⟩ := hw
    have hby : y ≠ b := fun h => by subst h; exact hw' (w.start_mem_support)
    exact (Adj.reachable
      (bc72_quot_edge_to_removeSites hab (Ne.symm hay) (Ne.symm hby))).trans (ih hw')





theorem bc72_removeSites_of_quotInduce {L : ℕ} {y a₁ a₂ : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (ha₁ : a₁ ≠ y) (ha₂ : a₂ ≠ y)
    (h : ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce
      ({y}ᶜ : Set (Site d))).Reachable ⟨a₁, by simpa using ha₁⟩ ⟨a₂, by simpa using ha₂⟩) :
    Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ := by
  obtain ⟨w⟩ := h
  set Q := bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y) with hQ
  set f : (Q.induce ({y}ᶜ : Set (Site d))) →g Q :=
    { toFun := fun u => u.1, map_rel' := fun {u v} huv => huv } with hf
  set w' := w.map f with hw'
  have hsupp : y ∉ w'.support := by
    intro hx
    rw [hw', Walk.support_map, List.mem_map] at hx
    obtain ⟨⟨c, hc⟩, _, hcx⟩ := hx
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hc
    exact hc (by simpa [hf] using hcx)
  exact bc72_removeSites_reachable_of_quot_avoid w' hsupp















theorem bc72_arm_adjacent_to_superVertex {L : ℕ} {y a : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (hinc : bc67_GnIncident ω L y a) (hne : a ∉ bc61_boxAround d L y) :
    (bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).Adj y a := by
  obtain ⟨b, hbbox, hadj⟩ := hinc
  have hay : a ≠ y := fun h => hne (h ▸ bc72_y_mem_box L y)
  exact ⟨hay.symm, b, a, bc72_collapseBox_inside hbbox, bc72_collapseBox_outside hne, hadj⟩






theorem bc72_arms_nonAdjacent {L : ℕ} {y a₁ a₂ : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (ha₁ : a₁ ≠ y) (ha₂ : a₂ ≠ y)
    (hcut : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂) :
    ¬ (bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).Adj a₁ a₂ := fun hadj =>
  hcut ((bc72_quot_edge_to_removeSites hadj ha₁ ha₂).reachable)





theorem bc72_arm_outside_of_infinite {L : ℕ} {x a : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (hinf : (cluster d (removeSites (bc61_boxAround d L x) ω) a).Infinite) :
    a ∉ bc61_boxAround d L x := by
  intro habox
  apply hinf
  apply Set.Finite.subset (Set.finite_singleton a)
  intro z hz
  rw [mem_cluster] at hz
  obtain ⟨w⟩ := hz
  cases w with
  | nil => simp
  | @cons a' b c hab w =>
    exact absurd habox (bc72_notMem_of_removeSites_open hab.2).1















theorem bc72_rs_of_doubleInduce {L : ℕ} {y : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    {S : Set (Site d)} (hyS : y ∈ S)
    {a₁ a₂ : (↑S : Type)} (h1 : a₁ ≠ ⟨y, hyS⟩) (h2 : a₂ ≠ ⟨y, hyS⟩)
    (h : (((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).induce
        ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
      ⟨a₁, by simpa using h1⟩ ⟨a₂, by simpa using h2⟩) :
    Connected d (removeSites (bc61_boxAround d L y) ω) (a₁ : Site d) (a₂ : Site d) := by
  obtain ⟨w⟩ := h
  set Q := bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y) with hQ
  set g : (((Q.induce S).induce ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type)))) →g Q :=
    { toFun := fun u => (u.1.1 : Site d), map_rel' := fun {u v} huv => huv } with hg
  set w' := w.map g with hw'
  have hsupp : y ∉ w'.support := by
    intro hx
    rw [hw', Walk.support_map, List.mem_map] at hx
    obtain ⟨⟨⟨c, hcS⟩, hc⟩, _, hcx⟩ := hx
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hc
    exact hc (Subtype.ext (by simpa [hg] using hcx))
  exact bc72_removeSites_reachable_of_quot_avoid w' hsupp

open Classical in









theorem bc72_quot_deg3_of_gnTrif {L : ℕ} {y : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (h : bc67_IsGnTrifurcation ω L y) :
    ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (hyS : y ∈ S)
      (_ : DecidableRel ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).Adj),
      3 ≤ ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).degree ⟨y, hyS⟩ := by
  classical
  obtain ⟨a₁, a₂, a₃, ⟨hi1, hi2, hi3⟩, ⟨hf1, hf2, hf3⟩, hc12, hc13, hc23⟩ := h
  set Q := bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y) with hQ
  have ho1 := bc72_arm_outside_of_infinite hf1
  have ho2 := bc72_arm_outside_of_infinite hf2
  have ho3 := bc72_arm_outside_of_infinite hf3
  have hy1 : a₁ ≠ y := fun hh => ho1 (hh ▸ bc72_y_mem_box L y)
  have hy2 : a₂ ≠ y := fun hh => ho2 (hh ▸ bc72_y_mem_box L y)
  have hy3 : a₃ ≠ y := fun hh => ho3 (hh ▸ bc72_y_mem_box L y)
  set S : Set (Site d) := {y, a₁, a₂, a₃} with hSdef
  have hyS : y ∈ S := by simp [hSdef]
  have hm1 : a₁ ∈ S := by simp [hSdef]
  have hm2 : a₂ ∈ S := by simp [hSdef]
  have hm3 : a₃ ∈ S := by simp [hSdef]
  haveI hSfin : Fintype (↑S : Type) := by rw [hSdef]; exact Set.Finite.fintype (by simp)
  set G := Q.induce S with hGdef
  haveI hGdec : DecidableRel G.Adj := Classical.decRel _
  have hGadj1 : G.Adj ⟨y, hyS⟩ ⟨a₁, hm1⟩ := bc72_arm_adjacent_to_superVertex hi1 ho1
  have hGadj2 : G.Adj ⟨y, hyS⟩ ⟨a₂, hm2⟩ := bc72_arm_adjacent_to_superVertex hi2 ho2
  have hGadj3 : G.Adj ⟨y, hyS⟩ ⟨a₃, hm3⟩ := bc72_arm_adjacent_to_superVertex hi3 ho3
  refine ⟨S, hSfin, hyS, hGdec, ?_⟩
  refine slh_deg_ge_three_of_cut (x := ⟨y, hyS⟩) (a₁ := ⟨a₁, hm1⟩) (a₂ := ⟨a₂, hm2⟩)
    (a₃ := ⟨a₃, hm3⟩) hGadj1.reachable hGadj2.reachable hGadj3.reachable
    (fun hh => hy1 (congrArg Subtype.val hh).symm)
    (fun hh => hy2 (congrArg Subtype.val hh).symm)
    (fun hh => hy3 (congrArg Subtype.val hh).symm) ?_ ?_ ?_
  · intro hr
    exact hc12 (bc72_rs_of_doubleInduce hyS (a₁ := ⟨a₁, hm1⟩) (a₂ := ⟨a₂, hm2⟩)
      (fun hh => hy1 (congrArg Subtype.val hh)) (fun hh => hy2 (congrArg Subtype.val hh)) hr)
  · intro hr
    exact hc13 (bc72_rs_of_doubleInduce hyS (a₁ := ⟨a₁, hm1⟩) (a₂ := ⟨a₃, hm3⟩)
      (fun hh => hy1 (congrArg Subtype.val hh)) (fun hh => hy3 (congrArg Subtype.val hh)) hr)
  · intro hr
    exact hc23 (bc72_rs_of_doubleInduce hyS (a₁ := ⟨a₂, hm2⟩) (a₂ := ⟨a₃, hm3⟩)
      (fun hh => hy2 (congrArg Subtype.val hh)) (fun hh => hy3 (congrArg Subtype.val hh)) hr)











open Classical in








theorem bc72_GnForestNeighbours_of_singleHub (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {x : Site d} (a : Fin 3 → Site d)
    (hxbox : x ∈ box d R)
    (hsingle : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x)
    (habdry : ∀ i, a i ∈ vertexBoundary d R)
    (hincid : ∀ i, bc67_GnIncident ω L x (a i))
    (haoutside : ∀ i, a i ∉ bc61_boxAround d L x)
    (hcut : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (a i) (a j))
    (hxne : ∀ i, a i ≠ x)
    (hainj : Function.Injective a) :
    bc71_GnForestNeighbours ω L R := by
  classical
  set lab : Fin 4 → Site d := fun v => match v with
    | 0 => x | 1 => a 0 | 2 => a 1 | 3 => a 2 with hlab
  have hlabinj : Function.Injective lab := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp only [hlab] at huv <;>
      first
        | rfl
        | (exact absurd huv (hxne 0).symm) | (exact absurd huv (hxne 1).symm)
        | (exact absurd huv (hxne 2).symm) | (exact absurd huv.symm (hxne 0).symm)
        | (exact absurd huv.symm (hxne 1).symm) | (exact absurd huv.symm (hxne 2).symm)
        | (exact absurd (hainj huv) (by decide))
  set S : Set (Site d) := Set.range lab with hSdef
  have hmem : ∀ i : Fin 4, lab i ∈ S := fun i => ⟨i, rfl⟩
  haveI hSfin : Fintype (↑S : Type) := by rw [hSdef]; exact Set.fintypeRange lab
  set e : Fin 4 ≃ (↑S : Type) :=
    Equiv.ofBijective (fun i => (⟨lab i, hmem i⟩ : (↑S : Type)))
      ⟨fun u v huv => hlabinj (Subtype.ext_iff.mp huv),
        fun ⟨y, hy⟩ => by obtain ⟨i, rfl⟩ := hy; exact ⟨i, rfl⟩⟩ with he
  have heval : ∀ i, (e i : Site d) = lab i := fun i => rfl
  have hsurj : ∀ w : (↑S : Type), ∃ i : Fin 4, e i = w := fun w => e.surjective w
  let G : SimpleGraph (↑S : Type) := bc70_star4.map e.toEmbedding
  let hisoG : bc70_star4 ≃g G := SimpleGraph.Iso.map e bc70_star4
  have hisoApp : ∀ i : Fin 4, hisoG i = e i := fun i => SimpleGraph.Iso.map_apply e bc70_star4 i
  have hGadj : ∀ u v : Fin 4, G.Adj (e u) (e v) ↔ bc70_star4.Adj u v := by
    intro u v; have := hisoG.map_adj_iff (v := u) (w := v); simpa [hisoApp] using this
  have hGac : G.IsAcyclic := (hisoG.symm.isAcyclic_iff).mpr bc70_star4_acyclic
  haveI hGdec : DecidableRel G.Adj := Classical.decRel _
  have hdeg : ∀ i : Fin 4, G.degree (e i) = bc70_star4.degree i := by
    intro i
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    have hnbhd : G.neighborFinset (e i) = (bc70_star4.neighborFinset i).image e := by
      ext w
      rw [SimpleGraph.mem_neighborFinset, Finset.mem_image]
      constructor
      · intro hw; obtain ⟨j, rfl⟩ := e.surjective w
        exact ⟨j, by rw [SimpleGraph.mem_neighborFinset]; exact (hGadj i j).mp hw, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        rw [SimpleGraph.mem_neighborFinset] at hj; exact (hGadj i j).mpr hj
    rw [hnbhd, Finset.card_image_of_injective _ e.injective]
  refine ⟨S, hSfin, ⟨e 0⟩, G, hGdec, (fun _ => e 0), hGac, ?_, ?_, ?_, ?_⟩
  · intro v; obtain ⟨i, rfl⟩ := hsurj v; rw [hdeg]; exact bc70_star4_deg_pos i
  · 
    intro y hybox htri
    have hyx : y = x := hsingle y hybox htri
    subst hyx
    refine ⟨e 1, e 2, e 3, (hGadj 0 1).mpr (by decide), (hGadj 0 2).mpr (by decide),
      (hGadj 0 3).mpr (by decide), ?_, ?_, ?_⟩
    · rw [heval, heval]; exact hcut 0 1 (by decide)
    · rw [heval, heval]; exact hcut 0 2 (by decide)
    · rw [heval, heval]; exact hcut 1 2 (by decide)
  · intro y hybox htri z hzbox htriz _
    rw [hsingle y hybox htri, hsingle z hzbox htriz]
  · intro v hv
    obtain ⟨i, rfl⟩ := hsurj v
    rw [hdeg] at hv
    rw [heval]
    fin_cases i
    · exact absurd hv (by decide)
    · simp only [hlab]; exact habdry 0
    · simp only [hlab]; exact habdry 1
    · simp only [hlab]; exact habdry 2




theorem bc72_count_of_singleHub (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {x : Site d} (a : Fin 3 → Site d)
    (hxbox : x ∈ box d R)
    (hsingle : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x)
    (habdry : ∀ i, a i ∈ vertexBoundary d R)
    (hincid : ∀ i, bc67_GnIncident ω L x (a i))
    (haoutside : ∀ i, a i ∉ bc61_boxAround d L x)
    (hcut : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (a i) (a j))
    (hxne : ∀ i, a i ≠ x)
    (hainj : Function.Injective a) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc71_count_of_forestNeighbours ω L R
    (bc72_GnForestNeighbours_of_singleHub ω L R a hxbox hsingle habdry hincid haoutside hcut hxne hainj)














theorem bc72_upperLines_arm_adjacent {L : ℕ} (hL : 3 ≤ L) :
    ∃ a : Site 2, (bc72_quotGraph (openSubgraph 2 bc60_upperLines)
        (bc72_collapseBox L (0 : Site 2))).Adj 0 a := by
  obtain ⟨a₁, a₂, a₃, ⟨hi1, _, _⟩, ⟨hf1, _, _⟩, _⟩ := bc67_upperLines_is_G_n_trifurcation hL
  exact ⟨a₁, bc72_arm_adjacent_to_superVertex hi1 (bc72_arm_outside_of_infinite hf1)⟩





theorem bc72_upperLines_deg3 {L : ℕ} (hL : 3 ≤ L) :
    ∃ (S : Set (Site 2)) (_ : Fintype (↑S : Type)) (hyS : (0 : Site 2) ∈ S)
      (_ : DecidableRel ((bc72_quotGraph (openSubgraph 2 bc60_upperLines)
              (bc72_collapseBox L (0 : Site 2))).induce S).Adj),
      3 ≤ ((bc72_quotGraph (openSubgraph 2 bc60_upperLines)
            (bc72_collapseBox L (0 : Site 2))).induce S).degree ⟨0, hyS⟩ :=
  bc72_quot_deg3_of_gnTrif (bc67_upperLines_is_G_n_trifurcation hL)


















def bc72_MultiBoxForestOnQuot (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  bc71_GnForestNeighbours ω L R




theorem bc72_forestNeighbours_of_multiBox (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc72_MultiBoxForestOnQuot ω L R) : bc71_GnForestNeighbours ω L R := h



theorem bc72_count_of_multiBox (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc72_MultiBoxForestOnQuot ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc71_count_of_forestNeighbours ω L R h

















theorem bc72_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a : Site d),
      bc67_GnIncident ω L y a → a ∉ bc61_boxAround d L y →
      (bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).Adj y a) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d), bc67_IsGnTrifurcation ω L y →
      ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (hyS : y ∈ S)
        (_ : DecidableRel ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).Adj),
        3 ≤ ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).degree ⟨y, hyS⟩) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc72_MultiBoxForestOnQuot ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω L y a hinc hne; exact bc72_arm_adjacent_to_superVertex hinc hne
  · intro ω L y htri; exact bc72_quot_deg3_of_gnTrif htri
  · intro ω L R h; exact bc72_count_of_multiBox ω L R h

end StatMech.Walls
