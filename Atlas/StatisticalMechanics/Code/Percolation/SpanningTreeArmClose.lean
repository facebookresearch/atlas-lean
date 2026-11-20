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
import Code.Percolation.BurtonKeaneMerge
import Code.Percolation.TrifurcationCount
import Code.Percolation.BurtonKeaneClose2
import Code.Percolation.DisjointArmEndsClose
import Code.Percolation.DisjointArmEndsProve
import Code.Percolation.DisjointArmEndsProve2
import Code.Percolation.DisjointArmEndsFinal
import Code.Percolation.PrivateArmProve
import Code.Percolation.BKForestLib
import Code.Percolation.ForestSelectorProve

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}










theorem stac_removeSites_no_neighbor (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    {x w : Site d} (hxT : x ∈ T) : ¬ (openSubgraph d (removeSites T ω)).Adj x w := by
  intro hadj
  have : (removeSites T ω) s(x, w) = true := hadj.2
  rw [removeSites, if_pos ⟨x, hxT, Sym2.mem_mk_left x _⟩] at this
  exact Bool.false_ne_true this



theorem stac_removeSites_connected_eq (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    {x v : Site d} (hxT : x ∈ T) (hconn : Connected d (removeSites T ω) x v) : v = x := by
  rcases hconn with ⟨w⟩
  cases w with
  | nil => rfl
  | cons hadj p => exact absurd hadj (stac_removeSites_no_neighbor T ω hxT)



theorem stac_removeSites_cluster_singleton (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) {x : Site d} (hxT : x ∈ T) :
    cluster d (removeSites T ω) x = {x} := by
  ext v
  simp only [mem_cluster, Set.mem_singleton_iff]
  exact ⟨fun h => stac_removeSites_connected_eq T ω hxT h, fun h => h ▸ connected_rfl⟩




theorem stac_infiniteCluster_notMem (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    {w : Site d} (hinf : (cluster d (removeSites T ω) w).Infinite) : w ∉ T := by
  intro hwT
  rw [stac_removeSites_cluster_singleton T ω hwT] at hinf
  exact hinf (Set.finite_singleton w)












theorem stac_sameArm_of_sameClass (ω : ConfigSpace (Sym2 (Site d))) {x₀ aj u v : Site d}
    (hxu : Connected d ω x₀ u) (hneu : x₀ ≠ u)
    (hxv : Connected d ω x₀ v) (hnev : x₀ ≠ v)
    (hu : Connected d (removeSite x₀ ω) aj u)
    (hv : Connected d (removeSite x₀ ω) aj v) :
    fsp_sameArm ω x₀ u v := by
  unfold fsp_sameArm
  have hwu := fsp_armWitness_inArm ω hxu hneu
  have hwv := fsp_armWitness_inArm ω hxv hnev
  exact hwu.trans (hu.symm.trans (hv.trans hwv.symm))























theorem stac_claw_unsat
    (cx : Fin 3) (cy : Fin 3 → Fin 3)
    (ay : Fin 3 → Fin 3) (ayj : Fin 3 → Fin 3 → Fin 3)
    (Gay : ∀ i, ay i = 0 ↔ cy i ≠ i)
    (Gayj : ∀ i j, ayj i j = 0 ↔ cy j ≠ i)
    (Dx0 : ∀ i, cx ≠ cy i)
    (Dyiyj : ∀ i j, j ≠ i → ay i ≠ ayj i j) :
    False := by
  
  have step1 : ∀ i j : Fin 3, j ≠ i → cy i = i ∨ cy j = i := by
    intro i j hji
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hi, hj⟩ := hcon
    have h1 : ay i = 0 := (Gay i).mpr hi
    have h2 : ayj i j = 0 := (Gayj i j).mpr hj
    exact Dyiyj i j hji (by rw [h1, h2])
  
  have step2 : ∀ a : Fin 3, cy a = a := by
    intro a
    by_contra ha
    have hall : ∀ j : Fin 3, j ≠ a → cy j = a := by
      intro j hj
      rcases step1 a j hj with h | h
      · exact absurd h ha
      · exact h
    obtain ⟨b, c, hb, hc, hbc⟩ : ∃ b c : Fin 3, b ≠ a ∧ c ≠ a ∧ c ≠ b := by
      fin_cases a
      · exact ⟨1, 2, by decide, by decide, by decide⟩
      · exact ⟨0, 2, by decide, by decide, by decide⟩
      · exact ⟨0, 1, by decide, by decide, by decide⟩
    have hcyb : cy b = a := hall b hb
    have hcyc : cy c = a := hall c hc
    rcases step1 b c hbc with h | h
    · exact hb ((hcyb.symm.trans h).symm)
    · exact hb ((hcyc.symm.trans h).symm)
  
  exact Dx0 cx (by rw [step2 cx])









theorem stac_claw_shadow_consistent :
    ∃ (cy : Fin 3 → Fin 3) (ay : Fin 3 → Fin 3) (ayj : Fin 3 → Fin 3 → Fin 3),
      (∀ i, ay i = 0 ↔ cy i ≠ i) ∧ (∀ i j, ayj i j = 0 ↔ cy j ≠ i) := by
  classical
  refine ⟨id, fun _ => 1, fun i j => if j = i then 1 else 0, ?_, ?_⟩
  · intro i
    have hl : ¬ ((1 : Fin 3) = 0) := by decide
    have hr : ¬ (id i ≠ i) := fun h => h rfl
    exact ⟨fun h => absurd h hl, fun h => absurd h hr⟩
  · intro i j
    show (if j = i then (1 : Fin 3) else 0) = 0 ↔ id j ≠ i
    by_cases hji : j = i
    · have hl : ¬ ((1 : Fin 3) = 0) := by decide
      have hr : ¬ (id j ≠ i) := by rw [id_eq, hji]; exact fun h => h rfl
      rw [if_pos hji]
      exact ⟨fun h => absurd h hl, fun h => absurd h hr⟩
    · rw [if_neg hji]
      exact ⟨fun _ => fun h => hji h, fun _ => rfl⟩










open Classical in



noncomputable def stac_colorOf (ω : ConfigSpace (Sym2 (Site d))) (x₀ : Site d)
    (a : Fin 3 → Site d) (w : Site d) : Fin 3 :=
  if h : ∃ i, Connected d (removeSite x₀ ω) (a i) (fsp_armWitness ω x₀ w) then h.choose else 0







theorem stac_colorOf_faithful (ω : ConfigSpace (Sym2 (Site d))) (x₀ : Site d)
    (a : Fin 3 → Site d)
    (hsep : ∀ i j, i ≠ j → ¬ Connected d (removeSite x₀ ω) (a i) (a j))
    (hcover : ∀ w, Connected d ω x₀ w → x₀ ≠ w →
      ∃ i, Connected d (removeSite x₀ ω) (a i) (fsp_armWitness ω x₀ w))
    {u v : Site d} (hu : Connected d ω x₀ u) (hneu : x₀ ≠ u)
    (hv : Connected d ω x₀ v) (hnev : x₀ ≠ v) :
    stac_colorOf ω x₀ a u = stac_colorOf ω x₀ a v ↔ fsp_sameArm ω x₀ u v := by
  classical
  unfold stac_colorOf fsp_sameArm
  rw [dif_pos (hcover u hu hneu), dif_pos (hcover v hv hnev)]
  set i := (hcover u hu hneu).choose with hi
  set j := (hcover v hv hnev).choose with hj
  have hispec : Connected d (removeSite x₀ ω) (a i) (fsp_armWitness ω x₀ u) :=
    (hcover u hu hneu).choose_spec
  have hjspec : Connected d (removeSite x₀ ω) (a j) (fsp_armWitness ω x₀ v) :=
    (hcover v hv hnev).choose_spec
  constructor
  · intro hij
    rw [← hij] at hjspec
    exact hispec.symm.trans hjspec
  · intro hsame
    by_contra hijne
    exact hsep i j hijne (hispec.trans (hsame.trans hjspec.symm))






























def stac_ClawConfig (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (x₀ : Site d) (y : Fin 3 → Site d) (lx : Site d → Fin 3) (ly : Fin 3 → Site d → Fin 3),
    
    (x₀ ∈ box d n ∧ IsTrifurcation d ω x₀) ∧
    
    (∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧ Connected d ω x₀ (y i)) ∧
    Function.Injective y ∧
    
    (∀ u v, Connected d ω x₀ u → x₀ ≠ u → Connected d ω x₀ v → x₀ ≠ v →
      (lx u = lx v ↔ fsp_sameArm ω x₀ u v)) ∧
    
    (∀ i u v, Connected d ω (y i) u → y i ≠ u → Connected d ω (y i) v → y i ≠ v →
      (ly i u = ly i v ↔ fsp_sameArm ω (y i) u v)) ∧
    
    (∀ i, lx (y i) = i) ∧
    
    (∀ i w, Connected d ω x₀ w → x₀ ≠ w → Connected d ω (y i) w → y i ≠ w →
      (ly i w = 0 ↔ lx w ≠ i))












theorem stac_not_divergentArmOrder_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hclaw : stac_ClawConfig ω n) : ¬ fsp_DivergentArmOrder ω n := by
  classical
  obtain ⟨x₀, y, lx, ly, ⟨hx0box, htri0⟩, hydata, hyinj, hlxf, hlyf, hydown, hGstar⟩ := hclaw
  rintro ⟨b, hbdata, hdiv⟩
  set T := tfc_trifFinset ω n with hT
  
  have hx0T : x₀ ∈ T := tfc_mem_trifFinset.mpr ⟨hx0box, htri0⟩
  have hyT : ∀ i, y i ∈ T := fun i =>
    tfc_mem_trifFinset.mpr ⟨(hydata i).1, (hydata i).2.1⟩
  
  obtain ⟨_, hbx0ne, hbx0conn, hbx0inf⟩ := hbdata x₀ hx0box htri0
  
  have hbx0notin : b x₀ ∉ T := stac_infiniteCluster_notMem T ω hbx0inf
  have hbynotin : ∀ i, b (y i) ∉ T := fun i =>
    stac_infiniteCluster_notMem T ω (hbdata (y i) (hydata i).1 (hydata i).2.1).2.2.2
  
  have hne_bx0 : x₀ ≠ b x₀ := fun h => hbx0notin (h ▸ hx0T)
  have hne_x0_byi : ∀ i, x₀ ≠ b (y i) := fun i h => hbynotin i (h ▸ hx0T)
  have hne_yi_byj : ∀ i j, y i ≠ b (y j) := fun i j h => hbynotin j (h ▸ hyT i)
  
  have hx0byi : ∀ i, Connected d ω x₀ (b (y i)) := fun i =>
    (hydata i).2.2.2.trans (hbdata (y i) (hydata i).1 (hydata i).2.1).2.2.1
  have hyi_byi : ∀ i, Connected d ω (y i) (b (y i)) := fun i =>
    (hbdata (y i) (hydata i).1 (hydata i).2.1).2.2.1
  
  have hyi_byj : ∀ i j, Connected d ω (y i) (b (y j)) := fun i j =>
    ((hydata i).2.2.2.symm.trans (hx0byi j))
  
  set cx : Fin 3 := lx (b x₀) with hcx
  set cy : Fin 3 → Fin 3 := fun i => lx (b (y i)) with hcy
  set ayv : Fin 3 → Fin 3 := fun i => ly i (b (y i)) with hayv
  set ayjv : Fin 3 → Fin 3 → Fin 3 := fun i j => ly i (b (y j)) with hayjv
  
  have Gay : ∀ i, ayv i = 0 ↔ cy i ≠ i := fun i =>
    hGstar i (b (y i)) (hx0byi i) (hne_x0_byi i) (hyi_byi i) (hne_yi_byj i i)
  
  have Gayj : ∀ i j, ayjv i j = 0 ↔ cy j ≠ i := fun i j =>
    hGstar i (b (y j)) (hx0byi j) (hne_x0_byi j) (hyi_byj i j) (hne_yi_byj i j)
  
  have Dx0 : ∀ i, cx ≠ cy i := by
    intro i hcoll
    have hsame : fsp_sameArm ω x₀ (b x₀) (b (y i)) :=
      (hlxf (b x₀) (b (y i)) hbx0conn hne_bx0 (hx0byi i) (hne_x0_byi i)).mp hcoll
    exact hdiv x₀ hx0box htri0 (y i) (hydata i).1 (hydata i).2.1
      (hydata i).2.2.1 (hydata i).2.2.2 hsame
  
  have Dyiyj : ∀ i j, j ≠ i → ayv i ≠ ayjv i j := by
    intro i j hji hcoll
    have hyij : y i ≠ y j := fun h => hji (hyinj h).symm
    have hsame : fsp_sameArm ω (y i) (b (y i)) (b (y j)) :=
      (hlyf i (b (y i)) (b (y j)) (hyi_byi i) (hne_yi_byj i i)
        (hyi_byj i j) (hne_yi_byj i j)).mp hcoll
    exact hdiv (y i) (hydata i).1 (hydata i).2.1 (y j) (hydata j).1 (hydata j).2.1
      hyij ((hydata i).2.2.2.symm.trans (hydata j).2.2.2) hsame
  exact stac_claw_unsat cx cy ayv ayjv Gay Gayj Dx0 Dyiyj












theorem stac_claw_excludes_divergentArmOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hclaw : stac_ClawConfig ω n) (hdiv : fsp_DivergentArmOrder ω n) : False :=
  stac_not_divergentArmOrder_of_claw ω n hclaw hdiv







theorem stac_uniform_divergentArmOrder_false
    (hex : ∃ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n ∧ stac_ClawConfig ω n) :
    ¬ (∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fsp_DivergentArmOrder ω n) := by
  obtain ⟨ω, n, hn, hclaw⟩ := hex
  intro huniform
  exact stac_not_divergentArmOrder_of_claw ω n hclaw (huniform ω n hn)

end Percolation

end StatMech
