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
import Code.Percolation.DisjointArmEndsProve
import Code.Percolation.DisjointArmEndsProve2
import Code.Percolation.ArmReachComponentClose
import Code.Percolation.BKForestLib
import Code.Walls.bc26forest
import Code.Walls.bc37armadj
import Code.Walls.bc38acyclic
import Code.Walls.bc39spanning
import Code.Walls.bc40funnel
import Code.Walls.bc41rootside
import Code.Walls.bc42rootward
import Code.Walls.bc43rootparent
import Code.Walls.bc44rootwalk

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}









open Classical in



noncomputable def bc45_root (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    {x : Site d // x ∈ tfc_trifFinset ω n} → {x : Site d // x ∈ tfc_trifFinset ω n} :=
  fun v => ((bc37_armAdjGraph ω n).connectedComponentMk v).nonempty_supp.some




noncomputable def bc45_dep (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (v : Site d) : ℕ :=
  if hv : v ∈ tfc_trifFinset ω n then
    (bc37_armAdjGraph ω n).dist (bc45_root ω n ⟨v, hv⟩) ⟨v, hv⟩
  else 0

open Classical in

noncomputable def bc45_idx (_ω : ConfigSpace (Sym2 (Site d))) (_n : ℕ) : Site d → ℕ :=
  ((inferInstance : Countable (Site d)).exists_injective_nat).choose

theorem bc45_idx_injective (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    Function.Injective (bc45_idx ω n) :=
  ((inferInstance : Countable (Site d)).exists_injective_nat).choose_spec

open Classical in



noncomputable def bc45_armDepthRank (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Site d → ℕ ×ₗ ℕ :=
  fun v => toLex (bc45_dep ω n v, bc45_idx ω n v)

open Classical in


noncomputable def bc45_armForestPar (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Site d → Site d :=
  fun v => if hv : v ∈ tfc_trifFinset ω n then
    (bc38_parentTo (bc37_armAdjGraph ω n) (bc45_root ω n) ⟨v, hv⟩).1 else v




theorem bc45_root_reachable (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (v : {x : Site d // x ∈ tfc_trifFinset ω n}) :
    (bc37_armAdjGraph ω n).Reachable (bc45_root ω n v) v := by
  rw [bc45_root, ← SimpleGraph.ConnectedComponent.eq]
  exact ((bc37_armAdjGraph ω n).connectedComponentMk v).nonempty_supp.some_mem


theorem bc45_root_inv (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {v w : {x : Site d // x ∈ tfc_trifFinset ω n}} (h : (bc37_armAdjGraph ω n).Reachable v w) :
    bc45_root ω n v = bc45_root ω n w := by
  have : (bc37_armAdjGraph ω n).connectedComponentMk v
      = (bc37_armAdjGraph ω n).connectedComponentMk w :=
    SimpleGraph.ConnectedComponent.eq.mpr h
  simp only [bc45_root, this]


theorem bc45_dep_eq_zero_iff (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (v : Site d)
    (hv : v ∈ tfc_trifFinset ω n) :
    bc45_dep ω n v = 0 ↔ (⟨v, hv⟩ : {x : Site d // x ∈ tfc_trifFinset ω n}) = bc45_root ω n ⟨v, hv⟩ := by
  simp only [bc45_dep, dif_pos hv]
  rw [SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable]
  constructor
  · rintro (h | h)
    · exact h.symm
    · exact absurd (bc45_root_reachable ω n ⟨v, hv⟩) h
  · intro h; exact Or.inl h.symm






theorem bc45_par_spec (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) {v : Site d}
    (hv : v ∈ tfc_trifFinset ω n)
    (hnonroot : (⟨v, hv⟩ : {x : Site d // x ∈ tfc_trifFinset ω n}) ≠ bc45_root ω n ⟨v, hv⟩) :
    (bc45_armForestPar ω n v ∈ tfc_trifFinset ω n) ∧
      bc37_ArmAdjacent ω n v (bc45_armForestPar ω n v) ∧
      bc45_dep ω n (bc45_armForestPar ω n v) < bc45_dep ω n v := by
  classical
  set G := bc37_armAdjGraph ω n with hG
  obtain ⟨hadj, hdlt⟩ :=
    bc38_parentTo_spec G (bc45_root ω n) hnonroot (bc45_root_reachable ω n ⟨v, hv⟩)
  have hpar_val : bc45_armForestPar ω n v = (bc38_parentTo G (bc45_root ω n) ⟨v, hv⟩).1 := by
    simp only [bc45_armForestPar, dif_pos hv, ← hG]
  have hparT : bc45_armForestPar ω n v ∈ tfc_trifFinset ω n := by
    rw [hpar_val]; exact (bc38_parentTo G (bc45_root ω n) ⟨v, hv⟩).2
  have hpar_pack : (⟨bc45_armForestPar ω n v, hparT⟩ : {x : Site d // x ∈ tfc_trifFinset ω n})
      = bc38_parentTo G (bc45_root ω n) ⟨v, hv⟩ := Subtype.ext hpar_val
  refine ⟨hparT, ?_, ?_⟩
  · 
    have : G.Adj ⟨v, hv⟩ ⟨bc45_armForestPar ω n v, hparT⟩ := by rw [hpar_pack]; exact hadj
    exact this
  · 
    have hparreach : G.Reachable ⟨v, hv⟩ (bc38_parentTo G (bc45_root ω n) ⟨v, hv⟩) := hadj.reachable
    have hrootpar : bc45_root ω n (bc38_parentTo G (bc45_root ω n) ⟨v, hv⟩) = bc45_root ω n ⟨v, hv⟩ :=
      bc45_root_inv ω n hparreach.symm
    have hdeppar : bc45_dep ω n (bc45_armForestPar ω n v)
        = G.dist (bc45_root ω n ⟨v, hv⟩) (bc38_parentTo G (bc45_root ω n) ⟨v, hv⟩) := by
      simp only [bc45_dep, dif_pos hparT]
      rw [hpar_pack, hrootpar]
    have hdepv : bc45_dep ω n v = G.dist (bc45_root ω n ⟨v, hv⟩) ⟨v, hv⟩ := by
      simp only [bc45_dep, dif_pos hv, ← hG]
    rw [hdeppar, hdepv]; exact hdlt













theorem bc45_armEdge_transfer (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {a b y : Site d} (hadj : bc37_ArmAdjacent ω n a b)
    (hyT : y ∈ tfc_trifFinset ω n) (hya : y ≠ a) (hyb : y ≠ b) :
    Connected d (removeSite y ω) a b := by
  obtain ⟨_hne, _hconn, hcut⟩ := hadj
  
  have hymem : y ∈ ((tfc_trifFinset ω n).erase a).erase b :=
    Finset.mem_erase.mpr ⟨hyb, Finset.mem_erase.mpr ⟨hya, hyT⟩⟩
  have hle : bc37_cutExcept ω n a b ≤ removeSite y ω := by
    unfold bc37_cutExcept
    exact daep2_removeSites_le_removeSite _ ω hymem
  exact connected_mono hle hcut













theorem bc45_rootward_reach_root (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {y : Site d} (hyT : y ∈ tfc_trifFinset ω n) :
    ∀ (v : Site d) (hv : v ∈ tfc_trifFinset ω n), bc45_dep ω n v < bc45_dep ω n y →
      Connected d (removeSite y ω) v (bc45_root ω n ⟨v, hv⟩).1 := by
  intro v
  
  induction hdv : bc45_dep ω n v using Nat.strong_induction_on generalizing v with
  | _ k IH =>
    intro hv hlt
    
    have hvy : v ≠ y := by
      rintro rfl; exact absurd hdv (by omega)
    by_cases hroot : (⟨v, hv⟩ : {x : Site d // x ∈ tfc_trifFinset ω n}) = bc45_root ω n ⟨v, hv⟩
    · 
      rw [← hroot]
    · 
      obtain ⟨hparT, hpadj, hdppar⟩ := bc45_par_spec ω n hv hroot
      have hpar_lt_y : bc45_dep ω n (bc45_armForestPar ω n v) < bc45_dep ω n y := by
        rw [hdv] at hdppar; omega
      have hpary : bc45_armForestPar ω n v ≠ y := by
        rintro heq; rw [heq] at hpar_lt_y; exact absurd hpar_lt_y (by omega)
      
      have hstep : Connected d (removeSite y ω) v (bc45_armForestPar ω n v) :=
        bc45_armEdge_transfer ω n hpadj hyT hvy.symm hpary.symm
      
      have hpar_dep_lt_k : bc45_dep ω n (bc45_armForestPar ω n v) < k := by rw [← hdv]; exact hdppar
      have hrec :=
        IH (bc45_dep ω n (bc45_armForestPar ω n v)) hpar_dep_lt_k (bc45_armForestPar ω n v) rfl
          hparT hpar_lt_y
      
      have hreach : (bc37_armAdjGraph ω n).Reachable ⟨v, hv⟩ ⟨bc45_armForestPar ω n v, hparT⟩ := by
        have : (bc37_armAdjGraph ω n).Adj ⟨v, hv⟩ ⟨bc45_armForestPar ω n v, hparT⟩ := hpadj
        exact this.reachable
      have hrooteq : bc45_root ω n ⟨bc45_armForestPar ω n v, hparT⟩ = bc45_root ω n ⟨v, hv⟩ :=
        bc45_root_inv ω n hreach.symm
      rw [hrooteq] at hrec
      exact hstep.trans hrec











theorem bc45_armDepthRank_injective (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    ∀ a, a ∈ box d n → IsTrifurcation d ω a → ∀ b, b ∈ box d n → IsTrifurcation d ω b →
      a ≠ b → Connected d ω a b →
      bc45_armDepthRank ω n a ≠ bc45_armDepthRank ω n b := by
  intro a _habox _htria b _hbbox _htrib hab _hconn hrankeq
  have hidxeq : bc45_idx ω n a = bc45_idx ω n b := by
    simpa [bc45_armDepthRank] using congrArg (fun p => (ofLex p).2) hrankeq
  exact hab (bc45_idx_injective ω n hidxeq)











theorem bc45_rootWard_connected (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x y : Site d} (hxT : x ∈ tfc_trifFinset ω n) (hyT : y ∈ tfc_trifFinset ω n)
    (hxy : x ≠ y) (hconn : Connected d ω x y)
    (hlt : bc45_armDepthRank ω n x < bc45_armDepthRank ω n y)
    (hpadj : bc37_ArmAdjacent ω n y (bc45_armForestPar ω n y))
    (hparT : bc45_armForestPar ω n y ∈ tfc_trifFinset ω n)
    (_hprank : bc45_armDepthRank ω n (bc45_armForestPar ω n y) < bc45_armDepthRank ω n y) :
    Connected d (removeSite y ω) x (bc45_armForestPar ω n y) := by
  classical
  set p := bc45_armForestPar ω n y with hp
  
  have hdep_x_le : bc45_dep ω n x ≤ bc45_dep ω n y := by
    rw [bc45_armDepthRank, bc45_armDepthRank, Prod.Lex.toLex_lt_toLex] at hlt
    rcases hlt with h | ⟨h, _⟩ <;> omega
  
  
  have hyroot : (⟨y, hyT⟩ : {z : Site d // z ∈ tfc_trifFinset ω n}) ≠ bc45_root ω n ⟨y, hyT⟩ := by
    intro he
    have hdy0 : bc45_dep ω n y = 0 := (bc45_dep_eq_zero_iff ω n y hyT).mpr he
    rw [bc45_armDepthRank, bc45_armDepthRank, hdy0, Prod.Lex.toLex_lt_toLex] at hlt
    
    have hdx0 : bc45_dep ω n x = 0 := by rcases hlt with h | ⟨h, _⟩ <;> omega
    have hxroot : (⟨x, hxT⟩ : {z : Site d // z ∈ tfc_trifFinset ω n}) = bc45_root ω n ⟨x, hxT⟩ :=
      (bc45_dep_eq_zero_iff ω n x hxT).mp hdx0
    have hxy_reach : (bc37_armAdjGraph ω n).Reachable ⟨x, hxT⟩ ⟨y, hyT⟩ :=
      bc39_armAdjSpanning ω n ⟨x, hxT⟩ ⟨y, hyT⟩ hconn
    have hrooteq : bc45_root ω n ⟨x, hxT⟩ = bc45_root ω n ⟨y, hyT⟩ := bc45_root_inv ω n hxy_reach
    apply hxy
    have : (⟨x, hxT⟩ : {z : Site d // z ∈ tfc_trifFinset ω n}) = ⟨y, hyT⟩ := by
      rw [hxroot, hrooteq, ← he]
    exact congrArg Subtype.val this
  have hdep_p_lt : bc45_dep ω n p < bc45_dep ω n y := (bc45_par_spec ω n hyT hyroot).2.2
  
  have hp_reach : Connected d (removeSite y ω) p (bc45_root ω n ⟨p, hparT⟩).1 :=
    bc45_rootward_reach_root ω n hyT p hparT hdep_p_lt
  
  have hx_reach : Connected d (removeSite y ω) x (bc45_root ω n ⟨x, hxT⟩).1 := by
    rcases lt_or_eq_of_le hdep_x_le with hdlt | hdeq
    · exact bc45_rootward_reach_root ω n hyT x hxT hdlt
    · 
      have hx_pos : 0 < bc45_dep ω n x := by omega
      have hxroot : (⟨x, hxT⟩ : {z : Site d // z ∈ tfc_trifFinset ω n}) ≠ bc45_root ω n ⟨x, hxT⟩ := by
        intro he
        have : bc45_dep ω n x = 0 := (bc45_dep_eq_zero_iff ω n x hxT).mpr he
        omega
      obtain ⟨hpxT, hpxadj, hdppx⟩ := bc45_par_spec ω n hxT hxroot
      have hpx_lt_y : bc45_dep ω n (bc45_armForestPar ω n x) < bc45_dep ω n y := by omega
      have hxy' : y ≠ x := hxy.symm
      have hpxy : y ≠ bc45_armForestPar ω n x := by
        intro he; rw [← he] at hpx_lt_y; exact absurd hpx_lt_y (by omega)
      have hstep : Connected d (removeSite y ω) x (bc45_armForestPar ω n x) :=
        bc45_armEdge_transfer ω n hpxadj hyT hxy' hpxy
      have hrec : Connected d (removeSite y ω) (bc45_armForestPar ω n x)
          (bc45_root ω n ⟨bc45_armForestPar ω n x, hpxT⟩).1 :=
        bc45_rootward_reach_root ω n hyT (bc45_armForestPar ω n x) hpxT hpx_lt_y
      
      have hreach : (bc37_armAdjGraph ω n).Reachable ⟨x, hxT⟩ ⟨bc45_armForestPar ω n x, hpxT⟩ := by
        have : (bc37_armAdjGraph ω n).Adj ⟨x, hxT⟩ ⟨bc45_armForestPar ω n x, hpxT⟩ := hpxadj
        exact this.reachable
      have hrooteq : bc45_root ω n ⟨bc45_armForestPar ω n x, hpxT⟩ = bc45_root ω n ⟨x, hxT⟩ :=
        bc45_root_inv ω n hreach.symm
      rw [hrooteq] at hrec
      exact hstep.trans hrec
  
  have hxy_reach : (bc37_armAdjGraph ω n).Reachable ⟨x, hxT⟩ ⟨y, hyT⟩ :=
    bc39_armAdjSpanning ω n ⟨x, hxT⟩ ⟨y, hyT⟩ hconn
  have hyp_reach : (bc37_armAdjGraph ω n).Reachable ⟨y, hyT⟩ ⟨p, hparT⟩ := by
    have : (bc37_armAdjGraph ω n).Adj ⟨y, hyT⟩ ⟨p, hparT⟩ := hpadj
    exact this.reachable
  have hxp_reach : (bc37_armAdjGraph ω n).Reachable ⟨x, hxT⟩ ⟨p, hparT⟩ := hxy_reach.trans hyp_reach
  have hrooteq : bc45_root ω n ⟨x, hxT⟩ = bc45_root ω n ⟨p, hparT⟩ := bc45_root_inv ω n hxp_reach
  rw [hrooteq] at hx_reach
  exact hx_reach.trans hp_reach.symm












theorem bc45_rootWardRootParent_holds_at_depthRank (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc43_RootWardRootParent ω n (bc45_armDepthRank ω n) (bc45_armForestPar ω n) := by
  intro _hinj x hxbox htri y hybox htriy hxy hconn hlt hxpar hpbox hptri hpadj hprank
  have hxT : x ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
  have hyT : y ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
  have hparT : bc45_armForestPar ω n y ∈ tfc_trifFinset ω n :=
    tfc_mem_trifFinset.mpr ⟨hpbox, hptri⟩
  have hconn_cut : Connected d (removeSite y ω) x (bc45_armForestPar ω n y) :=
    bc45_rootWard_connected ω n hxT hyT hxy hconn hlt hpadj hparT hprank
  exact (bc42_avoidingWalk_iff_connected_removeSite ω hxy).mpr hconn_cut















theorem bc45_rooting_spec (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → bc45_armDepthRank ω n x < bc45_armDepthRank ω n y →
        bc45_armForestPar ω n y ∈ tfc_trifFinset ω n ∧
        bc37_ArmAdjacent ω n y (bc45_armForestPar ω n y) ∧
        bc45_armDepthRank ω n (bc45_armForestPar ω n y) < bc45_armDepthRank ω n y := by
  intro x hxbox htri y hybox htriy hxy hconn hlt
  have hxT : x ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
  have hyT : y ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
  
  have hyroot : (⟨y, hyT⟩ : {z : Site d // z ∈ tfc_trifFinset ω n}) ≠ bc45_root ω n ⟨y, hyT⟩ := by
    intro he
    have hdy0 : bc45_dep ω n y = 0 := (bc45_dep_eq_zero_iff ω n y hyT).mpr he
    rw [bc45_armDepthRank, bc45_armDepthRank, hdy0, Prod.Lex.toLex_lt_toLex] at hlt
    have hdx0 : bc45_dep ω n x = 0 := by rcases hlt with h | ⟨h, _⟩ <;> omega
    have hxroot : (⟨x, hxT⟩ : {z : Site d // z ∈ tfc_trifFinset ω n}) = bc45_root ω n ⟨x, hxT⟩ :=
      (bc45_dep_eq_zero_iff ω n x hxT).mp hdx0
    have hxy_reach : (bc37_armAdjGraph ω n).Reachable ⟨x, hxT⟩ ⟨y, hyT⟩ :=
      bc39_armAdjSpanning ω n ⟨x, hxT⟩ ⟨y, hyT⟩ hconn
    have hrooteq : bc45_root ω n ⟨x, hxT⟩ = bc45_root ω n ⟨y, hyT⟩ := bc45_root_inv ω n hxy_reach
    apply hxy
    have : (⟨x, hxT⟩ : {z : Site d // z ∈ tfc_trifFinset ω n}) = ⟨y, hyT⟩ := by
      rw [hxroot, hrooteq, ← he]
    exact congrArg Subtype.val this
  obtain ⟨hparT, hpadj, hdppar⟩ := bc45_par_spec ω n hyT hyroot
  exact ⟨hparT, hpadj, Prod.Lex.toLex_lt_toLex.mpr (Or.inl hdppar)⟩







theorem bc45_parentFunneling_of_cutGeometryFixed' (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc40_ArmCutGeometryFixed' ω n) : bc37_ParentFunneling ω n := by
  obtain ⟨b, hdata, hclauses⟩ := hgeo
  refine ⟨b, bc45_armDepthRank ω n, bc45_armForestPar ω n, hdata,
    bc45_armDepthRank_injective ω n, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hparT, hpadj, hprank⟩ :=
    bc45_rooting_spec ω n x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hpbox, hptri⟩ := tfc_mem_trifFinset.mp hparT
  obtain ⟨hloc, hself, hfun⟩ := hclauses y (bc45_armForestPar ω n y) hybox htriy hpadj
  refine ⟨hloc, hself, fun hxne => ?_⟩
  
  obtain ⟨p, hp⟩ :=
    bc45_rootWardRootParent_holds_at_depthRank ω n (bc45_armDepthRank_injective ω n)
      x hxbox htri y hybox htriy hxy hconn hlt hxne hpbox hptri hpadj hprank
  have hrs : Connected d (removeSite y ω) x (bc45_armForestPar ω n y) :=
    (bc42_avoidingWalk_iff_connected_removeSite ω hxy).mp ⟨p, hp⟩
  exact hfun x hxy hrs


theorem bc45_selfDownArm_of_cutGeometryFixed' (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc40_ArmCutGeometryFixed' ω n) : bc36_SelfDownArm ω n :=
  bc37_selfDownArm_of_parentFunneling ω n (bc45_parentFunneling_of_cutGeometryFixed' ω n hgeo)













theorem bc45_burton_keane_bernoulli (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc40_ArmCutGeometryFixed' ω n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc36_burton_keane_bernoulli_of_selfDownArm hd p hp1 hp0
    (fun ω n hn => bc45_selfDownArm_of_cutGeometryFixed' ω n (hgeo ω n hn)) htrif














theorem bc45_farSide_deeper_excluded (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) {y z : Site d}
    (hyT : y ∈ tfc_trifFinset ω n)
    (hyroot : (⟨y, hyT⟩ : {x : Site d // x ∈ tfc_trifFinset ω n}) ≠ bc45_root ω n ⟨y, hyT⟩)
    (hdeeper : bc45_dep ω n y < bc45_dep ω n z) :
    z ≠ bc45_armForestPar ω n y := by
  intro he
  have hshallower : bc45_dep ω n (bc45_armForestPar ω n y) < bc45_dep ω n y :=
    (bc45_par_spec ω n hyT hyroot).2.2
  rw [← he] at hshallower
  omega






theorem bc45_monotone_avoids_deeper (depY depV : ℕ) (hlt : depV < depY) :
    ∀ depW, depW ≤ depV → depW ≠ depY := by
  intro depW hle heq; omega











def bc45_chainDep (v : Fin 3) : ℕ := v.val


def bc45_chainPar (v : Fin 3) : Fin 3 := if v = 0 then 0 else v - 1






theorem bc45_chainShadow_confirms :
    (∀ v : Fin 3, v ≠ 0 → bc45_chainDep (bc45_chainPar v) < bc45_chainDep v) ∧
    (bc45_chainDep 1 < bc45_chainDep 2 ∧ bc45_chainPar 1 ≠ 2) ∧
    (∀ v : Fin 3, bc45_chainDep v < bc45_chainDep 1 → v ≠ 1) := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩ <;> decide



def bc45_yDep (v : Fin 4) : ℕ := if v = 0 then 0 else if v = 1 then 1 else 2


def bc45_yPar (v : Fin 4) : Fin 4 := if v = 0 then 0 else if v = 1 then 0 else 1







theorem bc45_yTreeShadow_confirms :
    (∀ v : Fin 4, v ≠ 0 → bc45_yDep (bc45_yPar v) < bc45_yDep v) ∧
    (bc45_yDep 1 < bc45_yDep 2 ∧ bc45_yPar 1 ≠ 2) ∧
    (bc45_yPar 2 = 1 ∧ bc45_yPar 3 = 1) ∧
    (∀ v : Fin 4, bc45_yDep v < bc45_yDep 2 → v ≠ 2) := by
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> decide

end StatMech.Walls
