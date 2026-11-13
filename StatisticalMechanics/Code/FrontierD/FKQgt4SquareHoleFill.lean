/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Lattice.PeierlsHoleFreeBoundary
import Code.Lattice.JordanContour

open Set SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section


noncomputable def squareHoleFillRadius (S : Set (Site 2)) (hS : S.Finite) : Nat :=
  (finite_subset_box S hS).choose

theorem squareHoleFillRadius_spec (S : Set (Site 2)) (hS : S.Finite) :
    S ⊆ box 2 (squareHoleFillRadius S hS) :=
  (finite_subset_box S hS).choose_spec



def squareOuterComponent (S : Set (Site 2)) (hS : S.Finite) : Set (Site 2) :=
  {x | (latticeMinusBarrier S).Reachable
    (beacon 2 (squareHoleFillRadius S hS)) x}


def squareHoleFill (S : Set (Site 2)) (hS : S.Finite) : Set (Site 2) :=
  (squareOuterComponent S hS)ᶜ

theorem squareHoleFill_beacon_not_mem (S : Set (Site 2)) (hS : S.Finite) :
    beacon 2 (squareHoleFillRadius S hS) ∉ S := by
  have hbe : beacon 2 (squareHoleFillRadius S hS) ∈
      exterior 2 (squareHoleFillRadius S hS) :=
    beacon_mem_exterior _ (by norm_num)
  exact (exterior_subset_compl S _ (squareHoleFillRadius_spec S hS) hbe)


theorem subset_squareHoleFill (S : Set (Site 2)) (hS : S.Finite) :
    S ⊆ squareHoleFill S hS := by
  intro x hxS hxout
  obtain ⟨w⟩ := (show (latticeMinusBarrier S).Reachable
    (beacon 2 (squareHoleFillRadius S hS)) x from hxout)
  have hside := latticeMinusBarrier_sameSide S w
  exact (squareHoleFill_beacon_not_mem S hS) (hside.mpr hxS)


theorem squareHoleFill_subset_box (S : Set (Site 2)) (hS : S.Finite) :
    squareHoleFill S hS ⊆ box 2 (squareHoleFillRadius S hS) := by
  intro x hxfill
  by_contra hxbox
  have hxext : x ∈ exterior 2 (squareHoleFillRadius S hS) := by
    rw [exterior_eq_compl_box]
    exact hxbox
  have hbe : beacon 2 (squareHoleFillRadius S hS) ∈
      exterior 2 (squareHoleFillRadius S hS) :=
    beacon_mem_exterior _ (by norm_num)
  exact hxfill (exterior_reachable_in_barrier S _
    (squareHoleFillRadius_spec S hS) hbe hxext)

theorem squareHoleFill_finite (S : Set (Site 2)) (hS : S.Finite) :
    (squareHoleFill S hS).Finite :=
  (box_finite 2 (squareHoleFillRadius S hS)).subset
    (squareHoleFill_subset_box S hS)

private theorem latticeWalk_reachable_barrier_of_support_subset
    (A : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y)
    (hw : ∀ z ∈ w.support, z ∈ A) :
    (latticeMinusBarrier A).Reachable x y := by
  induction w with
  | nil => exact Reachable.refl _
  | @cons a b c hab w ih =>
      have ha : a ∈ A := hw a (by simp)
      have hb : b ∈ A := hw b (by simp)
      exact (latticeMinusBarrier_adj_of_both_mem A hab ha hb).reachable.trans
        (ih (fun z hz => hw z (by simp [hz])))

private theorem latticeWalk_reachable_barrier_of_support_disjoint
    (A : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y)
    (hw : ∀ z ∈ w.support, z ∉ A) :
    (latticeMinusBarrier A).Reachable x y := by
  induction w with
  | nil => exact Reachable.refl _
  | @cons a b c hab w ih =>
      have ha : a ∉ A := hw a (by simp)
      have hb : b ∉ A := hw b (by simp)
      exact (latticeMinusBarrier_adj_of_both_not_mem A hab ha hb).reachable.trans
        (ih (fun z hz => hw z (by simp [hz])))



theorem squareHoleFill_reaches_original
    (S : Set (Site 2)) (hS : S.Finite) (hne : S.Nonempty)
    {x : Site 2} (hx : x ∈ squareHoleFill S hS) :
    ∃ s ∈ S, (latticeMinusBarrier (squareHoleFill S hS)).Reachable x s := by
  classical
  by_cases hxS : x ∈ S
  · exact ⟨x, hxS, Reachable.refl x⟩
  · let b := beacon 2 (squareHoleFillRadius S hS)
    obtain ⟨w0⟩ := pbs_reach_all x b
    let w : (hypercubicLattice 2).Path x b := w0.toPath
    have hhit : {z ∈ hS.toFinset | z ∈ (w :
        (hypercubicLattice 2).Walk x b).support}.Nonempty := by
      by_contra hnone
      simp only [Finset.not_nonempty_iff_eq_empty] at hnone
      have havoid : ∀ z ∈ (w : (hypercubicLattice 2).Walk x b).support,
          z ∉ S := by
        intro z hz hzS
        have hzfin : z ∈ hS.toFinset := hS.mem_toFinset.mpr hzS
        have : z ∈ {z ∈ hS.toFinset |
            z ∈ (w : (hypercubicLattice 2).Walk x b).support} := by
          simp [hzfin, hz]
        simpa [hnone] using this
      have hxb : (latticeMinusBarrier S).Reachable x b :=
        latticeWalk_reachable_barrier_of_support_disjoint S w havoid
      exact hx hxb.symm
    obtain ⟨s, hsfin, hsupp, hfirst⟩ :=
      Walk.exists_mem_support_forall_mem_support_imp_eq
        (p := (w : (hypercubicLattice 2).Walk x b)) hS.toFinset hhit
    have hsS : s ∈ S := hS.mem_toFinset.mp hsfin
    let p : (hypercubicLattice 2).Walk x s :=
      (w : (hypercubicLattice 2).Walk x b).takeUntil s hsupp
    have hpPath : p.IsPath := by
      exact w.isPath.takeUntil hsupp
    have hpfill : ∀ z ∈ p.support, z ∈ squareHoleFill S hS := by
      intro z hz
      by_cases hzS : z ∈ S
      · exact subset_squareHoleFill S hS hzS
      · intro hzout
        have hzs : z ≠ s := fun h => hzS (h ▸ hsS)
        have hsnot : s ∉ (p.takeUntil z hz).support :=
          Walk.endpoint_notMem_support_takeUntil hpPath hz hzs.symm
        have hsubavoid : ∀ u ∈ (p.takeUntil z hz).support, u ∉ S := by
          intro u hu huS
          have huFin : u ∈ hS.toFinset := hS.mem_toFinset.mpr huS
          have huP : u ∈ p.support :=
            p.support_takeUntil_subset_support hz hu
          have hus : u = s := hfirst u huFin huP
          exact hsnot (hus ▸ hu)
        have hxz : (latticeMinusBarrier S).Reachable x z :=
          latticeWalk_reachable_barrier_of_support_disjoint S
            (p.takeUntil z hz) hsubavoid
        exact hx (hzout.trans hxz.symm)
    exact ⟨s, hsS,
      latticeWalk_reachable_barrier_of_support_subset
        (squareHoleFill S hS) p hpfill⟩



theorem squareHoleFill_inside_connected
    (S : Set (Site 2)) (hS : S.Finite) (hne : S.Nonempty)
    (hconn : ∀ a b : S,
      ((hypercubicLattice 2).induce S).Reachable a b) :
    ∀ a b : Site 2, a ∈ squareHoleFill S hS → b ∈ squareHoleFill S hS →
      (latticeMinusBarrier (squareHoleFill S hS)).Reachable a b := by
  intro a b ha hb
  obtain ⟨sa, hsa, hasa⟩ := squareHoleFill_reaches_original S hS hne ha
  obtain ⟨sb, hsb, hbsb⟩ := squareHoleFill_reaches_original S hS hne hb
  obtain ⟨w⟩ := hconn ⟨sa, hsa⟩ ⟨sb, hsb⟩
  let incl : (hypercubicLattice 2).induce S →g hypercubicLattice 2 :=
    { toFun := Subtype.val
      map_rel' := fun {a b} h => h }
  have hsfill : ∀ z ∈ (w.map incl).support,
      z ∈ squareHoleFill S hS := by
    intro z hz
    rw [Walk.support_map] at hz
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
    simpa [incl] using subset_squareHoleFill S hS u.2
  have hmid : (latticeMinusBarrier (squareHoleFill S hS)).Reachable sa sb :=
    by
      simpa [incl] using latticeWalk_reachable_barrier_of_support_subset
        (squareHoleFill S hS) (w.map incl) hsfill
  exact hasa.trans (hmid.trans hbsb.symm)


theorem squareHoleFill_outside_connected
    (S : Set (Site 2)) (hS : S.Finite) :
    ∀ a b : Site 2, a ∉ squareHoleFill S hS → b ∉ squareHoleFill S hS →
      (latticeMinusBarrier (squareHoleFill S hS)).Reachable a b := by
  intro a b ha hb
  have haout : (latticeMinusBarrier S).Reachable
      (beacon 2 (squareHoleFillRadius S hS)) a := by
    simpa [squareHoleFill, squareOuterComponent] using ha
  have hbout : (latticeMinusBarrier S).Reachable
      (beacon 2 (squareHoleFillRadius S hS)) b := by
    simpa [squareHoleFill, squareOuterComponent] using hb
  obtain ⟨wa⟩ := haout
  obtain ⟨wb⟩ := hbout
  have hwa : ∀ z ∈ wa.support, z ∉ squareHoleFill S hS := by
    intro z hz hzfill
    exact hzfill ⟨wa.takeUntil z hz⟩
  have hwb : ∀ z ∈ wb.support, z ∉ squareHoleFill S hS := by
    intro z hz hzfill
    exact hzfill ⟨wb.takeUntil z hz⟩
  have hwa' : ∀ z ∈ (wa.map (Hom.ofLE (latticeMinusBarrier_le S))).support,
      z ∉ squareHoleFill S hS := by
    intro z hz
    rw [Walk.support_map] at hz
    have hz' : z ∈ wa.support := by simpa using hz
    exact hwa z hz'
  have hwb' : ∀ z ∈ (wb.map (Hom.ofLE (latticeMinusBarrier_le S))).support,
      z ∉ squareHoleFill S hS := by
    intro z hz
    rw [Walk.support_map] at hz
    have hz' : z ∈ wb.support := by simpa using hz
    exact hwb z hz'
  have hra : (latticeMinusBarrier (squareHoleFill S hS)).Reachable
      (beacon 2 (squareHoleFillRadius S hS)) a :=
    latticeWalk_reachable_barrier_of_support_disjoint
      (squareHoleFill S hS) (wa.map (Hom.ofLE (latticeMinusBarrier_le S))) hwa'
  have hrb : (latticeMinusBarrier (squareHoleFill S hS)).Reachable
      (beacon 2 (squareHoleFillRadius S hS)) b :=
    latticeWalk_reachable_barrier_of_support_disjoint
      (squareHoleFill S hS) (wb.map (Hom.ofLE (latticeMinusBarrier_le S))) hwb'
  exact hra.symm.trans hrb



theorem squareHoleFill_faceBoundaryConnected
    (S : Set (Site 2)) (hS : S.Finite) (hne : S.Nonempty)
    (hconn : ∀ a b : S,
      ((hypercubicLattice 2).induce S).Reachable a b) :
    FaceBoundaryConnected (squareHoleFill S hS)
      (phb_boundarySupport (squareHoleFill S hS)
        (squareHoleFill_finite S hS)) := by
  have hne' := hne
  obtain ⟨x, hxS⟩ := hne
  let y := beacon 2 (squareHoleFillRadius S hS)
  apply faceBoundaryConnected_of_connected_complement
    (squareHoleFill S hS) (squareHoleFill_finite S hS)
    (x := x) (y := y)
  · exact subset_squareHoleFill S hS hxS
  · simp only [squareHoleFill, mem_compl_iff, not_not,
      squareOuterComponent, mem_setOf_eq]
    dsimp [y]
    exact Reachable.refl _
  · exact squareHoleFill_inside_connected S hS hne' hconn
  · exact squareHoleFill_outside_connected S hS


theorem squareHoleFill_faceBoundary_degree_eq_two
    (S : Set (Site 2)) (hS : S.Finite) (hne : S.Nonempty)
    (hconn : ∀ a b : S,
      ((hypercubicLattice 2).induce S).Reachable a b)
    {f : Site 2} (hf : f ∈ (faceBoundaryGraph (squareHoleFill S hS)).support) :
    (faceBoundaryGraph (squareHoleFill S hS)).degree f = 2 := by
  have hne' := hne
  obtain ⟨x, hxS⟩ := hne
  let y := beacon 2 (squareHoleFillRadius S hS)
  apply faceBoundaryGraph_degree_eq_two_of_connected_complement
    (squareHoleFill S hS) (squareHoleFill_finite S hS)
    (x := x) (y := y)
  · exact subset_squareHoleFill S hS hxS
  · simp only [squareHoleFill, mem_compl_iff, not_not,
      squareOuterComponent, mem_setOf_eq]
    dsimp [y]
    exact Reachable.refl _
  · exact squareHoleFill_inside_connected S hS hne' hconn
  · exact squareHoleFill_outside_connected S hS
  · exact hf

end

end StatMech.FrontierD
