/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingTorusFreeBoundaryComparison





open Finset
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech Ising Sharpness Lattice
open StatMech.Percolation

noncomputable section

variable {d k R : Nat}



theorem mk_mem_plusBoundaryEdges_iff (S : Finset (Site d)) (a b : Site d) :
    s(a, b) ∈ plusBoundaryEdges S ↔
      (hypercubicLattice d).Adj a b ∧
        ((a ∈ S ∧ b ∉ S) ∨ (a ∉ S ∧ b ∈ S)) := by
  classical
  constructor
  · intro h
    rw [plusBoundaryEdges, Finset.mem_filter] at h
    have htouch := h.1
    have hendpoint := gvBondTouch_endpoint htouch
    have hadj : (hypercubicLattice d).Adj a b := by
      rw [gvBondTouch, Finset.mem_image] at htouch
      obtain ⟨p, hp, he⟩ := htouch
      rw [Finset.mem_filter] at hp
      rw [Sym2.eq_iff] at he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hp.2.1
      · exact hp.2.1.symm
    refine ⟨hadj, ?_⟩
    rcases hendpoint with ha | hb
    · left
      refine ⟨ha, ?_⟩
      intro hb
      exact h.2 (fun v hv ↦ by
        rw [Sym2.mem_iff] at hv
        rcases hv with rfl | rfl <;> assumption)
    · right
      refine ⟨?_, hb⟩
      intro ha
      exact h.2 (fun v hv ↦ by
        rw [Sym2.mem_iff] at hv
        rcases hv with rfl | rfl <;> assumption)
  · rintro ⟨hab, ⟨ha, hb⟩ | ⟨ha, hb⟩⟩
    · rw [plusBoundaryEdges, Finset.mem_filter]
      constructor
      · rw [gvBondTouch, Finset.mem_image]
        refine ⟨(a, b), ?_, rfl⟩
        rw [Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨?_, ?_⟩, hab, Or.inl ha⟩
        · rw [gvCand, Finset.mem_biUnion]
          exact ⟨a, ha, gv_self_mem_ball a⟩
        · rw [gvCand, Finset.mem_biUnion]
          exact ⟨a, ha, gv_nbr_mem_ball hab⟩
      · intro hins
        exact hb (hins b (Sym2.mem_mk_right a b))
    · rw [plusBoundaryEdges, Finset.mem_filter]
      constructor
      · rw [gvBondTouch, Finset.mem_image]
        refine ⟨(a, b), ?_, rfl⟩
        rw [Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨?_, ?_⟩, hab, Or.inr hb⟩
        · rw [gvCand, Finset.mem_biUnion]
          exact ⟨b, hb, gv_nbr_mem_ball hab.symm⟩
        · rw [gvCand, Finset.mem_biUnion]
          exact ⟨b, hb, gv_self_mem_ball b⟩
      · intro hins
        exact ha (hins a (Sym2.mem_mk_left a b))



theorem exists_latticeNeighbor_lift_of_torusAdj (x : Site d)
    (z : IsingDyadicTorus d k)
    (h : (isingTorusGraph d k).Adj (isingSiteToDyadicTorus k x) z) :
    ∃ y : Site d, (hypercubicLattice d).Adj x y ∧
      isingSiteToDyadicTorus k y = z := by
  rw [isingTorusGraph_adj_iff] at h
  rcases h with ⟨i, h | h⟩
  · refine ⟨coordShift x i (stepSign true), adj_coordShift x i true, ?_⟩
    rw [isingSiteToDyadicTorus_coordShift]
    simpa using h.symm
  · refine ⟨coordShift x i (stepSign false), adj_coordShift x i false, ?_⟩
    rw [isingSiteToDyadicTorus_coordShift]
    simp only [Bool.false_eq_true, if_false]
    rw [h]
    abel


noncomputable def latticeNeighborLiftOfTorusAdj (x : Site d)
    (z : IsingDyadicTorus d k)
    (h : (isingTorusGraph d k).Adj (isingSiteToDyadicTorus k x) z) :
    Site d :=
  (exists_latticeNeighbor_lift_of_torusAdj x z h).choose

theorem latticeNeighborLiftOfTorusAdj_spec (x : Site d)
    (z : IsingDyadicTorus d k)
    (h : (isingTorusGraph d k).Adj (isingSiteToDyadicTorus k x) z) :
    (hypercubicLattice d).Adj x (latticeNeighborLiftOfTorusAdj x z h) ∧
      isingSiteToDyadicTorus k (latticeNeighborLiftOfTorusAdj x z h) = z :=
  (exists_latticeNeighbor_lift_of_torusAdj x z h).choose_spec



theorem finiteCutPlusBoundaryField_isingTorusImageEquiv
    (S : Finset (Site d)) (hS : (↑S : Set (Site d)) ⊆ box d R)
    (hside : 2 * (R + 1) < isingDyadicSide k)
    (hinj : Set.InjOn (isingSiteToDyadicTorus k) (↑S : Set (Site d)))
    (x : {x // x ∈ S}) :
    finiteCutPlusBoundaryField (isingTorusGraph d k)
        (isingTorusImageFinset k S) (isingTorusImageEquiv S hinj x) =
      plusBoundaryField S x := by
  classical
  let T := isingTorusImageFinset k S
  let z0 := isingSiteToDyadicTorus k x.1
  let A : Finset {z : IsingDyadicTorus d k // z ∉ T} :=
    Finset.univ.filter fun z ↦ (isingTorusGraph d k).Adj z0 z.1
  let C : Finset (Sym2 (Site d)) :=
    (plusBoundaryEdges S).filter fun e ↦ x.1 ∈ e
  change (∑ y : {z : IsingDyadicTorus d k // z ∉ T},
      if (isingTorusGraph d k).Adj z0 y.1 then 1 else 0) =
    (C.card : Real)
  rw [← Finset.sum_filter]
  change (∑ y ∈ A, (1 : Real)) = (C.card : Real)
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one]
  apply Finset.sum_bij
      (fun y hy ↦
        s(x.1, latticeNeighborLiftOfTorusAdj x.1 y.1
          (by simpa [A] using (Finset.mem_filter.1 hy).2)))
  · intro y hy
    have hyA := (Finset.mem_filter.1 hy).2
    have hyAdj : (isingTorusGraph d k).Adj z0 y.1 := by
      simpa [A] using hyA
    have hlift := latticeNeighborLiftOfTorusAdj_spec x.1 y.1
      (by simpa [z0] using hyAdj)
    have hliftOut : latticeNeighborLiftOfTorusAdj x.1 y.1
        (by simpa [z0] using hyAdj) ∉ S := by
      intro hmem
      exact y.2 (by
        rw [mem_isingTorusImageFinset]
        exact ⟨_, hmem, hlift.2⟩)
    simp only [C, Finset.mem_filter]
    exact ⟨(mk_mem_plusBoundaryEdges_iff S _ _).2
      ⟨hlift.1, Or.inl ⟨x.2, hliftOut⟩⟩,
      Sym2.mem_mk_left _ _⟩
  · intro a ha b hb hab
    have haA := (Finset.mem_filter.1 ha).2
    have hbA := (Finset.mem_filter.1 hb).2
    have haAdj : (isingTorusGraph d k).Adj z0 a.1 := by
      simpa [A] using haA
    have hbAdj : (isingTorusGraph d k).Adj z0 b.1 := by
      simpa [A] using hbA
    let haProof : (isingTorusGraph d k).Adj
        (isingSiteToDyadicTorus k x.1) a.1 := by simpa [z0] using haAdj
    let hbProof : (isingTorusGraph d k).Adj
        (isingSiteToDyadicTorus k x.1) b.1 := by simpa [z0] using hbAdj
    let la := latticeNeighborLiftOfTorusAdj x.1 a.1 haProof
    let lb := latticeNeighborLiftOfTorusAdj x.1 b.1 hbProof
    have hla := latticeNeighborLiftOfTorusAdj_spec x.1 a.1 haProof
    have hlb := latticeNeighborLiftOfTorusAdj_spec x.1 b.1 hbProof
    have hlaOut : la ∉ S := by
      intro hmem
      exact a.2 (by
        rw [mem_isingTorusImageFinset]
        exact ⟨_, hmem, hla.2⟩)
    have hlbOut : lb ∉ S := by
      intro hmem
      exact b.2 (by
        rw [mem_isingTorusImageFinset]
        exact ⟨_, hmem, hlb.2⟩)
    change s(x.1, la) = s(x.1, lb) at hab
    rw [Sym2.eq_iff] at hab
    rcases hab with hab | hab
    · exact Subtype.ext (hla.2.symm.trans
        ((congrArg (isingSiteToDyadicTorus k) hab.2).trans hlb.2))
    · exact (hlaOut (hab.2.symm ▸ x.2)).elim
  · intro e he
    simp only [C, Finset.mem_filter] at he
    induction e using Sym2.inductionOn with
    | _ a b =>
      rw [Sym2.mem_iff] at he
      rcases he.2 with hxa | hxb
      · subst a
        have hedge := (mk_mem_plusBoundaryEdges_iff S x.1 b).1 he.1
        rcases hedge.2 with hcross | hcross
        · let y : {z : IsingDyadicTorus d k // z ∉ T} :=
            ⟨isingSiteToDyadicTorus k b, by
              intro hbT
              obtain ⟨w, hwS, hw⟩ := mem_isingTorusImageFinset.mp hbT
              have hbBox : b ∈ box d (R + 1) := by
                obtain ⟨i, q, rfl⟩ := adj_exists_dir hedge.1
                exact coordShift_mem_box_succ (hS x.2) i q
              have hwBox : w ∈ box d (R + 1) :=
                box_mono d (Nat.le_succ R) (hS hwS)
              have := isingSiteToDyadicTorus_injectiveOn_box hside
                hwBox hbBox hw
              exact hcross.2 (this ▸ hwS)⟩
          have hyAdj : (isingTorusGraph d k).Adj z0 y.1 := by
            simpa [z0, y] using isingSiteToDyadicTorus_map_adj hedge.1
          refine ⟨y, ?_, ?_⟩
          · simp only [A, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hyAdj⟩
          · rw [Sym2.eq_iff]
            left
            refine ⟨rfl, ?_⟩
            have hspec := latticeNeighborLiftOfTorusAdj_spec x.1 y.1
              (by simpa [z0] using hyAdj)
            have hliftBox : latticeNeighborLiftOfTorusAdj x.1 y.1
                (by simpa [z0] using hyAdj) ∈ box d (R + 1) := by
              obtain ⟨i, q, hdir⟩ := adj_exists_dir hspec.1
              rw [hdir]
              exact coordShift_mem_box_succ (hS x.2) i q
            have hbBox : b ∈ box d (R + 1) := by
              obtain ⟨i, q, rfl⟩ := adj_exists_dir hedge.1
              exact coordShift_mem_box_succ (hS x.2) i q
            exact isingSiteToDyadicTorus_injectiveOn_box hside
              hliftBox hbBox (by simpa [y] using hspec.2)
        · exact (hcross.1 x.2).elim
      · subst b
        have hedge := (mk_mem_plusBoundaryEdges_iff S a x.1).1 he.1
        rcases hedge.2 with hcross | hcross
        · exact (hcross.2 x.2).elim
        · let y : {z : IsingDyadicTorus d k // z ∉ T} :=
            ⟨isingSiteToDyadicTorus k a, by
              intro haT
              obtain ⟨w, hwS, hw⟩ := mem_isingTorusImageFinset.mp haT
              have haBox : a ∈ box d (R + 1) := by
                obtain ⟨i, q, rfl⟩ := adj_exists_dir hedge.1.symm
                exact coordShift_mem_box_succ (hS x.2) i q
              have hwBox : w ∈ box d (R + 1) :=
                box_mono d (Nat.le_succ R) (hS hwS)
              have := isingSiteToDyadicTorus_injectiveOn_box hside
                hwBox haBox hw
              exact hcross.1 (this ▸ hwS)⟩
          have hyAdj : (isingTorusGraph d k).Adj z0 y.1 := by
            simpa [z0, y] using isingSiteToDyadicTorus_map_adj hedge.1.symm
          refine ⟨y, ?_, ?_⟩
          · simp only [A, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hyAdj⟩
          · rw [Sym2.eq_iff]
            right
            refine ⟨rfl, ?_⟩
            have hspec := latticeNeighborLiftOfTorusAdj_spec x.1 y.1
              (by simpa [z0] using hyAdj)
            have hliftBox : latticeNeighborLiftOfTorusAdj x.1 y.1
                (by simpa [z0] using hyAdj) ∈ box d (R + 1) := by
              obtain ⟨i, q, hdir⟩ := adj_exists_dir hspec.1
              rw [hdir]
              exact coordShift_mem_box_succ (hS x.2) i q
            have haBox : a ∈ box d (R + 1) := by
              obtain ⟨i, q, rfl⟩ := adj_exists_dir hedge.1.symm
              exact coordShift_mem_box_succ (hS x.2) i q
            exact isingSiteToDyadicTorus_injectiveOn_box hside
              hliftBox haBox (by simpa [y] using hspec.2)
  · intro y hy
    rfl

end

end StatMech.FrontierA
