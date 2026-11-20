/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKQgt4SquareDualBundles
import Code.FK.IndexedEdgeLumping
import Code.FK.Tilt

open Finset Set SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

noncomputable section

local instance pfdFullDualDecidableRel (P : PlanarZ2Subgraph) :
    DecidableRel (pfdClosedDual P ⊥).Adj := Classical.decRel _



def pfdIndexedSupportActive (P : PlanarZ2Subgraph)
    (eta : ConfigSpace P.G.edgeSet) :
    ConfigSpace (pfdClosedDual P ⊥).edgeSet :=
  restrictActive (pfdClosedDual P ⊥)
    (indexedBundleSupport (kwg_dualEnds P) eta)


def pfdEdgeComplement (P : PlanarZ2Subgraph) :
    ConfigSpace P.G.edgeSet ≃ ConfigSpace P.G.edgeSet where
  toFun omega e := !(omega e)
  invFun omega e := !(omega e)
  left_inv := by intro omega; funext e; simp
  right_inv := by intro omega; funext e; simp

@[simp] theorem pfdEdgeComplement_apply (P : PlanarZ2Subgraph)
    (omega : ConfigSpace P.G.edgeSet) (e : P.G.edgeSet) :
    pfdEdgeComplement P omega e = !(omega e) := rfl

@[simp] theorem pfdEdgeComplement_symm_apply (P : PlanarZ2Subgraph)
    (omega : ConfigSpace P.G.edgeSet) (e : P.G.edgeSet) :
    (pfdEdgeComplement P).symm omega e = !(omega e) := rfl

@[simp] theorem pfdEdgeComplement_involutive (P : PlanarZ2Subgraph)
    (omega : ConfigSpace P.G.edgeSet) :
    pfdEdgeComplement P (pfdEdgeComplement P omega) = omega := by
  funext e
  simp

private theorem openCount_complement {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (omega : ConfigSpace (Sym2 V)) :
    openCount G (fun e => !(omega e)) = G.edgeFinset.card - openCount G omega := by
  have hclosed : openCount G (fun e => !(omega e)) = closedCount G omega := by
    unfold openCount closedCount
    congr 1
    ext e
    simp only [Finset.mem_filter]
    cases omega e <;> simp
  rw [hclosed]
  have hsum := openCount_add_closedCount G omega
  omega

private theorem mem_openSub_edgeSet_iff_of_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (omega : ConfigSpace (Sym2 V)) {e : Sym2 V}
    (he : e ∈ G.edgeSet) :
    e ∈ (openSub G omega).edgeSet ↔ omega e = true := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet, openSub_adj]
      rw [SimpleGraph.mem_edgeSet] at he
      simp [he]



theorem pfdDualEdgeProduct_eq_indexed (P : PlanarZ2Subgraph)
    (p : Real) (omega : ConfigSpace (Sym2 P.V)) :
    edgeProductCount p P.G.edgeFinset.card
        (P.G.edgeFinset.card - (openSub P.G omega).edgeSet.ncard) =
      indexedBernoulliWeight p
        (fun e : kwg_Edge P => !(omega e.1)) := by
  rw [pfd_openSub_edge_ncard]
  calc
    edgeProductCount p P.G.edgeFinset.card
        (P.G.edgeFinset.card - openCount P.G omega) =
        edgeProductCount p P.G.edgeFinset.card
          (openCount P.G (fun e => !(omega e))) := by
      rw [openCount_complement]
    _ = edgeProduct P.G p (fun e => !(omega e)) :=
      (dlt_edgeProduct_eq_count P.G p (fun e => !(omega e))).symm
    _ = indexedBernoulliWeight p
        (fun e : kwg_Edge P => !(omega e.1)) := by
      unfold edgeProduct indexedBernoulliWeight
      rw [← Finset.prod_attach P.G.edgeFinset]
      rw [Finset.attach_eq_univ]
      let edgeEquiv : P.G.edgeFinset ≃ kwg_Edge P :=
        { toFun := fun e => ⟨e.1, by simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
          invFun := fun e => ⟨e.1, by simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
          left_inv := by intro e; rfl
          right_inv := by intro e; rfl }
      apply Fintype.prod_equiv edgeEquiv
      intro e
      rfl



theorem pfdClosedDual_eq_openSub_indexedSupport (P : PlanarZ2Subgraph)
    (omega : ConfigSpace (Sym2 P.V)) :
    pfdClosedDual P (openSub P.G omega) =
      openSub (pfdClosedDual P ⊥)
        (extendActive (pfdClosedDual P ⊥)
          (pfdIndexedSupportActive P
            (fun e : kwg_Edge P => !(omega e.1)))) := by
  ext C D
  rw [pfdClosedDual_adj, openSub_adj]
  constructor
  · rintro ⟨hne, e, heclosed, hends⟩
    have hfull : (pfdClosedDual P ⊥).Adj C D :=
      (pfdClosedDual_adj P ⊥ C D).2 ⟨hne, e, by simp, hends⟩
    refine ⟨hfull, ?_⟩
    let a : (pfdClosedDual P ⊥).edgeSet :=
      ⟨s(C, D), by simpa [SimpleGraph.mem_edgeSet] using hfull⟩
    change extendActive (pfdClosedDual P ⊥)
      (pfdIndexedSupportActive P
        (fun e : kwg_Edge P => !(omega e.1))) a.1 = true
    rw [extendActive_apply]
    simp only [pfdIndexedSupportActive, restrictActive,
      indexedBundleSupport, decide_eq_true_eq]
    refine ⟨e, hends, ?_⟩
    have hnot : omega e.1 ≠ true := by
      intro hopen
      exact heclosed ((mem_openSub_edgeSet_iff_of_mem P.G omega e.2).2 hopen)
    cases homega : omega e.1 <;> simp_all
  · rintro ⟨hfull, hopen⟩
    have hfullEdge : s(C, D) ∈ (pfdClosedDual P ⊥).edgeSet := by
      simpa [SimpleGraph.mem_edgeSet] using hfull
    let a : (pfdClosedDual P ⊥).edgeSet := ⟨s(C, D), hfullEdge⟩
    change extendActive (pfdClosedDual P ⊥)
      (pfdIndexedSupportActive P
        (fun e : kwg_Edge P => !(omega e.1))) a.1 = true at hopen
    rw [extendActive_apply] at hopen
    rw [pfdClosedDual_adj] at hfull
    obtain ⟨hne, _, _, _⟩ := hfull
    simp only [pfdIndexedSupportActive, restrictActive,
      indexedBundleSupport, decide_eq_true_eq] at hopen
    obtain ⟨e, hends, heopen⟩ := hopen
    refine ⟨hne, e, ?_, hends⟩
    intro hmem
    have hopenPrimal :=
      (mem_openSub_edgeSet_iff_of_mem P.G omega e.2).1 hmem
    cases h : omega e.1 <;> simp_all


theorem pfdDualWeight_eq_indexedSupport (P : PlanarZ2Subgraph)
    (p q : Real) (omega : ConfigSpace (Sym2 P.V)) :
    pfdDualWeight P p q (openSub P.G omega) =
      indexedBernoulliWeight p
          (fun e : kwg_Edge P => !(omega e.1)) *
        q ^ (numClustersBC (pfdClosedDual P ⊥) ⊥
          (extendActive (pfdClosedDual P ⊥)
            (pfdIndexedSupportActive P
              (fun e : kwg_Edge P => !(omega e.1))))) := by
  unfold pfdDualWeight
  rw [pfdDualEdgeProduct_eq_indexed]
  congr 1
  unfold numClustersBC
  rw [sup_bot_eq, ← pfdClosedDual_eq_openSub_indexedSupport]





def fkSquareDualLumpedParam (N m : Nat) (p : Real)
    (a : Sym2 (kwg_Face (fkSquareBoxPlanar m))) : Real :=
  if a ∈ Set.range (ocd_innerEdge (fkSquareBox_innerFaceMap N m)) then p
  else if a ∈ (fkSquareBoxFullDualGraph m).edgeSet then
    indexedEffectiveParam (kwg_dualEnds (fkSquareBoxPlanar m)) p a
  else 1 / 2

theorem fkSquareDualLumpedParam_compatible
    (N m : Nat) (p : Real) :
    ocd_ParamCompatible (fkSquareBox_innerFaceMap N m)
      (fun _ => p) (fkSquareDualLumpedParam N m p) := by
  intro e
  simp [fkSquareDualLumpedParam]

private theorem indexedEffectiveParam_eq_pfdEffectiveParam
    (P : PlanarZ2Subgraph) (p : Real)
    (a : Sym2 (kwg_Face P)) :
    indexedEffectiveParam (kwg_dualEnds P) p a =
      pfdEffectiveParam P p a := by
  rfl



theorem fkSquareDualLumpedParam_eq_effective_on_edge
    {N m : Nat} (hNm : N < m) (p : Real)
    {a : Sym2 (kwg_Face (fkSquareBoxPlanar m))}
    (ha : a ∈ (fkSquareBoxFullDualGraph m).edgeSet) :
    fkSquareDualLumpedParam N m p a =
      indexedEffectiveParam (kwg_dualEnds (fkSquareBoxPlanar m)) p a := by
  unfold fkSquareDualLumpedParam
  split
  · rename_i hrange
    obtain ⟨e, rfl⟩ := hrange
    have himage : ocd_innerEdge (fkSquareBox_innerFaceMap N m) e ∈
        (FK.boxGraph 2 N).edgeFinset.image
          (ocd_innerEdge (fkSquareBox_innerFaceMap N m)) := by
      rw [ocd_innerEdge_image_edgeFinset
        (fkSquareBox_innerFaceMap_injective hNm)
        (fkSquareBox_innerFaceMap_adjMatch hNm)]
      exact Finset.mem_filter.mpr
        ⟨by simpa only [SimpleGraph.mem_edgeFinset] using ha, ⟨e, rfl⟩⟩
    obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp himage
    have heq : e = b :=
      ocd_innerEdge_injective _ (fkSquareBox_innerFaceMap_injective hNm) hbe.symm
    subst e
    rw [indexedEffectiveParam_eq_pfdEffectiveParam]
    exact (pfdEffectiveParam_innerEdge hNm p ⟨b, hb⟩).symm
  · simp [ha]

theorem fkSquareDualLumpedParam_pos
    {N m : Nat} (hNm : N < m) {p : Real}
    (hp : 0 < p) (hp1 : p < 1)
    (a : Sym2 (kwg_Face (fkSquareBoxPlanar m))) :
    0 < fkSquareDualLumpedParam N m p a := by
  unfold fkSquareDualLumpedParam
  split
  · exact hp
  · split
    · rename_i ha
      rw [indexedEffectiveParam_eq_pfdEffectiveParam]
      exact pfdEffectiveParam_pos _ hp hp1 ha
    · norm_num

theorem fkSquareDualLumpedParam_lt_one
    {N m : Nat} (hNm : N < m) {p : Real}
    (hp : 0 < p) (hp1 : p < 1)
    (a : Sym2 (kwg_Face (fkSquareBoxPlanar m))) :
    fkSquareDualLumpedParam N m p a < 1 := by
  unfold fkSquareDualLumpedParam
  split
  · exact hp1
  · split
    · rw [indexedEffectiveParam_eq_pfdEffectiveParam]
      exact pfdEffectiveParam_lt_one _ hp hp1 _
    · norm_num

private theorem edgeProductW_lumpedParam_extendActive
    {N m : Nat} (hNm : N < m) (p : Real)
    (rho : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet) :
    edgeProductW (fkSquareBoxFullDualGraph m)
        (fkSquareDualLumpedParam N m p)
        (extendActive (fkSquareBoxFullDualGraph m) rho) =
      ∏ a : (fkSquareBoxFullDualGraph m).edgeSet,
        if rho a then
          indexedEffectiveParam (kwg_dualEnds (fkSquareBoxPlanar m)) p a.1
        else 1 - indexedEffectiveParam
          (kwg_dualEnds (fkSquareBoxPlanar m)) p a.1 := by
  unfold edgeProductW
  rw [← Finset.prod_attach (fkSquareBoxFullDualGraph m).edgeFinset,
    Finset.attach_eq_univ]
  let edgeEquiv : (fkSquareBoxFullDualGraph m).edgeFinset ≃
      (fkSquareBoxFullDualGraph m).edgeSet :=
    { toFun := fun e => ⟨e.1, by simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
      invFun := fun e => ⟨e.1, by simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
      left_inv := by intro e; rfl
      right_inv := by intro e; rfl }
  apply Fintype.prod_equiv edgeEquiv
  intro e
  change (if extendActive (fkSquareBoxFullDualGraph m) rho (edgeEquiv e).1 then
      fkSquareDualLumpedParam N m p (edgeEquiv e).1
    else 1 - fkSquareDualLumpedParam N m p (edgeEquiv e).1) = _
  rw [extendActive_apply,
    fkSquareDualLumpedParam_eq_effective_on_edge hNm _ (edgeEquiv e).2]



theorem pfdIndexedWeight_lumping
    {N m : Nat} (hNm : N < m) (p q : Real)
    (F : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet → Real) :
    (∑ eta : ConfigSpace (fkSquareBoxPlanar m).G.edgeSet,
      indexedBernoulliWeight p eta *
        (F (pfdIndexedSupportActive (fkSquareBoxPlanar m) eta) *
          q ^ numClustersBC (fkSquareBoxFullDualGraph m) ⊥
            (extendActive (fkSquareBoxFullDualGraph m)
              (pfdIndexedSupportActive (fkSquareBoxPlanar m) eta)))) =
    ∑ rho : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet,
      F rho * activeBCWeight (fkSquareBoxFullDualGraph m) ⊥
        (fkSquareDualLumpedParam N m p) q rho := by
  have h := sum_indexedBernoulliWeight_restrictActive_bundleSupport
    (fkSquareBoxFullDualGraph m) p
    (kwg_dualEnds (fkSquareBoxPlanar m))
    (fun rho => F rho * q ^ numClustersBC
      (fkSquareBoxFullDualGraph m) ⊥
        (extendActive (fkSquareBoxFullDualGraph m) rho))
  change (∑ eta : ConfigSpace (fkSquareBoxPlanar m).G.edgeSet,
      indexedBernoulliWeight p eta *
        (F (restrictActive (fkSquareBoxFullDualGraph m)
          (indexedBundleSupport (kwg_dualEnds (fkSquareBoxPlanar m)) eta)) *
        q ^ numClustersBC (fkSquareBoxFullDualGraph m) ⊥
          (extendActive (fkSquareBoxFullDualGraph m)
            (restrictActive (fkSquareBoxFullDualGraph m)
              (indexedBundleSupport (kwg_dualEnds (fkSquareBoxPlanar m)) eta))))) = _
  rw [h]
  apply Finset.sum_congr rfl
  intro rho _
  rw [activeBCWeight,
    edgeProductW_lumpedParam_extendActive hNm]
  ring



def fkSquarePfdSupport (m : Nat)
    (omega : ConfigSpace (Sym2 (FK.boxVerts 2 m))) :
    ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet :=
  pfdIndexedSupportActive (fkSquareBoxPlanar m)
    (pfdEdgeComplement (fkSquareBoxPlanar m)
      (restrictActive (FK.boxGraph 2 m) omega))

private theorem pfdDualWeight_openSub_eq_of_edges
    (P : PlanarZ2Subgraph) (p q : Real)
    (omega eta : ConfigSpace (Sym2 P.V))
    (h : ∀ e ∈ P.G.edgeFinset, omega e = eta e) :
    pfdDualWeight P p q (openSub P.G omega) =
      pfdDualWeight P p q (openSub P.G eta) := by
  rw [ecz_openSub_eq_of_edges P.G omega eta h]

private theorem fkSquarePfdWeight_activeSplit
    (m : Nat) (p q : Real)
    (eta : ConfigSpace (FK.boxGraph 2 m).edgeSet)
    (xi : ConfigSpace {e : Sym2 (FK.boxVerts 2 m) //
      e ∉ (FK.boxGraph 2 m).edgeSet}) :
    pfdDualWeight (fkSquareBoxPlanar m) p q
        (openSub (FK.boxGraph 2 m)
          ((activeSplitEquiv (FK.boxGraph 2 m)).symm (eta, xi))) =
      pfdDualWeight (fkSquareBoxPlanar m) p q
        (openSub (FK.boxGraph 2 m)
          (extendActive (FK.boxGraph 2 m) eta)) := by
  apply pfdDualWeight_openSub_eq_of_edges
  intro e he
  have heSet : e ∈ (FK.boxGraph 2 m).edgeSet := by
    simpa only [SimpleGraph.mem_edgeFinset] using he
  have hsplit := congrFun
    (restrictActive_activeSplitEquiv_symm (FK.boxGraph 2 m) eta xi)
    ⟨e, heSet⟩
  calc
    ((activeSplitEquiv (FK.boxGraph 2 m)).symm (eta, xi)) e =
        eta ⟨e, heSet⟩ := hsplit
    _ = extendActive (FK.boxGraph 2 m) eta e := by
      symm
      exact extendActive_apply (FK.boxGraph 2 m) eta ⟨e, heSet⟩




theorem fkSquare_pfdDualNumer_eq_lumped
    {N m : Nat} (hNm : N < m) (p q : Real)
    (F : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet → Real) :
    (∑ omega : ConfigSpace (Sym2 (FK.boxVerts 2 m)),
      F (fkSquarePfdSupport m omega) *
        pfdDualWeight (fkSquareBoxPlanar m) p q
          (openSub (FK.boxGraph 2 m) omega)) =
      2 ^ ecz_NE (FK.boxGraph 2 m) *
        ∑ rho : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet,
          F rho * activeBCWeight (fkSquareBoxFullDualGraph m) ⊥
            (fkSquareDualLumpedParam N m p) q rho := by
  rw [← Equiv.sum_comp (activeSplitEquiv (FK.boxGraph 2 m)).symm,
    Fintype.sum_prod_type]
  have key : ∀ eta : ConfigSpace (FK.boxGraph 2 m).edgeSet,
      (∑ xi : ConfigSpace {e : Sym2 (FK.boxVerts 2 m) //
          e ∉ (FK.boxGraph 2 m).edgeSet},
        F (fkSquarePfdSupport m
          ((activeSplitEquiv (FK.boxGraph 2 m)).symm (eta, xi))) *
        pfdDualWeight (fkSquareBoxPlanar m) p q
          (openSub (FK.boxGraph 2 m)
            ((activeSplitEquiv (FK.boxGraph 2 m)).symm (eta, xi)))) =
        2 ^ ecz_NE (FK.boxGraph 2 m) *
          (F (pfdIndexedSupportActive (fkSquareBoxPlanar m)
              (pfdEdgeComplement (fkSquareBoxPlanar m) eta)) *
            pfdDualWeight (fkSquareBoxPlanar m) p q
              (openSub (FK.boxGraph 2 m)
                (extendActive (FK.boxGraph 2 m) eta))) := by
    intro eta
    rw [Finset.sum_congr rfl (fun xi _ => by
      simp only [fkSquarePfdSupport]
      rw [restrictActive_activeSplitEquiv_symm,
        fkSquarePfdWeight_activeSplit])]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      card_inactive_config (FK.boxGraph 2 m)]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun eta _ => key eta), ← Finset.mul_sum]
  congr 1
  have hreindex :
      (∑ i : ConfigSpace (fkSquareBoxPlanar m).G.edgeSet,
        F (pfdIndexedSupportActive (fkSquareBoxPlanar m)
            (pfdEdgeComplement (fkSquareBoxPlanar m) i)) *
          pfdDualWeight (fkSquareBoxPlanar m) p q
            (openSub (FK.boxGraph 2 m)
              (extendActive (FK.boxGraph 2 m) i))) =
        ∑ eta : ConfigSpace (fkSquareBoxPlanar m).G.edgeSet,
          F (pfdIndexedSupportActive (fkSquareBoxPlanar m) eta) *
            pfdDualWeight (fkSquareBoxPlanar m) p q
              (openSub (FK.boxGraph 2 m)
                (extendActive (FK.boxGraph 2 m)
                  (pfdEdgeComplement (fkSquareBoxPlanar m) eta))) := by
    let g := fun eta : ConfigSpace (fkSquareBoxPlanar m).G.edgeSet =>
      F (pfdIndexedSupportActive (fkSquareBoxPlanar m) eta) *
        pfdDualWeight (fkSquareBoxPlanar m) p q
          (openSub (FK.boxGraph 2 m)
            (extendActive (FK.boxGraph 2 m)
              (pfdEdgeComplement (fkSquareBoxPlanar m) eta)))
    simpa only [g, pfdEdgeComplement_involutive] using
      (Equiv.sum_comp (pfdEdgeComplement (fkSquareBoxPlanar m)) g)
  have hpoint : ∀ eta : ConfigSpace (fkSquareBoxPlanar m).G.edgeSet,
      pfdDualWeight (fkSquareBoxPlanar m) p q
          (openSub (FK.boxGraph 2 m)
            (extendActive (FK.boxGraph 2 m)
              (pfdEdgeComplement (fkSquareBoxPlanar m) eta))) =
        indexedBernoulliWeight p eta *
          q ^ numClustersBC (fkSquareBoxFullDualGraph m) ⊥
            (extendActive (fkSquareBoxFullDualGraph m)
              (pfdIndexedSupportActive (fkSquareBoxPlanar m) eta)) := by
    intro eta
    change pfdDualWeight (fkSquareBoxPlanar m) p q
        (openSub (fkSquareBoxPlanar m).G
          (extendActive (fkSquareBoxPlanar m).G
            (pfdEdgeComplement (fkSquareBoxPlanar m) eta))) = _
    rw [pfdDualWeight_eq_indexedSupport]
    have hcomp :
        (fun e : kwg_Edge (fkSquareBoxPlanar m) =>
          !(extendActive (fkSquareBoxPlanar m).G
            (pfdEdgeComplement (fkSquareBoxPlanar m) eta) e.1)) = eta := by
      funext e
      rw [extendActive_apply, pfdEdgeComplement_apply]
      simp
    rw [hcomp]
    unfold fkSquareBoxFullDualGraph
    rfl
  refine hreindex.trans ?_
  rw [Finset.sum_congr rfl (fun eta _ => by rw [hpoint eta])]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    pfdIndexedWeight_lumping hNm p q F


theorem fkSquare_pfdDualZ_eq_lumped
    {N m : Nat} (hNm : N < m) (p q : Real) :
    pfdDualZ (fkSquareBoxPlanar m) p q =
      2 ^ ecz_NE (FK.boxGraph 2 m) *
        activeBCZ (fkSquareBoxFullDualGraph m) ⊥
          (fkSquareDualLumpedParam N m p) q := by
  unfold pfdDualZ activeBCZ
  simpa using fkSquare_pfdDualNumer_eq_lumped hNm p q (fun _ => 1)



theorem fkSquare_pfdDualMean_eq_lumped
    {N m : Nat} (hNm : N < m) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet → Real) :
    (∑ omega : ConfigSpace (Sym2 (FK.boxVerts 2 m)),
      F (fkSquarePfdSupport m omega) *
        pfdDualProb (fkSquareBoxPlanar m) p q omega) =
      ∑ rho : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet,
        F rho * activeBCProb (fkSquareBoxFullDualGraph m) ⊥
          (fkSquareDualLumpedParam N m p) q rho := by
  unfold pfdDualProb activeBCProb
  change
    (∑ omega : ConfigSpace (Sym2 (FK.boxVerts 2 m)),
      F (fkSquarePfdSupport m omega) *
        (pfdDualWeight (fkSquareBoxPlanar m) p q
          (openSub (FK.boxGraph 2 m) omega) /
            pfdDualZ (fkSquareBoxPlanar m) p q)) =
      ∑ rho : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet,
        F rho * (activeBCWeight (fkSquareBoxFullDualGraph m) ⊥
          (fkSquareDualLumpedParam N m p) q rho /
            activeBCZ (fkSquareBoxFullDualGraph m) ⊥
              (fkSquareDualLumpedParam N m p) q)
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, ← Finset.sum_div,
    fkSquare_pfdDualNumer_eq_lumped hNm,
    fkSquare_pfdDualZ_eq_lumped hNm]
  have htwo : (2 : Real) ^ ecz_NE (FK.boxGraph 2 m) ≠ 0 := by positivity
  have hZ : activeBCZ (fkSquareBoxFullDualGraph m) ⊥
      (fkSquareDualLumpedParam N m p) q ≠ 0 :=
    (activeBCZ_pos _ _
      (fkSquareDualLumpedParam_pos hNm hp hp1)
      (fkSquareDualLumpedParam_lt_one hNm hp hp1) hq).ne'
  field_simp

end

end StatMech.FrontierD
