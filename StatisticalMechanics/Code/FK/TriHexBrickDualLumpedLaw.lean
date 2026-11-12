/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexBrickDualBundles
import Code.FrontierD.FKQgt4SquareDualLumpedLaw









open Finset Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC
open StatMech.FrontierD

noncomputable section


def triHexBrickDualLumpedParam (N m : Nat) (p : Real)
    (a : Sym2 (kwg_Face (triHexPlanarFiniteStarPlanar m))) : Real :=
  if a ∈ Set.range (ocd_innerEdge (triHexBrickInnerFaceMap N m)) then p
  else if a ∈ (triHexBrickFullDualGraph m).edgeSet then
    indexedEffectiveParam
      (kwg_dualEnds (triHexPlanarFiniteStarPlanar m)) p a
  else 1 / 2

theorem triHexBrickDualLumpedParam_compatible
    (N m : Nat) (p : Real) :
    ocd_ParamCompatible (triHexBrickInnerFaceMap N m)
      (fun _ => p) (triHexBrickDualLumpedParam N m p) := by
  intro e
  simp [triHexBrickDualLumpedParam]



theorem triHexBrickDualLumpedParam_eq_effective_on_edge
    {N m : Nat} (hNm : N < m) (p : Real)
    {a : Sym2 (kwg_Face (triHexPlanarFiniteStarPlanar m))}
    (ha : a ∈ (triHexBrickFullDualGraph m).edgeSet) :
    triHexBrickDualLumpedParam N m p a =
      indexedEffectiveParam
        (kwg_dualEnds (triHexPlanarFiniteStarPlanar m)) p a := by
  unfold triHexBrickDualLumpedParam
  split
  · rename_i hrange
    obtain ⟨e, rfl⟩ := hrange
    have himage : ocd_innerEdge (triHexBrickInnerFaceMap N m) e ∈
        (triHexBrickInnerTriangleGraph N).edgeFinset.image
          (ocd_innerEdge (triHexBrickInnerFaceMap N m)) := by
      rw [ocd_innerEdge_image_edgeFinset
        (triHexBrickInnerFaceMap_injective hNm)
        (triHexBrickInnerFaceMap_adjMatch hNm)]
      exact Finset.mem_filter.mpr
        ⟨by simpa only [SimpleGraph.mem_edgeFinset] using ha, ⟨e, rfl⟩⟩
    obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp himage
    have heq : e = b :=
      ocd_innerEdge_injective _
        (triHexBrickInnerFaceMap_injective hNm) hbe.symm
    subst e
    change p = pfdEffectiveParam (triHexPlanarFiniteStarPlanar m) p
      (ocd_innerEdge (triHexBrickInnerFaceMap N m) b)
    exact (triHexBrick_pfdEffectiveParam_innerEdge
      hNm p ⟨b, hb⟩).symm
  · simp [ha]

theorem triHexBrickDualLumpedParam_pos
    {N m : Nat} (hNm : N < m) {p : Real}
    (hp : 0 < p) (hp1 : p < 1)
    (a : Sym2 (kwg_Face (triHexPlanarFiniteStarPlanar m))) :
    0 < triHexBrickDualLumpedParam N m p a := by
  unfold triHexBrickDualLumpedParam
  split
  · exact hp
  · split
    · rename_i ha
      change 0 < pfdEffectiveParam
        (triHexPlanarFiniteStarPlanar m) p a
      exact pfdEffectiveParam_pos _ hp hp1 ha
    · norm_num

theorem triHexBrickDualLumpedParam_lt_one
    {N m : Nat} (hNm : N < m) {p : Real}
    (hp : 0 < p) (hp1 : p < 1)
    (a : Sym2 (kwg_Face (triHexPlanarFiniteStarPlanar m))) :
    triHexBrickDualLumpedParam N m p a < 1 := by
  unfold triHexBrickDualLumpedParam
  split
  · exact hp1
  · split
    · change pfdEffectiveParam
        (triHexPlanarFiniteStarPlanar m) p a < 1
      exact pfdEffectiveParam_lt_one _ hp hp1 _
    · norm_num

private theorem triHexBrick_edgeProductW_lumpedParam_extendActive
    {N m : Nat} (hNm : N < m) (p : Real)
    (rho : ConfigSpace (triHexBrickFullDualGraph m).edgeSet) :
    edgeProductW (triHexBrickFullDualGraph m)
        (triHexBrickDualLumpedParam N m p)
        (extendActive (triHexBrickFullDualGraph m) rho) =
      ∏ a : (triHexBrickFullDualGraph m).edgeSet,
        if rho a then
          indexedEffectiveParam
            (kwg_dualEnds (triHexPlanarFiniteStarPlanar m)) p a.1
        else 1 - indexedEffectiveParam
          (kwg_dualEnds (triHexPlanarFiniteStarPlanar m)) p a.1 := by
  unfold edgeProductW
  rw [← Finset.prod_attach (triHexBrickFullDualGraph m).edgeFinset,
    Finset.attach_eq_univ]
  let edgeEquiv : (triHexBrickFullDualGraph m).edgeFinset ≃
      (triHexBrickFullDualGraph m).edgeSet :=
    { toFun := fun e =>
        ⟨e.1, by simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
      invFun := fun e =>
        ⟨e.1, by simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
      left_inv := by intro e; rfl
      right_inv := by intro e; rfl }
  apply Fintype.prod_equiv edgeEquiv
  intro e
  change (if extendActive (triHexBrickFullDualGraph m) rho
        (edgeEquiv e).1 then
      triHexBrickDualLumpedParam N m p (edgeEquiv e).1
    else 1 - triHexBrickDualLumpedParam N m p (edgeEquiv e).1) = _
  rw [extendActive_apply,
    triHexBrickDualLumpedParam_eq_effective_on_edge
      hNm _ (edgeEquiv e).2]


theorem triHexBrick_pfdIndexedWeight_lumping
    {N m : Nat} (hNm : N < m) (p q : Real)
    (F : ConfigSpace (triHexBrickFullDualGraph m).edgeSet → Real) :
    (∑ eta : ConfigSpace (triHexPlanarFiniteStarPlanar m).G.edgeSet,
      indexedBernoulliWeight p eta *
        (F (pfdIndexedSupportActive
          (triHexPlanarFiniteStarPlanar m) eta) *
          q ^ numClustersBC (triHexBrickFullDualGraph m) ⊥
            (extendActive (triHexBrickFullDualGraph m)
              (pfdIndexedSupportActive
                (triHexPlanarFiniteStarPlanar m) eta)))) =
    ∑ rho : ConfigSpace (triHexBrickFullDualGraph m).edgeSet,
      F rho * activeBCWeight (triHexBrickFullDualGraph m) ⊥
        (triHexBrickDualLumpedParam N m p) q rho := by
  have h := sum_indexedBernoulliWeight_restrictActive_bundleSupport
    (triHexBrickFullDualGraph m) p
    (kwg_dualEnds (triHexPlanarFiniteStarPlanar m))
    (fun rho => F rho * q ^ numClustersBC
      (triHexBrickFullDualGraph m) ⊥
        (extendActive (triHexBrickFullDualGraph m) rho))
  change (∑ eta : ConfigSpace (triHexPlanarFiniteStarPlanar m).G.edgeSet,
      indexedBernoulliWeight p eta *
        (F (restrictActive (triHexBrickFullDualGraph m)
          (indexedBundleSupport
            (kwg_dualEnds (triHexPlanarFiniteStarPlanar m)) eta)) *
        q ^ numClustersBC (triHexBrickFullDualGraph m) ⊥
          (extendActive (triHexBrickFullDualGraph m)
            (restrictActive (triHexBrickFullDualGraph m)
              (indexedBundleSupport
                (kwg_dualEnds (triHexPlanarFiniteStarPlanar m)) eta))))) = _
  rw [h]
  apply Finset.sum_congr rfl
  intro rho _
  rw [activeBCWeight,
    triHexBrick_edgeProductW_lumpedParam_extendActive hNm]
  ring


def triHexBrickPfdSupport (m : Nat)
    (omega : ConfigSpace
      (Sym2 (triHexPlanarFiniteStarPlanar m).V)) :
    ConfigSpace (triHexBrickFullDualGraph m).edgeSet :=
  pfdIndexedSupportActive (triHexPlanarFiniteStarPlanar m)
    (pfdEdgeComplement (triHexPlanarFiniteStarPlanar m)
      (restrictActive (triHexPlanarFiniteStarPlanar m).G omega))

private theorem triHexBrick_pfdDualWeight_openSub_eq_of_edges
    (P : PlanarZ2Subgraph) (p q : Real)
    (omega eta : ConfigSpace (Sym2 P.V))
    (h : ∀ e ∈ P.G.edgeFinset, omega e = eta e) :
    pfdDualWeight P p q (openSub P.G omega) =
      pfdDualWeight P p q (openSub P.G eta) := by
  rw [ecz_openSub_eq_of_edges P.G omega eta h]

private theorem triHexBrickPfdWeight_activeSplit
    (m : Nat) (p q : Real)
    (eta : ConfigSpace (triHexPlanarFiniteStarPlanar m).G.edgeSet)
    (xi : ConfigSpace
      {e : Sym2 (triHexPlanarFiniteStarPlanar m).V //
        e ∉ (triHexPlanarFiniteStarPlanar m).G.edgeSet}) :
    pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
        (openSub (triHexPlanarFiniteStarPlanar m).G
          ((activeSplitEquiv (triHexPlanarFiniteStarPlanar m).G).symm
            (eta, xi))) =
      pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
        (openSub (triHexPlanarFiniteStarPlanar m).G
          (extendActive (triHexPlanarFiniteStarPlanar m).G eta)) := by
  apply triHexBrick_pfdDualWeight_openSub_eq_of_edges
  intro e he
  have heSet : e ∈ (triHexPlanarFiniteStarPlanar m).G.edgeSet := by
    simpa only [SimpleGraph.mem_edgeFinset] using he
  have hsplit := congrFun
    (restrictActive_activeSplitEquiv_symm
      (triHexPlanarFiniteStarPlanar m).G eta xi) ⟨e, heSet⟩
  calc
    ((activeSplitEquiv (triHexPlanarFiniteStarPlanar m).G).symm
        (eta, xi)) e = eta ⟨e, heSet⟩ := hsplit
    _ = extendActive (triHexPlanarFiniteStarPlanar m).G eta e := by
      symm
      exact extendActive_apply
        (triHexPlanarFiniteStarPlanar m).G eta ⟨e, heSet⟩



theorem triHexBrick_pfdDualNumer_eq_lumped
    {N m : Nat} (hNm : N < m) (p q : Real)
    (F : ConfigSpace (triHexBrickFullDualGraph m).edgeSet → Real) :
    (∑ omega : ConfigSpace
        (Sym2 (triHexPlanarFiniteStarPlanar m).V),
      F (triHexBrickPfdSupport m omega) *
        pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
          (openSub (triHexPlanarFiniteStarPlanar m).G omega)) =
      2 ^ ecz_NE (triHexPlanarFiniteStarPlanar m).G *
        ∑ rho : ConfigSpace (triHexBrickFullDualGraph m).edgeSet,
          F rho * activeBCWeight (triHexBrickFullDualGraph m) ⊥
            (triHexBrickDualLumpedParam N m p) q rho := by
  rw [← Equiv.sum_comp
      (activeSplitEquiv (triHexPlanarFiniteStarPlanar m).G).symm,
    Fintype.sum_prod_type]
  have key : ∀ eta : ConfigSpace
      (triHexPlanarFiniteStarPlanar m).G.edgeSet,
      (∑ xi : ConfigSpace
          {e : Sym2 (triHexPlanarFiniteStarPlanar m).V //
            e ∉ (triHexPlanarFiniteStarPlanar m).G.edgeSet},
        F (triHexBrickPfdSupport m
          ((activeSplitEquiv (triHexPlanarFiniteStarPlanar m).G).symm
            (eta, xi))) *
        pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
          (openSub (triHexPlanarFiniteStarPlanar m).G
            ((activeSplitEquiv (triHexPlanarFiniteStarPlanar m).G).symm
              (eta, xi)))) =
        2 ^ ecz_NE (triHexPlanarFiniteStarPlanar m).G *
          (F (pfdIndexedSupportActive
              (triHexPlanarFiniteStarPlanar m)
              (pfdEdgeComplement
                (triHexPlanarFiniteStarPlanar m) eta)) *
            pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
              (openSub (triHexPlanarFiniteStarPlanar m).G
                (extendActive (triHexPlanarFiniteStarPlanar m).G eta))) := by
    intro eta
    rw [Finset.sum_congr rfl (fun xi _ => by
      simp only [triHexBrickPfdSupport]
      rw [restrictActive_activeSplitEquiv_symm,
        triHexBrickPfdWeight_activeSplit])]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      card_inactive_config (triHexPlanarFiniteStarPlanar m).G]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun eta _ => key eta), ← Finset.mul_sum]
  congr 1
  have hreindex :
      (∑ i : ConfigSpace (triHexPlanarFiniteStarPlanar m).G.edgeSet,
        F (pfdIndexedSupportActive (triHexPlanarFiniteStarPlanar m)
            (pfdEdgeComplement (triHexPlanarFiniteStarPlanar m) i)) *
          pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
            (openSub (triHexPlanarFiniteStarPlanar m).G
              (extendActive (triHexPlanarFiniteStarPlanar m).G i))) =
        ∑ eta : ConfigSpace (triHexPlanarFiniteStarPlanar m).G.edgeSet,
          F (pfdIndexedSupportActive
              (triHexPlanarFiniteStarPlanar m) eta) *
            pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
              (openSub (triHexPlanarFiniteStarPlanar m).G
                (extendActive (triHexPlanarFiniteStarPlanar m).G
                  (pfdEdgeComplement
                    (triHexPlanarFiniteStarPlanar m) eta))) := by
    let g := fun eta : ConfigSpace
        (triHexPlanarFiniteStarPlanar m).G.edgeSet =>
      F (pfdIndexedSupportActive (triHexPlanarFiniteStarPlanar m) eta) *
        pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
          (openSub (triHexPlanarFiniteStarPlanar m).G
            (extendActive (triHexPlanarFiniteStarPlanar m).G
              (pfdEdgeComplement
                (triHexPlanarFiniteStarPlanar m) eta)))
    simpa only [g, pfdEdgeComplement_involutive] using
      (Equiv.sum_comp
        (pfdEdgeComplement (triHexPlanarFiniteStarPlanar m)) g)
  have hpoint : ∀ eta : ConfigSpace
      (triHexPlanarFiniteStarPlanar m).G.edgeSet,
      pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
          (openSub (triHexPlanarFiniteStarPlanar m).G
            (extendActive (triHexPlanarFiniteStarPlanar m).G
              (pfdEdgeComplement
                (triHexPlanarFiniteStarPlanar m) eta))) =
        indexedBernoulliWeight p eta *
          q ^ numClustersBC (triHexBrickFullDualGraph m) ⊥
            (extendActive (triHexBrickFullDualGraph m)
              (pfdIndexedSupportActive
                (triHexPlanarFiniteStarPlanar m) eta)) := by
    intro eta
    change pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
        (openSub (triHexPlanarFiniteStarPlanar m).G
          (extendActive (triHexPlanarFiniteStarPlanar m).G
            (pfdEdgeComplement
              (triHexPlanarFiniteStarPlanar m) eta))) = _
    rw [pfdDualWeight_eq_indexedSupport]
    have hcomp :
        (fun e : kwg_Edge (triHexPlanarFiniteStarPlanar m) =>
          !(extendActive (triHexPlanarFiniteStarPlanar m).G
            (pfdEdgeComplement (triHexPlanarFiniteStarPlanar m) eta)
              e.1)) = eta := by
      funext e
      rw [extendActive_apply, pfdEdgeComplement_apply]
      simp
    rw [hcomp]
    unfold triHexBrickFullDualGraph
    rfl
  refine hreindex.trans ?_
  rw [Finset.sum_congr rfl (fun eta _ => by rw [hpoint eta])]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    triHexBrick_pfdIndexedWeight_lumping hNm p q F


theorem triHexBrick_pfdDualZ_eq_lumped
    {N m : Nat} (hNm : N < m) (p q : Real) :
    pfdDualZ (triHexPlanarFiniteStarPlanar m) p q =
      2 ^ ecz_NE (triHexPlanarFiniteStarPlanar m).G *
        activeBCZ (triHexBrickFullDualGraph m) ⊥
          (triHexBrickDualLumpedParam N m p) q := by
  unfold pfdDualZ activeBCZ
  simpa using triHexBrick_pfdDualNumer_eq_lumped
    hNm p q (fun _ => 1)



theorem triHexBrick_pfdDualMean_eq_lumped
    {N m : Nat} (hNm : N < m) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : ConfigSpace (triHexBrickFullDualGraph m).edgeSet → Real) :
    (∑ omega : ConfigSpace
        (Sym2 (triHexPlanarFiniteStarPlanar m).V),
      F (triHexBrickPfdSupport m omega) *
        pfdDualProb (triHexPlanarFiniteStarPlanar m) p q omega) =
      ∑ rho : ConfigSpace (triHexBrickFullDualGraph m).edgeSet,
        F rho * activeBCProb (triHexBrickFullDualGraph m) ⊥
          (triHexBrickDualLumpedParam N m p) q rho := by
  unfold pfdDualProb activeBCProb
  change
    (∑ omega : ConfigSpace
        (Sym2 (triHexPlanarFiniteStarPlanar m).V),
      F (triHexBrickPfdSupport m omega) *
        (pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
          (openSub (triHexPlanarFiniteStarPlanar m).G omega) /
            pfdDualZ (triHexPlanarFiniteStarPlanar m) p q)) =
      ∑ rho : ConfigSpace (triHexBrickFullDualGraph m).edgeSet,
        F rho * (activeBCWeight (triHexBrickFullDualGraph m) ⊥
          (triHexBrickDualLumpedParam N m p) q rho /
            activeBCZ (triHexBrickFullDualGraph m) ⊥
              (triHexBrickDualLumpedParam N m p) q)
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, ← Finset.sum_div,
    triHexBrick_pfdDualNumer_eq_lumped hNm,
    triHexBrick_pfdDualZ_eq_lumped hNm]
  have htwo : (2 : Real) ^
      ecz_NE (triHexPlanarFiniteStarPlanar m).G ≠ 0 := by positivity
  have hZ : activeBCZ (triHexBrickFullDualGraph m) ⊥
      (triHexBrickDualLumpedParam N m p) q ≠ 0 :=
    (activeBCZ_pos _ _
      (triHexBrickDualLumpedParam_pos hNm hp hp1)
      (triHexBrickDualLumpedParam_lt_one hNm hp hp1) hq).ne'
  field_simp

end

end StatMech.FK.PeriodicPlanar
