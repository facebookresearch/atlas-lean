/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRandomClusterGraphBridge
import Code.FK.PositiveAssociation










open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section

open StatMech

local instance fkRectTorusGraphDecidableRel (R : FKRectTorus) :
    DecidableRel (fkRectTorusGraph R).Adj := Classical.decRel _



def fkRectGraphConfigurationExtend (R : FKRectTorus)
    (eta : FKRectGraphConfiguration R) :
    ConfigSpace (Sym2 R.Vertex) := fun e =>
  if he : e ∈ (fkRectTorusGraph R).edgeSet then eta ⟨e, he⟩ else false

@[simp] theorem fkRectGraphConfigurationExtend_edge
    (R : FKRectTorus) (eta : FKRectGraphConfiguration R)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    fkRectGraphConfigurationExtend R eta e.1 = eta e := by
  simp [fkRectGraphConfigurationExtend, e.2]



theorem fk_openSub_configurationExtend
    (R : FKRectTorus) (eta : FKRectGraphConfiguration R) :
    FK.openSub (fkRectTorusGraph R)
        (fkRectGraphConfigurationExtend R eta) =
      fkRectGraphOpenGraph R eta := by
  ext x y
  constructor
  · rintro ⟨hxy, hopen⟩
    have he : s(x, y) ∈ (fkRectTorusGraph R).edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      exact hxy
    refine ⟨⟨s(x, y), he⟩, ?_, rfl⟩
    simpa [fkRectGraphConfigurationExtend, he] using hopen
  · rintro ⟨e, hopen, hexy⟩
    have hedge : (fkRectTorusGraph R).Adj x y := by
      have he := e.2
      rw [hexy, SimpleGraph.mem_edgeSet] at he
      exact he
    refine ⟨hedge, ?_⟩
    rw [fkRectGraphConfigurationExtend]
    simp only [hedge, SimpleGraph.mem_edgeSet, dite_true]
    have hsub : (⟨s(x, y), by
        rwa [SimpleGraph.mem_edgeSet]⟩ :
          {e // e ∈ (fkRectTorusGraph R).edgeSet}) = e := by
      apply Subtype.ext
      exact hexy.symm
    simpa [hsub] using hopen


theorem fk_numClusters_configurationExtend
    (R : FKRectTorus) (eta : FKRectGraphConfiguration R) :
    FK.numClusters (fkRectTorusGraph R)
        (fkRectGraphConfigurationExtend R eta) =
      Fintype.card (fkRectGraphOpenGraph R eta).ConnectedComponent := by
  unfold FK.numClusters
  simpa only [← Nat.card_eq_fintype_card] using congrArg
    (fun G : SimpleGraph R.Vertex => Nat.card G.ConnectedComponent)
    (fk_openSub_configurationExtend R eta)



theorem fk_edgeProduct_configurationExtend
    (R : FKRectTorus) (p : Real) (eta : FKRectGraphConfiguration R) :
    FK.edgeProduct (fkRectTorusGraph R) p
        (fkRectGraphConfigurationExtend R eta) =
      ∏ e : {e // e ∈ (fkRectTorusGraph R).edgeSet},
        if eta e then p else 1 - p := by
  unfold FK.edgeProduct
  let edgeEquiv :
      {e // e ∈ (fkRectTorusGraph R).edgeFinset} ≃
        {e // e ∈ (fkRectTorusGraph R).edgeSet} :=
    Equiv.subtypeEquiv (Equiv.refl _) fun e =>
      SimpleGraph.mem_edgeFinset
  calc
    (∏ e ∈ (fkRectTorusGraph R).edgeFinset,
        if fkRectGraphConfigurationExtend R eta e then p else 1 - p) =
        ∏ e : {e // e ∈ (fkRectTorusGraph R).edgeFinset},
          if fkRectGraphConfigurationExtend R eta e.1 then p else 1 - p := by
      rw [← Finset.prod_attach, Finset.attach_eq_univ]
    _ = ∏ e : {e // e ∈ (fkRectTorusGraph R).edgeSet},
          if eta e then p else 1 - p := by
      apply Fintype.prod_equiv edgeEquiv
      intro e
      have heSet : e.1 ∈ (fkRectTorusGraph R).edgeSet :=
        SimpleGraph.mem_edgeFinset.mp e.2
      have hext : fkRectGraphConfigurationExtend R eta e.1 =
          eta (edgeEquiv e) := by
        unfold fkRectGraphConfigurationExtend
        rw [dif_pos heSet]
        congr 1
      rw [hext]



theorem fk_edgeProduct_configurationGraphEquiv
    (R : FKRectTorus) (p : Real) (omega : R.Configuration) :
    FK.edgeProduct (fkRectTorusGraph R) p
        (fkRectGraphConfigurationExtend R
          (fkRectConfigurationGraphEquiv R omega)) =
      fkRectEdgeProduct R p omega := by
  rw [fk_edgeProduct_configurationExtend]
  unfold fkRectEdgeProduct
  symm
  apply Fintype.prod_equiv (fkRectEdgeGraphEquiv R)
      (fun a => if omega a then p else 1 - p)
      (fun e => if fkRectConfigurationGraphEquiv R omega e then p else 1 - p)
  intro a
  rw [fkRectConfigurationGraphEquiv_apply_edge]



theorem fkWeight_configurationGraphEquiv
    (R : FKRectTorus) (p q : Real) (omega : R.Configuration) :
    FK.fkWeight (fkRectTorusGraph R) p q
        (fkRectGraphConfigurationExtend R
          (fkRectConfigurationGraphEquiv R omega)) =
      fkRectRandomClusterWeight R p q omega := by
  unfold FK.fkWeight fkRectRandomClusterWeight
  rw [fk_edgeProduct_configurationGraphEquiv,
    fk_numClusters_configurationExtend,
    fkRectGraph_clusterCount_configurationGraphEquiv]

@[simp] theorem fkRectGraphConfigurationExtend_sup
    (R : FKRectTorus) (eta zeta : FKRectGraphConfiguration R) :
    fkRectGraphConfigurationExtend R (eta ⊔ zeta) =
      fkRectGraphConfigurationExtend R eta ⊔
        fkRectGraphConfigurationExtend R zeta := by
  funext e
  by_cases he : e ∈ (fkRectTorusGraph R).edgeSet <;>
    simp [fkRectGraphConfigurationExtend, he]

@[simp] theorem fkRectGraphConfigurationExtend_inf
    (R : FKRectTorus) (eta zeta : FKRectGraphConfiguration R) :
    fkRectGraphConfigurationExtend R (eta ⊓ zeta) =
      fkRectGraphConfigurationExtend R eta ⊓
        fkRectGraphConfigurationExtend R zeta := by
  funext e
  by_cases he : e ∈ (fkRectTorusGraph R).edgeSet <;>
    simp [fkRectGraphConfigurationExtend, he]


def fkRectCriticalEdgeFactor (R : FKRectTorus) (q : Real) : Real :=
  (1 / (1 + Real.sqrt q)) ^ (2 * R.width * R.height)

theorem fkRectCriticalEdgeFactor_pos (R : FKRectTorus)
    {q : Real} (hq : 0 < q) :
    0 < fkRectCriticalEdgeFactor R q := by
  unfold fkRectCriticalEdgeFactor
  positivity



theorem fkWeight_configurationExtend_critical
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (eta : FKRectGraphConfiguration R) :
    FK.fkWeight (fkRectTorusGraph R) (fkRectCriticalP q) q
        (fkRectGraphConfigurationExtend R eta) =
      fkRectCriticalEdgeFactor R q *
        fkRectGraphCriticalReducedWeight R q eta := by
  let omega := (fkRectConfigurationGraphEquiv R).symm eta
  have hweight := fkWeight_configurationGraphEquiv R
    (fkRectCriticalP q) q omega
  have hcritical := fkRectRandomClusterWeight_critical_eq R hq omega
  rw [hcritical] at hweight
  rw [← fkRectGraphCriticalReducedWeight_configurationGraphEquiv
    R q omega] at hweight
  rw [show fkRectConfigurationGraphEquiv R omega = eta by
    exact (fkRectConfigurationGraphEquiv R).apply_symm_apply eta] at hweight
  simpa [fkRectCriticalEdgeFactor] using hweight


theorem fkRectGraphCriticalReducedWeight_logSupermodular
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (eta zeta : FKRectGraphConfiguration R) :
    fkRectGraphCriticalReducedWeight R q eta *
        fkRectGraphCriticalReducedWeight R q zeta ≤
      fkRectGraphCriticalReducedWeight R q (eta ⊔ zeta) *
        fkRectGraphCriticalReducedWeight R q (eta ⊓ zeta) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp := fkRectCriticalP_pos hq0
  have hp1 := fkRectCriticalP_lt_one hq0
  have hraw := FK.fkWeight_logSupermodular (fkRectTorusGraph R)
    hp hp1 hq
    (fkRectGraphConfigurationExtend R eta)
    (fkRectGraphConfigurationExtend R zeta)
  rw [← fkRectGraphConfigurationExtend_sup,
    ← fkRectGraphConfigurationExtend_inf] at hraw
  simp_rw [fkWeight_configurationExtend_critical R hq0] at hraw
  have hfactor : 0 < fkRectCriticalEdgeFactor R q :=
    fkRectCriticalEdgeFactor_pos R hq0
  nlinarith [sq_pos_of_pos hfactor]

theorem fkRectGraphCriticalReducedWeight_pos
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (eta : FKRectGraphConfiguration R) :
    0 < fkRectGraphCriticalReducedWeight R q eta := by
  unfold fkRectGraphCriticalReducedWeight
  exact mul_pos (pow_pos (Real.sqrt_pos.2 hq) _) (pow_pos hq _)

theorem fkRectGraphCriticalReducedZ_pos
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    0 < fkRectGraphCriticalReducedZ R q := by
  rw [fkRectGraphCriticalReducedZ_eq]
  exact fkRectCriticalReducedZ_pos R hq

theorem fkRectGraphCriticalRandomClusterProb_nonneg
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (eta : FKRectGraphConfiguration R) :
    0 ≤ fkRectGraphCriticalRandomClusterProb R q eta :=
  (div_pos (fkRectGraphCriticalReducedWeight_pos R hq eta)
    (fkRectGraphCriticalReducedZ_pos R hq)).le

theorem sum_fkRectGraphCriticalRandomClusterProb
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    ∑ eta : FKRectGraphConfiguration R,
      fkRectGraphCriticalRandomClusterProb R q eta = 1 := by
  calc
    (∑ eta : FKRectGraphConfiguration R,
        fkRectGraphCriticalRandomClusterProb R q eta) =
        ∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega := by
      symm
      apply Fintype.sum_equiv (fkRectConfigurationGraphEquiv R)
      intro omega
      exact
        (fkRectGraphCriticalRandomClusterProb_configurationGraphEquiv
          R q omega).symm
    _ = 1 := sum_fkRectCriticalRandomClusterProb R hq

@[simp] theorem fkRectConfigurationGraphEquiv_inf
    (R : FKRectTorus) (omega tau : R.Configuration) :
    fkRectConfigurationGraphEquiv R (omega ⊓ tau) =
      fkRectConfigurationGraphEquiv R omega ⊓
        fkRectConfigurationGraphEquiv R tau := by
  funext e
  rfl

@[simp] theorem fkRectConfigurationGraphEquiv_sup
    (R : FKRectTorus) (omega tau : R.Configuration) :
    fkRectConfigurationGraphEquiv R (omega ⊔ tau) =
      fkRectConfigurationGraphEquiv R omega ⊔
        fkRectConfigurationGraphEquiv R tau := by
  funext e
  rfl


theorem fkRectGraphCriticalRandomClusterProb_fkgLattice
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (eta zeta : FKRectGraphConfiguration R) :
    fkRectGraphCriticalRandomClusterProb R q eta *
        fkRectGraphCriticalRandomClusterProb R q zeta ≤
      fkRectGraphCriticalRandomClusterProb R q (eta ⊓ zeta) *
        fkRectGraphCriticalRandomClusterProb R q (eta ⊔ zeta) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hZ : 0 < fkRectGraphCriticalReducedZ R q :=
    fkRectGraphCriticalReducedZ_pos R hq0
  unfold fkRectGraphCriticalRandomClusterProb
  rw [div_mul_div_comm, div_mul_div_comm]
  apply (div_le_div_iff_of_pos_right (mul_pos hZ hZ)).2
  simpa [mul_comm] using
    fkRectGraphCriticalReducedWeight_logSupermodular R hq eta zeta



theorem fkRectCriticalRandomClusterProb_fkgLattice
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (omega tau : R.Configuration) :
    fkRectCriticalRandomClusterProb R q omega *
        fkRectCriticalRandomClusterProb R q tau ≤
      fkRectCriticalRandomClusterProb R q (omega ⊓ tau) *
        fkRectCriticalRandomClusterProb R q (omega ⊔ tau) := by
  simpa only [
      ← fkRectGraphCriticalRandomClusterProb_configurationGraphEquiv,
      fkRectConfigurationGraphEquiv_inf,
      fkRectConfigurationGraphEquiv_sup] using
    fkRectGraphCriticalRandomClusterProb_fkgLattice R hq
      (fkRectConfigurationGraphEquiv R omega)
      (fkRectConfigurationGraphEquiv R tau)


theorem fkRectGraphCritical_positivelyAssociated
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    {f g : FKRectGraphConfiguration R → Real}
    (hf : Monotone f) (hg : Monotone g) :
    (∑ eta, fkRectGraphCriticalRandomClusterProb R q eta * f eta) *
        (∑ eta, fkRectGraphCriticalRandomClusterProb R q eta * g eta) ≤
      ∑ eta, fkRectGraphCriticalRandomClusterProb R q eta *
        (f eta * g eta) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact Probability.fkg_inequality
    (fun eta => fkRectGraphCriticalRandomClusterProb_nonneg R hq0 eta)
    (sum_fkRectGraphCriticalRandomClusterProb R hq0)
    (fkRectGraphCriticalRandomClusterProb_fkgLattice R hq) hf hg


theorem fkRectCritical_positivelyAssociated
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    {f g : R.Configuration → Real}
    (hf : Monotone f) (hg : Monotone g) :
    (∑ omega, fkRectCriticalRandomClusterProb R q omega * f omega) *
        (∑ omega, fkRectCriticalRandomClusterProb R q omega * g omega) ≤
      ∑ omega, fkRectCriticalRandomClusterProb R q omega *
        (f omega * g omega) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact Probability.fkg_inequality
    (fkRectCriticalRandomClusterProb_nonneg R hq0)
    (sum_fkRectCriticalRandomClusterProb R hq0)
    (fkRectCriticalRandomClusterProb_fkgLattice R hq) hf hg

end

end StatMech.FrontierD
