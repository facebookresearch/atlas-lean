/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBoundaryToggleMergeWinding
import Code.FrontierD.PermCycleQuotientWeightSum



open Equiv Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section



theorem fkRectBlackDart01_primalLabels
    (R : FKRectTorus) (v : R.medialTorus.Vertex) :
    s(fkRectMedialDartPrimalLabel R (fkMedialBlackDart0 v).1,
        fkRectMedialDartPrimalLabel R (fkMedialBlackDart1 v).1) =
      fkRectTorusIndexedEdge R (fkRectTorusMedialEdgeEquiv R v) := by
  let e := fkRectTorusMedialEdgeEquiv R v
  have hv : v = fkRectMedialVertexOfEdge R e :=
    ((fkRectTorusMedialEdgeEquiv R).symm_apply_apply v).symm
  rw [hv]
  rcases e with ⟨b, x, y⟩
  have hx : ¬ Even (1 + 2 * x.val) := by
    exact Nat.not_even_iff_odd.mpr ⟨x.val, by omega⟩
  cases b <;> by_cases hy : Even y.val <;>
    simp [fkMedialBlackDart0, fkMedialBlackDart1,
      fkRectMedialDartPrimalLabel, fkRectMedialWestPrimal,
      fkRectMedialEastPrimal, fkRectTorusIndexedEdge,
      fkRectClosedPairingAtEdge, fkMedialVertexParity, hy,
      hx, fkMedialCheckerColor, fkMedialSideVertical, Bool.toNat,
      Sym2.eq_swap]



theorem fkRectBlackDart01_primalLabels_reachable_of_open
    (R : FKRectTorus) (omega : R.Configuration)
    (v : R.medialTorus.Vertex)
    (hopen : omega (fkRectTorusMedialEdgeEquiv R v) = true) :
    (fkRectOpenGraph R omega).Reachable
      (fkRectMedialDartPrimalLabel R (fkMedialBlackDart0 v).1)
      (fkRectMedialDartPrimalLabel R (fkMedialBlackDart1 v).1) := by
  exact (show (fkRectOpenGraph R omega).Adj
      (fkRectMedialDartPrimalLabel R (fkMedialBlackDart0 v).1)
      (fkRectMedialDartPrimalLabel R (fkMedialBlackDart1 v).1) from
    ⟨fkRectTorusMedialEdgeEquiv R v, hopen,
      (fkRectBlackDart01_primalLabels R v).symm⟩).reachable



theorem fkRectBlackBoundaryWeight_dart0_add_dart1_eq_zero
    (R : FKRectTorus) (omega : R.Configuration)
    (v : R.medialTorus.Vertex) :
    fkRectBlackBoundaryWeight R
          (fkRectConfigurationToMedialPairing R omega)
          (fkMedialBlackDart0 v) +
        fkRectBlackBoundaryWeight R
          (fkRectConfigurationToMedialPairing R omega)
          (fkMedialBlackDart1 v) = 0 := by
  let F := fkRectOpenEdges R omega
  have homega : fkRectConfigurationOfEdges R F = omega :=
    fkRectConfigurationOfEdges_openEdges R omega
  let e := fkRectTorusMedialEdgeEquiv R v
  have hv : v = fkRectMedialVertexOfEdge R e :=
    ((fkRectTorusMedialEdgeEquiv R).symm_apply_apply v).symm
  rw [← homega, hv]
  by_cases heF : e ∈ F
  · let F0 := F.erase e
    have heF0 : e ∉ F0 := Finset.notMem_erase e F
    have hinsert : insert e F0 = F := Finset.insert_erase heF
    have hpair := fkRectBlackBoundaryWeight_toggle_pair_eq_zero
      R F0 e heF0
    rw [← fkRectConfigurationToMedialPairing_insert R F0 e heF0,
      hinsert] at hpair
    exact hpair
  · rw [fkRectBlackBoundaryWeight_closed_dart0_eq_zero R F e heF,
      fkRectBlackBoundaryWeight_closed_dart1_eq_zero R F e heF,
      zero_add]



theorem fkRectBlackBoundaryWeight_dart0_eq_zero_of_closed
    (R : FKRectTorus) (omega : R.Configuration)
    (v : R.medialTorus.Vertex)
    (hclosed : omega (fkRectTorusMedialEdgeEquiv R v) = false) :
    fkRectBlackBoundaryWeight R
        (fkRectConfigurationToMedialPairing R omega)
        (fkMedialBlackDart0 v) = 0 := by
  let F := fkRectOpenEdges R omega
  have homega : fkRectConfigurationOfEdges R F = omega :=
    fkRectConfigurationOfEdges_openEdges R omega
  let e := fkRectTorusMedialEdgeEquiv R v
  have hv : v = fkRectMedialVertexOfEdge R e :=
    ((fkRectTorusMedialEdgeEquiv R).symm_apply_apply v).symm
  have heF : e ∉ F := by
    intro he
    have hopen : fkRectConfigurationOfEdges R F e = true := by
      simp [fkRectConfigurationOfEdges, he]
    rw [homega, hclosed] at hopen
    contradiction
  rw [← homega, hv]
  exact fkRectBlackBoundaryWeight_closed_dart0_eq_zero R F e heF


theorem fkRectBlackBoundaryWeight_dart1_eq_zero_of_closed
    (R : FKRectTorus) (omega : R.Configuration)
    (v : R.medialTorus.Vertex)
    (hclosed : omega (fkRectTorusMedialEdgeEquiv R v) = false) :
    fkRectBlackBoundaryWeight R
        (fkRectConfigurationToMedialPairing R omega)
        (fkMedialBlackDart1 v) = 0 := by
  let F := fkRectOpenEdges R omega
  have homega : fkRectConfigurationOfEdges R F = omega :=
    fkRectConfigurationOfEdges_openEdges R omega
  let e := fkRectTorusMedialEdgeEquiv R v
  have hv : v = fkRectMedialVertexOfEdge R e :=
    ((fkRectTorusMedialEdgeEquiv R).symm_apply_apply v).symm
  have heF : e ∉ F := by
    intro he
    have hopen : fkRectConfigurationOfEdges R F e = true := by
      simp [fkRectConfigurationOfEdges, he]
    rw [homega, hclosed] at hopen
    contradiction
  rw [← homega, hv]
  exact fkRectBlackBoundaryWeight_closed_dart1_eq_zero R F e heF


abbrev FKRectConfigurationBlackBoundaryCycle
    (R : FKRectTorus) (omega : R.Configuration) :=
  StatMech.FrontierA.PermCycleClass
    (fkMedialBlackBoundaryPerm
      (fkRectConfigurationToMedialPairing R omega))




def fkRectBlackBoundaryCycleInPrimalCluster
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) :
    FKRectConfigurationBlackBoundaryCycle R omega → Prop := by
  classical
  apply Quot.lift (fun d : FKMedialBlackDart R.medialTorus =>
    (fkRectOpenGraph R omega).Reachable x
      (fkRectMedialDartPrimalLabel R d.1))
  intro d e hde
  apply propext
  have hmedial :
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).Reachable d.1 e.1 :=
    (fkMedial_blackBoundary_sameCycle_iff_reachable
      (fkRectConfigurationToMedialPairing R omega) d e).mp hde
  have hprimal := fkRectMedial_reachable_primalLabel_reachable
    R omega hmedial
  exact ⟨fun h => h.trans hprimal, fun h => h.trans hprimal.symm⟩

@[simp] theorem fkRectBlackBoundaryCycleInPrimalCluster_mk
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectBlackBoundaryCycleInPrimalCluster R omega x (Quot.mk _ d) ↔
      (fkRectOpenGraph R omega).Reachable x
        (fkRectMedialDartPrimalLabel R d.1) :=
  Iff.rfl


def fkRectBlackBoundaryCycleWinding
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectConfigurationBlackBoundaryCycle R omega) : Int × Int :=
  permCycleQuotientWeightSum
    (fkMedialBlackBoundaryPerm
      (fkRectConfigurationToMedialPairing R omega)) C
    (fkRectBlackBoundaryWeight R
      (fkRectConfigurationToMedialPairing R omega))

@[simp] theorem fkRectBlackBoundaryCycleWinding_mk
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectBlackBoundaryCycleWinding R omega (Quot.mk _ d) =
      fkRectBlackBoundaryCycleClassWinding R
        (fkRectConfigurationToMedialPairing R omega) d := by
  exact permCycleQuotientWeightSum_mk _ _ _



def fkRectPrimalClusterBoundaryCycleWindingSum
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) : Int × Int := by
  classical
  exact ∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
    if fkRectBlackBoundaryCycleInPrimalCluster R omega x C then
      fkRectBlackBoundaryCycleWinding R omega C
    else 0




def fkRectPrimalClusterBoundaryWeightSum
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) : Int × Int :=
  ∑ d : FKMedialBlackDart R.medialTorus,
    if (fkRectOpenGraph R omega).Reachable x
        (fkRectMedialDartPrimalLabel R d.1) then
      fkRectBlackBoundaryWeight R
        (fkRectConfigurationToMedialPairing R omega) d
    else 0



theorem fkRectPrimalClusterBoundaryCycleWindingSum_eq_weightSum
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) :
    fkRectPrimalClusterBoundaryCycleWindingSum R omega x =
      fkRectPrimalClusterBoundaryWeightSum R omega x := by
  classical
  let sigma := fkMedialBlackBoundaryPerm
    (fkRectConfigurationToMedialPairing R omega)
  let p : FKMedialBlackDart R.medialTorus → Prop := fun d =>
    (fkRectOpenGraph R omega).Reachable x
      (fkRectMedialDartPrimalLabel R d.1)
  let f : FKMedialBlackDart R.medialTorus → Int × Int :=
    fkRectBlackBoundaryWeight R
      (fkRectConfigurationToMedialPairing R omega)
  have hinv : ∀ d e, sigma.SameCycle d e → (p d ↔ p e) := by
    intro d e hde
    have hmedial :
        (fkMedialLoopGraph R.medialTorus
          (fkRectConfigurationToMedialPairing R omega)).Reachable d.1 e.1 :=
      (fkMedial_blackBoundary_sameCycle_iff_reachable
        (fkRectConfigurationToMedialPairing R omega) d e).mp hde
    have hprimal := fkRectMedial_reachable_primalLabel_reachable
      R omega hmedial
    exact ⟨fun h => h.trans hprimal, fun h => h.trans hprimal.symm⟩
  unfold fkRectPrimalClusterBoundaryCycleWindingSum
  rw [show (∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
        if fkRectBlackBoundaryCycleInPrimalCluster R omega x C then
          fkRectBlackBoundaryCycleWinding R omega C else 0) =
      ∑ C : StatMech.FrontierA.PermCycleClass sigma,
        permCycleQuotientWeightSum sigma C
          (fun d => if p d then f d else 0) by
    apply Finset.sum_congr rfl
    intro C _
    induction C using Quot.ind with
    | _ d =>
      simp only [fkRectBlackBoundaryCycleInPrimalCluster_mk,
        fkRectBlackBoundaryCycleWinding_mk]
      change (if p d then permCycleClassWeightSum sigma d f else 0) =
        permCycleQuotientWeightSum sigma (Quot.mk _ d)
          (fun e => if p e then f e else 0)
      rw [permCycleQuotientWeightSum_mk,
        permCycleClassWeightSum_filter_of_sameCycle_invariant
          sigma p f hinv d]
  ]
  rw [sum_permCycleQuotientWeightSum]
  rfl




theorem fkRectPrimalClusterBoundaryWeightSum_eq_zero
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) :
    fkRectPrimalClusterBoundaryWeightSum R omega x = 0 := by
  let f : FKMedialBlackDart R.medialTorus → Int × Int := fun d =>
    if (fkRectOpenGraph R omega).Reachable x
        (fkRectMedialDartPrimalLabel R d.1) then
      fkRectBlackBoundaryWeight R
        (fkRectConfigurationToMedialPairing R omega) d
    else 0
  let g : R.medialTorus.Vertex × Bool → Int × Int := fun vb =>
    f ((fkMedialBlackDartEquivVertexBool R.medialTorus).symm vb)
  have hequiv : (∑ d : FKMedialBlackDart R.medialTorus, f d) =
      ∑ vb : R.medialTorus.Vertex × Bool, g vb := by
    apply Fintype.sum_equiv
      (fkMedialBlackDartEquivVertexBool R.medialTorus)
    intro d
    change f d = g ((fkMedialBlackDartEquivVertexBool R.medialTorus) d)
    unfold g
    rw [(fkMedialBlackDartEquivVertexBool
      R.medialTorus).symm_apply_apply]
  have hprod : (∑ vb : R.medialTorus.Vertex × Bool, g vb) =
      ∑ v : R.medialTorus.Vertex, ∑ b : Bool, g (v, b) :=
    Fintype.sum_prod_type g
  unfold fkRectPrimalClusterBoundaryWeightSum
  change (∑ d : FKMedialBlackDart R.medialTorus, f d) = 0
  rw [hequiv, hprod]
  apply Finset.sum_eq_zero
  intro v _
  rw [Fintype.sum_bool]
  simp [g, f, fkMedialBlackDartEquivVertexBool]
  change (if (fkRectOpenGraph R omega).Reachable x
        (fkRectMedialDartPrimalLabel R (fkMedialBlackDart1 v).1) then
      fkRectBlackBoundaryWeight R
        (fkRectConfigurationToMedialPairing R omega)
        (fkMedialBlackDart1 v)
    else 0) +
    (if (fkRectOpenGraph R omega).Reachable x
        (fkRectMedialDartPrimalLabel R (fkMedialBlackDart0 v).1) then
      fkRectBlackBoundaryWeight R
        (fkRectConfigurationToMedialPairing R omega)
        (fkMedialBlackDart0 v)
    else 0) = 0
  by_cases hopen : omega (fkRectTorusMedialEdgeEquiv R v) = true
  · have h01 := fkRectBlackDart01_primalLabels_reachable_of_open
      R omega v hopen
    have hiff : (fkRectOpenGraph R omega).Reachable x
          (fkRectMedialDartPrimalLabel R (fkMedialBlackDart0 v).1) ↔
        (fkRectOpenGraph R omega).Reachable x
          (fkRectMedialDartPrimalLabel R (fkMedialBlackDart1 v).1) :=
      ⟨fun h => h.trans h01, fun h => h.trans h01.symm⟩
    by_cases h0 : (fkRectOpenGraph R omega).Reachable x
        (fkRectMedialDartPrimalLabel R (fkMedialBlackDart0 v).1)
    · rw [if_pos h0, if_pos (hiff.mp h0)]
      simpa [add_comm] using
        fkRectBlackBoundaryWeight_dart0_add_dart1_eq_zero R omega v
    · rw [if_neg h0, if_neg (mt hiff.mpr h0), zero_add]
  · have hclosed : omega (fkRectTorusMedialEdgeEquiv R v) = false := by
      cases h : omega (fkRectTorusMedialEdgeEquiv R v)
      · rfl
      · exact absurd h hopen
    rw [fkRectBlackBoundaryWeight_dart0_eq_zero_of_closed R omega v hclosed,
      fkRectBlackBoundaryWeight_dart1_eq_zero_of_closed R omega v hclosed]
    simp



theorem fkRectPrimalClusterBoundaryCycleWindingSum_eq_zero
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) :
    fkRectPrimalClusterBoundaryCycleWindingSum R omega x = 0 := by
  rw [fkRectPrimalClusterBoundaryCycleWindingSum_eq_weightSum,
    fkRectPrimalClusterBoundaryWeightSum_eq_zero]



def fkRectPrimalClusterNonzeroBoundaryCycles
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) :
    Finset (FKRectConfigurationBlackBoundaryCycle R omega) := by
  classical
  exact Finset.univ.filter fun C =>
    fkRectBlackBoundaryCycleInPrimalCluster R omega x C ∧
      fkRectBlackBoundaryCycleWinding R omega C ≠ 0

set_option maxHeartbeats 800000 in





theorem fkRectBlackBoundaryCycle_eq_of_card_nonzero_le_two_of_fst_mul_pos
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex)
    (hcard : (fkRectPrimalClusterNonzeroBoundaryCycles R omega x).card ≤ 2)
    {C D : FKRectConfigurationBlackBoundaryCycle R omega}
    (hC : fkRectBlackBoundaryCycleInPrimalCluster R omega x C)
    (hD : fkRectBlackBoundaryCycleInPrimalCluster R omega x D)
    (hsign : 0 < (fkRectBlackBoundaryCycleWinding R omega C).1 *
      (fkRectBlackBoundaryCycleWinding R omega D).1) :
    C = D := by
  classical
  apply eq_of_sum_ite_eq_zero_of_card_nonzero_le_two_of_fst_mul_pos
    (fun A : FKRectConfigurationBlackBoundaryCycle R omega =>
      fkRectBlackBoundaryCycleInPrimalCluster R omega x A)
    (fkRectBlackBoundaryCycleWinding R omega)
    (fkRectPrimalClusterBoundaryCycleWindingSum_eq_zero R omega x)
    (by simpa [fkRectPrimalClusterNonzeroBoundaryCycles] using hcard)
    hC hD hsign

end

end StatMech.FrontierD
