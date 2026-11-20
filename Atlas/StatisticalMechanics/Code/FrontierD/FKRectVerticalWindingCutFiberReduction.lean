/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectVerticalWindingPositiveBoundary
import Code.FrontierD.FKRectHorizontalCylinderCrossings
import Code.FrontierD.FKRectEssentialClusterBoundary










open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section


theorem fkRectOpenGraph_forceHorizontalCutClosed_le
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega) ≤
      fkRectOpenGraph R omega := by
  apply fkRectOpenGraph_mono R
  intro e he
  by_cases hcut : e ∈ fkRectHorizontalCutEdges R
  · simp [fkRectForceHorizontalCutClosed, hcut] at he
  · simpa [fkRectForceHorizontalCutClosed, hcut] using he


noncomputable def fkRectBlackBoundaryCyclePrimalComponent
    (R : FKRectTorus) (omega : R.Configuration) :
    FKRectConfigurationBlackBoundaryCycle R omega →
      (fkRectOpenGraph R omega).ConnectedComponent := by
  classical
  apply Quot.lift (fun d : FKMedialBlackDart R.medialTorus =>
    (fkRectOpenGraph R omega).connectedComponentMk
      (fkRectMedialDartPrimalLabel R d.1))
  intro d e hde
  apply ConnectedComponent.sound
  have hmedial :
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).Reachable d.1 e.1 :=
    (fkMedial_blackBoundary_sameCycle_iff_reachable
      (fkRectConfigurationToMedialPairing R omega) d e).mp hde
  exact fkRectMedial_reachable_primalLabel_reachable R omega hmedial

@[simp] theorem fkRectBlackBoundaryCyclePrimalComponent_mk
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectBlackBoundaryCyclePrimalComponent R omega (Quot.mk _ d) =
      (fkRectOpenGraph R omega).connectedComponentMk
        (fkRectMedialDartPrimalLabel R d.1) :=
  rfl



noncomputable def fkRectHorizontalCutComponentTorusComponent
    (R : FKRectTorus) (omega : R.Configuration)
    (X : (fkRectOpenGraph R
      (fkRectForceHorizontalCutClosed R omega)).ConnectedComponent) :
    (fkRectOpenGraph R omega).ConnectedComponent :=
  ConnectedComponent.map
    (SimpleGraph.Hom.ofLE
      (fkRectOpenGraph_forceHorizontalCutClosed_le R omega)) X

@[simp] theorem fkRectHorizontalCutComponentTorusComponent_mk
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) :
    fkRectHorizontalCutComponentTorusComponent R omega
        ((fkRectOpenGraph R
          (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk x) =
      (fkRectOpenGraph R omega).connectedComponentMk x :=
  ConnectedComponent.map_mk _ _



noncomputable def fkRectPrimalComponentBoundaryVerticalMass
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) : Nat := by
  classical
  exact ∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
    if fkRectBlackBoundaryCyclePrimalComponent R omega C = K then
      (fkRectBlackBoundaryCycleWinding R omega C).2.natAbs
    else 0



noncomputable def fkRectPrimalComponentHorizontalCutCrossingCount
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) : Nat := by
  classical
  let Crossing := {X : (fkRectOpenGraph R
      (fkRectForceHorizontalCutClosed R omega)).ConnectedComponent //
    FKRectHorizontalCutPrimalCrossingComponent R
      (fkRectForceHorizontalCutClosed R omega) X}
  exact ((Finset.univ : Finset Crossing).filter fun X =>
    fkRectHorizontalCutComponentTorusComponent R omega X.1 = K).card


theorem sum_fkRectPrimalComponentBoundaryVerticalMass
    (R : FKRectTorus) (omega : R.Configuration) :
    ∑ K : (fkRectOpenGraph R omega).ConnectedComponent,
        fkRectPrimalComponentBoundaryVerticalMass R omega K =
      ∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
        (fkRectBlackBoundaryCycleWinding R omega C).2.natAbs := by
  classical
  unfold fkRectPrimalComponentBoundaryVerticalMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  rw [Finset.sum_eq_single
    (fkRectBlackBoundaryCyclePrimalComponent R omega C)]
  · simp
  · intro K _ hne
    simp [Ne.symm hne]
  · simp



theorem sum_fkRectPrimalComponentHorizontalCutCrossingCount
    (R : FKRectTorus) (omega : R.Configuration) :
    ∑ K : (fkRectOpenGraph R omega).ConnectedComponent,
        fkRectPrimalComponentHorizontalCutCrossingCount R omega K =
      fkRectHorizontalCutPrimalCrossingClusterCount R
        (fkRectForceHorizontalCutClosed R omega) := by
  classical
  let Crossing := {X : (fkRectOpenGraph R
      (fkRectForceHorizontalCutClosed R omega)).ConnectedComponent //
    FKRectHorizontalCutPrimalCrossingComponent R
      (fkRectForceHorizontalCutClosed R omega) X}
  unfold fkRectPrimalComponentHorizontalCutCrossingCount
    fkRectHorizontalCutPrimalCrossingClusterCount
  change (∑ K : (fkRectOpenGraph R omega).ConnectedComponent,
      ((Finset.univ : Finset Crossing).filter fun X =>
        fkRectHorizontalCutComponentTorusComponent R omega X.1 = K).card) =
    Fintype.card Crossing
  simpa using (Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset Crossing)
    (Finset.univ : Finset
      (fkRectOpenGraph R omega).ConnectedComponent)
    (fun X : Crossing =>
      fkRectHorizontalCutComponentTorusComponent R omega X.1))



def FKRectVerticalBoundaryMassCutFiberBound
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  ∀ K : (fkRectOpenGraph R omega).ConnectedComponent,
    fkRectPrimalComponentBoundaryVerticalMass R omega K ≤
      2 * fkRectPrimalComponentHorizontalCutCrossingCount R omega K


theorem fkRectUnorientedVerticalWindingTotal_le_two_mul_horizontalCut_of_fiberBound
    (R : FKRectTorus) (omega : R.Configuration)
    (h : FKRectVerticalBoundaryMassCutFiberBound R omega) :
    fkRectUnorientedVerticalWindingTotal R omega ≤
      2 * fkRectHorizontalCutPrimalCrossingClusterCount R
        (fkRectForceHorizontalCutClosed R omega) := by
  rw [fkRectUnorientedVerticalWindingTotal,
    fkRectUnorientedVerticalWindingTotal_eq_sum_blackBoundaryCycle,
    ← sum_fkRectPrimalComponentBoundaryVerticalMass R omega]
  calc
    _ ≤ ∑ K : (fkRectOpenGraph R omega).ConnectedComponent,
        2 * fkRectPrimalComponentHorizontalCutCrossingCount R omega K := by
      exact Finset.sum_le_sum fun K _ => h K
    _ = 2 * ∑ K : (fkRectOpenGraph R omega).ConnectedComponent,
        fkRectPrimalComponentHorizontalCutCrossingCount R omega K := by
      rw [Finset.mul_sum]
    _ = _ := by
      rw [sum_fkRectPrimalComponentHorizontalCutCrossingCount]


theorem fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_fiberBound
    (R : FKRectTorus) (omega : R.Configuration)
    (h : FKRectVerticalBoundaryMassCutFiberBound R omega) :
    fkRectUnorientedVerticalWindingNumber R omega ≤
      fkRectHorizontalCutPrimalCrossingClusterCount R
        (fkRectForceHorizontalCutClosed R omega) := by
  have htotal :=
    fkRectUnorientedVerticalWindingTotal_le_two_mul_horizontalCut_of_fiberBound
      R omega h
  unfold fkRectUnorientedVerticalWindingNumber
  omega




noncomputable def fkRectPrimalComponentPositiveBoundaryVerticalMass
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) : Nat := by
  classical
  exact ∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
    if fkRectBlackBoundaryCyclePrimalComponent R omega C = K then
      (fkRectBlackBoundaryCycleWinding R omega C).2.toNat
    else 0



theorem sum_fkRectPrimalComponentPositiveBoundaryVerticalMass
    (R : FKRectTorus) (omega : R.Configuration) :
    ∑ K : (fkRectOpenGraph R omega).ConnectedComponent,
        fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K =
      fkRectPositiveVerticalBoundaryWindingTotal R omega := by
  classical
  unfold fkRectPrimalComponentPositiveBoundaryVerticalMass
    fkRectPositiveVerticalBoundaryWindingTotal
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  rw [Finset.sum_eq_single
    (fkRectBlackBoundaryCyclePrimalComponent R omega C)]
  · simp
  · intro K _ hne
    simp [Ne.symm hne]
  · simp


def FKRectPositiveVerticalBoundaryCutFiberBound
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  ∀ K : (fkRectOpenGraph R omega).ConnectedComponent,
    fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K ≤
      fkRectPrimalComponentHorizontalCutCrossingCount R omega K



theorem fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_positiveFiberBound
    (R : FKRectTorus) (omega : R.Configuration)
    (h : FKRectPositiveVerticalBoundaryCutFiberBound R omega) :
    fkRectUnorientedVerticalWindingNumber R omega ≤
      fkRectHorizontalCutPrimalCrossingClusterCount R
        (fkRectForceHorizontalCutClosed R omega) := by
  rw [fkRectUnorientedVerticalWindingNumber_eq_positiveBoundary,
    ← sum_fkRectPrimalComponentPositiveBoundaryVerticalMass R omega,
    ← sum_fkRectPrimalComponentHorizontalCutCrossingCount R omega]
  exact Finset.sum_le_sum fun K _ => h K


def FKRectPrimalComponentHasNet
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) : Prop :=
  ∃ p q : (fkRectOpenGraph R omega).Walk K.out K.out,
    FKRectWindingIndependent
      (fkRectWalkWinding R p) (fkRectWalkWinding R q)



theorem fkRectBlackBoundaryCycleWinding_eq_zero_of_componentHasNet
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    (hnet : FKRectPrimalComponentHasNet R omega K)
    (C : FKRectConfigurationBlackBoundaryCycle R omega)
    (hCK : fkRectBlackBoundaryCyclePrimalComponent R omega C = K) :
    fkRectBlackBoundaryCycleWinding R omega C = 0 := by
  induction C using Quot.ind with
  | _ d =>
    rcases hnet with ⟨p, q, hpq⟩
    let m := permOrbitVisitCount
      (fkMedialBoundaryStep
        (fkRectConfigurationToMedialPairing R omega)) d.1 d.1
    have hm : 0 < m := permOrbitVisitCount_self_pos _ _
    have hdp :=
      fkRect_boundaryOrbit_winding_dependent_of_openWalk_configuration
        R omega p d.1
    have hdq :=
      fkRect_boundaryOrbit_winding_dependent_of_openWalk_configuration
        R omega q d.1
    rw [fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle
      R omega d] at hdp hdq
    rw [fkRectBlackBoundaryCycleWinding_mk,
      ← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
    let c := fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)
    change c = 0
    let u := fkRectWalkWinding R p
    let v := fkRectWalkWinding R q
    change ¬ FKRectWindingIndependent (m • c) u at hdp
    change ¬ FKRectWindingIndependent (m • c) v at hdq
    change FKRectWindingIndependent u v at hpq
    unfold FKRectWindingIndependent at hdp hdq hpq
    push Not at hdp hdq
    simp only [Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul] at hdp hdq
    have hmInt : (m : Int) ≠ 0 := by exact_mod_cast hm.ne'
    have hcu : c.1 * u.2 - c.2 * u.1 = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hmInt
      calc
        (m : Int) * (c.1 * u.2 - c.2 * u.1) =
            (m : Int) * c.1 * u.2 - (m : Int) * c.2 * u.1 := by ring
        _ = 0 := hdp
    have hcv : c.1 * v.2 - c.2 * v.1 = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hmInt
      calc
        (m : Int) * (c.1 * v.2 - c.2 * v.1) =
            (m : Int) * c.1 * v.2 - (m : Int) * c.2 * v.1 := by ring
        _ = 0 := hdq
    have hc1mul : c.1 * (u.1 * v.2 - u.2 * v.1) = 0 := by
      calc
        c.1 * (u.1 * v.2 - u.2 * v.1) =
            u.1 * (c.1 * v.2 - c.2 * v.1) -
              v.1 * (c.1 * u.2 - c.2 * u.1) := by ring
        _ = 0 := by rw [hcu, hcv]; ring
    have hc2mul : c.2 * (u.1 * v.2 - u.2 * v.1) = 0 := by
      calc
        c.2 * (u.1 * v.2 - u.2 * v.1) =
            u.2 * (c.1 * v.2 - c.2 * v.1) -
              v.2 * (c.1 * u.2 - c.2 * u.1) := by ring
        _ = 0 := by rw [hcu, hcv]; ring
    have hc1 : c.1 = 0 :=
      (mul_eq_zero.mp hc1mul).resolve_right hpq
    have hc2 : c.2 = 0 :=
      (mul_eq_zero.mp hc2mul).resolve_right hpq
    exact Prod.ext hc1 hc2


theorem fkRectPrimalComponentPositiveBoundaryVerticalMass_eq_zero_of_hasNet
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    (hnet : FKRectPrimalComponentHasNet R omega K) :
    fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K = 0 := by
  classical
  unfold fkRectPrimalComponentPositiveBoundaryVerticalMass
  apply Finset.sum_eq_zero
  intro C _
  by_cases hCK : fkRectBlackBoundaryCyclePrimalComponent R omega C = K
  · rw [if_pos hCK,
      fkRectBlackBoundaryCycleWinding_eq_zero_of_componentHasNet
        R omega K hnet C hCK]
    rfl
  · rw [if_neg hCK]



theorem fkRectPositiveVerticalBoundaryCutFiberBound_of_componentHasNet
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    (hnet : FKRectPrimalComponentHasNet R omega K) :
    fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K ≤
      fkRectPrimalComponentHorizontalCutCrossingCount R omega K := by
  rw [fkRectPrimalComponentPositiveBoundaryVerticalMass_eq_zero_of_hasNet
    R omega K hnet]
  exact Nat.zero_le _

end

end StatMech.FrontierD
