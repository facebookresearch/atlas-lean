/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.GroupTheory.GroupExtension.SecondHomologySplitting
import MathlibExt.GroupTheory.GroupExtension.UniversalFunctoriality
import MathlibExt.AlgebraicTopology.SingularHomology.GroupHomologyTwo
import MathlibExt.KTheory.Ring.SteinbergPlusFiberPerfectness
import MathlibExt.KTheory.Ring.K2.SteinbergPlusFiberCentrality
import MathlibExt.KTheory.Ring.K2.StableSteinbergUniversalUniverses
import MathlibExt.KTheory.Ring.K2.KernelBridge
import MathlibExt.KTheory.Ring.Comparison.QuillenIndependentPlusHomotopyGroups
import MathlibExt.KTheory.Ring.Comparison.CanonicalOriginalScalarKiNaturality
import MathlibExt.KTheory.Exact.Quillen.ConnectiveKGroups.OriginalGroupDictionary

/-!
# The original Steinberg and Quillen second K-groups

The actual acyclic plus fiber has perfect ordinary fundamental group and
vanishing native second group homology. Its original central extension is
therefore universal. The unique original lifts between that extension and
the Steinberg extension are mutual inverses, on both total and kernel groups.

The resulting second-group equivalence retains the original connecting map
and categorical K₂ inclusion. The six-universe Quillen reader uses the actual
forward projection and inverse zero section of the independently constructed
plus comparison, together with its original carrier up and down maps.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w uR uM uObj uHom uNative uProbe uCarrier

attribute [local instance 1001] Nat.instNeZeroSucc

namespace AlgebraicKTheory

namespace StableGL

/-- The actual original plus-fiber extension is universal in independent target universes. -/
theorem independentPlusFiberExtension_isUniversalFor (R : Type u) [Ring R] :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    @GroupExtension.IsUniversalFor.{u, u, u, v, w}
      (HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R))
      (FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R))
      (StableE R)
      (HomotopyGroup.group (X := independentBGLCellTarget R)
        (x := independentBGLCellPoint R) (Fin 2))
      inferInstance inferInstance (independentPlusFiberExtension R) := by
  letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩
  letI : Group (HomotopyGroup.Pi 2 (independentBGLCellTarget R)
      (independentBGLCellPoint R)) :=
    HomotopyGroup.group (X := independentBGLCellTarget R)
      (x := independentBGLCellPoint R) (Fin 2)
  let S : GroupExtension
      (HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R))
      (FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R))
      (StableE R) := independentPlusFiberExtension R
  have hCentral : S.IsCentral := independentPlusFiberExtension_isCentral R
  let _ := independentPlusFiberFundamental_isPerfect R
  exact hCentral.isUniversalFor_of_isZero_secondHomology
    (TopCat.groupHomologyTwo_isZero_of_isAcyclicSpace (independentPlusFiber R)
      (independentPlusFiberPoint R) (independentPlusFiber_isAcyclic R))

/-- The original fixed-universe extension has its genuine universal property. -/
theorem independentPlusFiberExtension_isUniversal (R : Type u) [Ring R] :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    @GroupExtension.IsUniversal.{u, u, u}
      (HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R))
      (FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R))
      (StableE R)
      (HomotopyGroup.group (X := independentBGLCellTarget R)
        (x := independentBGLCellPoint R) (Fin 2))
      inferInstance inferInstance (independentPlusFiberExtension R) :=
  independentPlusFiberExtension_isUniversalFor R

end StableGL


namespace StableGL

/-- The canonical original extension morphism from the plus fiber to the Steinberg group. -/
def independentPlusFiberToSteinbergHom (R : Type u) [Ring R] :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (independentBGLCellTarget R)
        (independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := independentBGLCellTarget R)
        (x := independentBGLCellPoint R) (Fin 2);
    let S : GroupExtension
        (HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R))
        (FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R))
        (StableE R) := independentPlusFiberExtension R;
    S.Hom (StableSteinberg.steinbergExtension R) :=
  GroupExtension.IsUniversalFor.liftHom (independentPlusFiberExtension_isUniversalFor R)
    (StableSteinberg.steinbergExtension R) (StableSteinberg.steinbergExtension_isCentral R)
    (MonoidHom.id (StableE R))

/-- The canonical original reverse extension morphism from Steinberg to the plus fiber. -/
def independentSteinbergToPlusFiberHom (R : Type u) [Ring R] :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (independentBGLCellTarget R)
        (independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := independentBGLCellTarget R)
        (x := independentBGLCellPoint R) (Fin 2);
    let S : GroupExtension
        (HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R))
        (FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R))
        (StableE R) := independentPlusFiberExtension R;
    (StableSteinberg.steinbergExtension R).Hom S := by
  letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩
  letI : Group (HomotopyGroup.Pi 2 (independentBGLCellTarget R)
      (independentBGLCellPoint R)) :=
    HomotopyGroup.group (X := independentBGLCellTarget R)
      (x := independentBGLCellPoint R) (Fin 2)
  let S : GroupExtension
      (HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R))
      (FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R))
      (StableE R) := independentPlusFiberExtension R
  exact GroupExtension.IsUniversalFor.liftHom
    (StableSteinberg.steinbergExtension_isUniversalFor R)
    S (independentPlusFiberExtension_isCentral R) (MonoidHom.id (StableE R))

/-- The original extension round trip is the identity on the actual plus-fiber extension. -/
theorem independentSteinbergToPlusFiberHom_comp (R : Type u) [Ring R] :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (independentBGLCellTarget R)
        (independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := independentBGLCellTarget R)
        (x := independentBGLCellPoint R) (Fin 2);
    let S : GroupExtension
        (HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R))
        (FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R))
        (StableE R) := independentPlusFiberExtension R;
    (independentSteinbergToPlusFiberHom R).comp (independentPlusFiberToSteinbergHom R) =
      GroupExtension.Hom.id S := by
  letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩
  letI : Group (HomotopyGroup.Pi 2 (independentBGLCellTarget R)
      (independentBGLCellPoint R)) :=
    HomotopyGroup.group (X := independentBGLCellTarget R)
      (x := independentBGLCellPoint R) (Fin 2)
  let S : GroupExtension
      (HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R))
      (FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R))
      (StableE R) := independentPlusFiberExtension R
  let T : GroupExtension (StableSteinberg.toStableE (R := R)).ker
      (StableSteinberg R) (StableE R) := StableSteinberg.steinbergExtension R
  have hS : GroupExtension.IsUniversalFor.{u, u, u, u, u} S :=
    independentPlusFiberExtension_isUniversalFor R
  have hT : GroupExtension.IsUniversalFor.{u, u, u, u, u} T :=
    StableSteinberg.steinbergExtension_isUniversalFor R
  let f : S.Hom T := independentPlusFiberToSteinbergHom R
  let g : T.Hom S := independentSteinbergToPlusFiberHom R
  have hComp : GroupExtension.IsUniversalFor.liftHom hS S hS.1
      ((MonoidHom.id (StableE R)).comp (MonoidHom.id (StableE R))) = g.comp f :=
    GroupExtension.IsUniversalFor.liftHom_comp hS hT hS S hS.1
      (MonoidHom.id (StableE R)) (MonoidHom.id (StableE R))
  have hId : GroupExtension.IsUniversalFor.liftHom hS S hS.1
      (MonoidHom.id (StableE R)) = GroupExtension.Hom.id S :=
    GroupExtension.IsUniversalFor.liftHom_id hS
  calc
    g.comp f = GroupExtension.IsUniversalFor.liftHom hS S hS.1
        ((MonoidHom.id (StableE R)).comp (MonoidHom.id (StableE R))) := hComp.symm
    _ = GroupExtension.IsUniversalFor.liftHom hS S hS.1 (MonoidHom.id (StableE R)) :=
      congrArg (fun q : StableE R →* StableE R =>
        GroupExtension.IsUniversalFor.liftHom hS S hS.1 q)
        (MonoidHom.comp_id (MonoidHom.id (StableE R)))
    _ = GroupExtension.Hom.id S := hId

/-- The reverse original round trip is the identity on the actual Steinberg extension. -/
theorem independentPlusFiberToSteinbergHom_comp (R : Type u) [Ring R] :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    (independentPlusFiberToSteinbergHom R).comp (independentSteinbergToPlusFiberHom R) =
      GroupExtension.Hom.id (StableSteinberg.steinbergExtension R) := by
  have h := GroupExtension.IsUniversalFor.liftHom_comp
    (StableSteinberg.steinbergExtension_isUniversalFor R)
    (independentPlusFiberExtension_isUniversalFor R)
    (StableSteinberg.steinbergExtension_isUniversalFor R)
    (StableSteinberg.steinbergExtension R) (StableSteinberg.steinbergExtension_isCentral R)
    (MonoidHom.id (StableE R)) (MonoidHom.id (StableE R))
  rw [MonoidHom.comp_id, GroupExtension.IsUniversalFor.liftHom_id] at h
  exact h.symm

/-- The ordinary fundamental group of the original plus fiber is the original Steinberg group. -/
def independentPlusFiberSteinbergMulEquiv (R : Type u) [Ring R] :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R) ≃*
      StableSteinberg R :=
  MonoidHom.toMulEquiv (independentPlusFiberToSteinbergHom R).totalHom
    (independentSteinbergToPlusFiberHom R).totalHom
    (congrArg GroupExtension.Hom.totalHom (independentSteinbergToPlusFiberHom_comp R))
    (congrArg GroupExtension.Hom.totalHom (independentPlusFiberToSteinbergHom_comp R))

/-- The original second plus group is the actual kernel of the original Steinberg projection. -/
def independentPlusSteinbergKernelMulEquiv (R : Type u) [Ring R] :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R) ≃*
      (StableSteinberg.toStableE (R := R)).ker :=
  MonoidHom.toMulEquiv (independentPlusFiberToSteinbergHom R).kernelHom
    (independentSteinbergToPlusFiberHom R).kernelHom
    (congrArg GroupExtension.Hom.kernelHom (independentSteinbergToPlusFiberHom_comp R))
    (congrArg GroupExtension.Hom.kernelHom (independentPlusFiberToSteinbergHom_comp R))

/-- The original total-group equivalence preserves the whole original elementary projection. -/
theorem independentPlusFiberSteinbergMulEquiv_projection (R : Type u) [Ring R] :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    StableSteinberg.toStableE.comp (independentPlusFiberSteinbergMulEquiv R).toMonoidHom =
      independentPlusFiberToStableE R := by
  exact (independentPlusFiberToSteinbergHom R).rightHom_comm.trans
    (MonoidHom.id_comp _)

/-- The total and kernel comparisons retain the original connecting homomorphism. -/
theorem independentPlusFiberSteinbergMulEquiv_connecting (R : Type u) [Ring R]
    (a : HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R)) :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    let connecting : HomotopyGroup.Pi 2 (independentBGLCellTarget R)
        (independentBGLCellPoint R) →*
        FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R) :=
      independentPlusFiberConnectingHom R;
    let fiberCmp : FundamentalGroup (independentPlusFiber R)
        (independentPlusFiberPoint R) ≃* StableSteinberg R :=
      independentPlusFiberSteinbergMulEquiv R;
    let kernelCmp : HomotopyGroup.Pi 2 (independentBGLCellTarget R)
        (independentBGLCellPoint R) ≃* (StableSteinberg.toStableE (R := R)).ker :=
      independentPlusSteinbergKernelMulEquiv R;
    fiberCmp (connecting a) = (kernelCmp a : StableSteinberg R) :=
  (independentPlusFiberToSteinbergHom R).inl_comm_apply a

/-- The independently constructed original second plus group is the categorical algebraic K₂. -/
def independentPlusK2MulEquiv (R : Type u) [Ring R] :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R) ≃* K2 R :=
  (independentPlusSteinbergKernelMulEquiv R).trans (K2.kernelIsoKerOf R).groupIsoToMulEquiv.symm

/-- The K₂ inclusion of the actual comparison value is the original transported boundary. -/
theorem independentPlusK2MulEquiv_inclusion (R : Type u) [Ring R]
    (a : HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R)) :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    let connecting : HomotopyGroup.Pi 2 (independentBGLCellTarget R)
        (independentBGLCellPoint R) →*
        FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R) :=
      independentPlusFiberConnectingHom R;
    let plusCmp : HomotopyGroup.Pi 2 (independentBGLCellTarget R)
        (independentBGLCellPoint R) ≃* K2 R := independentPlusK2MulEquiv R;
    let fiberCmp : FundamentalGroup (independentPlusFiber R)
        (independentPlusFiberPoint R) ≃* StableSteinberg R :=
      independentPlusFiberSteinbergMulEquiv R;
    K2.inclusion.app (RingCat.of R) (plusCmp a) = fiberCmp (connecting a) := by
  letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩
  letI : Group (HomotopyGroup.Pi 2 (independentBGLCellTarget R)
      (independentBGLCellPoint R)) :=
    HomotopyGroup.group (X := independentBGLCellTarget R)
      (x := independentBGLCellPoint R) (Fin 2)
  let connecting : HomotopyGroup.Pi 2 (independentBGLCellTarget R)
      (independentBGLCellPoint R) →*
      FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R) :=
    independentPlusFiberConnectingHom R
  let plusCmp : HomotopyGroup.Pi 2 (independentBGLCellTarget R)
      (independentBGLCellPoint R) ≃* K2 R := independentPlusK2MulEquiv R
  let fiberCmp : FundamentalGroup (independentPlusFiber R)
      (independentPlusFiberPoint R) ≃* StableSteinberg R :=
    independentPlusFiberSteinbergMulEquiv R
  let kernelCmp : HomotopyGroup.Pi 2 (independentBGLCellTarget R)
      (independentBGLCellPoint R) ≃* (StableSteinberg.toStableE (R := R)).ker :=
    independentPlusSteinbergKernelMulEquiv R
  have h : K2.inclusion.app (RingCat.of R) (plusCmp a) =
      (kernelCmp a : StableSteinberg R) :=
    ConcreteCategory.congr_hom (K2.kernelIsoKerOf_inv_comp_ι (R := R)) (kernelCmp a)
  have hConnecting : fiberCmp (connecting a) = (kernelCmp a : StableSteinberg R) :=
    independentPlusFiberSteinbergMulEquiv_connecting R a
  exact h.trans hConnecting.symm

/-- The inverse K₂ dictionary returns the original connecting preimage of the included class. -/
theorem independentPlusK2MulEquiv_symm_boundary (R : Type u) [Ring R] (a : K2 R) :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (independentBGLCellTarget R)
        (independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := independentBGLCellTarget R)
        (x := independentBGLCellPoint R) (Fin 2);
    let connecting : HomotopyGroup.Pi 2 (independentBGLCellTarget R)
        (independentBGLCellPoint R) →*
        FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R) :=
      independentPlusFiberConnectingHom R;
    let plusCmp : HomotopyGroup.Pi 2 (independentBGLCellTarget R)
        (independentBGLCellPoint R) ≃* K2 R := independentPlusK2MulEquiv R;
    let fiberCmp : FundamentalGroup (independentPlusFiber R)
        (independentPlusFiberPoint R) ≃* StableSteinberg R :=
      independentPlusFiberSteinbergMulEquiv R;
    connecting (plusCmp.symm a) = fiberCmp.symm (K2.inclusion.app (RingCat.of R) a) := by
  letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩
  letI : Group (HomotopyGroup.Pi 2 (independentBGLCellTarget R)
      (independentBGLCellPoint R)) :=
    HomotopyGroup.group (X := independentBGLCellTarget R)
      (x := independentBGLCellPoint R) (Fin 2)
  let connecting : HomotopyGroup.Pi 2 (independentBGLCellTarget R)
      (independentBGLCellPoint R) →*
      FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R) :=
    independentPlusFiberConnectingHom R
  let plusCmp : HomotopyGroup.Pi 2 (independentBGLCellTarget R)
      (independentBGLCellPoint R) ≃* K2 R := independentPlusK2MulEquiv R
  let fiberCmp : FundamentalGroup (independentPlusFiber R)
      (independentPlusFiberPoint R) ≃* StableSteinberg R :=
    independentPlusFiberSteinbergMulEquiv R
  let z : StableSteinberg R := K2.inclusion.app (RingCat.of R) a
  have hIncl : K2.inclusion.app (RingCat.of R) (plusCmp (plusCmp.symm a)) =
      fiberCmp (connecting (plusCmp.symm a)) :=
    independentPlusK2MulEquiv_inclusion R (plusCmp.symm a)
  have h : fiberCmp (connecting (plusCmp.symm a)) = z :=
    hIncl.symm.trans
      (congrArg (fun b : K2 R => (K2.inclusion.app (RingCat.of R) b : StableSteinberg R))
        (plusCmp.apply_symm_apply a))
  exact fiberCmp.injective (h.trans (fiberCmp.apply_symm_apply z).symm)

private def independentPlusLiftSecondGroupDown (R : Type uR) [Ring R] :
    HomotopyGroup.Pi 2 (independentBGLCellTargetLift.{uR, uCarrier} R)
        (independentBGLCellPointLift.{uR, uCarrier} R) ≃*
      HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R) :=
  HomotopyGroup.mulEquivOfBasedInverse 1 (independentBGLCellTargetDown.{uR, uCarrier} R)
    (independentBGLCellTargetUp.{uR, uCarrier} R)
    (independentBGLCellTargetDown_point.{uR, uCarrier} R)
    (independentBGLCellTargetUp_point.{uR, uCarrier} R)
    (by
      rw [independentBGLCellTargetUp_comp_down.{uR, uCarrier} R]
      exact ContinuousMap.HomotopyRel.refl _ _)
    (by
      rw [independentBGLCellTargetDown_comp_up.{uR, uCarrier} R]
      exact ContinuousMap.HomotopyRel.refl _ _)

/-- The same original K₂ comparison in any independently lifted plus carrier. -/
def independentPlusLiftK2MulEquiv (R : Type uR) [Ring R] :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    HomotopyGroup.Pi 2 (independentBGLCellTargetLift.{uR, uCarrier} R)
      (independentBGLCellPointLift.{uR, uCarrier} R) ≃* K2 R :=
  (independentPlusLiftSecondGroupDown R).trans (independentPlusK2MulEquiv R)

/-- The lifted comparison uses the actual downward map of the original plus carrier. -/
theorem independentPlusLiftK2MulEquiv_apply (R : Type uR) [Ring R]
    (a : HomotopyGroup.Pi 2 (independentBGLCellTargetLift.{uR, uCarrier} R)
      (independentBGLCellPointLift.{uR, uCarrier} R)) :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    independentPlusLiftK2MulEquiv R a = independentPlusK2MulEquiv R
      (HomotopyGroup.mapHomOfEq (independentBGLCellTargetDown.{uR, uCarrier} R)
        (independentBGLCellTargetDown_point.{uR, uCarrier} R) 1 a) := rfl

/-- The inverse lifted dictionary uses the original upward map on the original second group. -/
theorem independentPlusLiftK2MulEquiv_symm_apply (R : Type uR) [Ring R] (a : K2 R) :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    (independentPlusLiftK2MulEquiv.{uR, uCarrier} R).symm a =
      HomotopyGroup.mapHomOfEq (independentBGLCellTargetUp.{uR, uCarrier} R)
        (independentBGLCellTargetUp_point.{uR, uCarrier} R) 1
        ((independentPlusK2MulEquiv R).symm a) := rfl

end StableGL

namespace QuillenPlus

open UniverseAssembly

/-- The current finite-projective second group has the original normalized plus dictionary. -/
def currentFGProjectivePlusSecondMulEquiv.{uR', uM', uProbe'} (R : Type uR') [Ring R] :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    @MulEquiv (ConnectiveKGroups.groupCarrier (FGProjectiveCat.{max uR' uM'} R) 2)
      (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R))
      (ConnectiveKGroups.groupStructure
        (FGProjectiveCat.{max uR' uM'} R) 2).toMulOneClass.toMulOne.toMul
      inferInstance := by
  let C := FGProjectiveCat.{max uR' uM'} R
  let _ : Group (HomotopyGroup.Pi 2 (NQKSpace C) (Path.refl (NQReal.basepoint C))) :=
    HomotopyGroup.group (X := NQKSpace C) (x := Path.refl (NQReal.basepoint C)) (Fin 2)
  let e := (canonicalOriginalPlusQPositiveComparison.{uR', uM', uProbe'} R 1).symm
  refine { toEquiv := e.toEquiv, map_mul' := ?_ }
  intro a b
  change e (@Mul.mul (ConnectiveKGroups.groupCarrier C 2)
    (ConnectiveKGroups.groupStructure C 2).toMulOneClass.toMulOne.toMul a b) = e a * e b
  rw [ConnectiveKGroups.groupStructure_succ_mul_original C 1 a b]
  exact e.map_mul a b

/-- Every current value retains the original normalized inverse and whole point chart. -/
theorem currentFGProjectivePlusSecondMulEquiv_apply (R : Type uR) [Ring R]
    (a : ConnectiveKGroups.groupCarrier (FGProjectiveCat.{max uR uM} R) 2) :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    currentFGProjectivePlusSecondMulEquiv.{uR, uM, uProbe} R a =
      (originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uProbe} R 1).symm
        (HomotopyGroup.mapHomOfEq
          (OriginalQuillenUnliftedTransport.originalNQLoopPointHomeomorph
            (FGProjectiveCat.{max uR uM} R)).toHomotopyEquiv.toFun
          (canonicalOriginalQLoopChart_point R) 1 a) := by
  let C := FGProjectiveCat.{max uR uM} R
  let _ : Group (HomotopyGroup.Pi 2 (NQKSpace C) (Path.refl (NQReal.basepoint C))) :=
    HomotopyGroup.group (X := NQKSpace C) (x := Path.refl (NQReal.basepoint C)) (Fin 2)
  change (canonicalOriginalPlusQPositiveComparison.{uR, uM, uProbe} R 1).symm a = _
  rw [canonicalOriginalPlusQPositiveComparison_symm_apply, canonicalOriginalQPositiveChart_apply]

/-- Original current K₂ of finite projectives is the original categorical Steinberg kernel. -/
def currentFGProjectiveK2MulEquiv.{uR', uM', uProbe'} (R : Type uR') [Ring R] :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    @MulEquiv (ConnectiveKGroups.groupCarrier (FGProjectiveCat.{max uR' uM'} R) 2) (K2 R)
      (ConnectiveKGroups.groupStructure
        (FGProjectiveCat.{max uR' uM'} R) 2).toMulOneClass.toMulOne.toMul
      inferInstance := by
  let _ := ConnectiveKGroups.groupStructure (FGProjectiveCat.{max uR' uM'} R) 2
  exact (currentFGProjectivePlusSecondMulEquiv.{uR', uM', uProbe'} R).trans
    (StableGL.independentPlusK2MulEquiv R)

/-- The current K₂ value uses the original current-group to plus map. -/
theorem currentFGProjectiveK2MulEquiv_apply (R : Type uR) [Ring R]
    (a : ConnectiveKGroups.groupCarrier (FGProjectiveCat.{max uR uM} R) 2) :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    currentFGProjectiveK2MulEquiv.{uR, uM, uProbe} R a =
      StableGL.independentPlusK2MulEquiv R
        (currentFGProjectivePlusSecondMulEquiv.{uR, uM, uProbe} R a) := rfl

/-- The actual current second-group inclusion retains its original connecting image. -/
theorem currentFGProjectiveK2MulEquiv_inclusion (R : Type uR) [Ring R]
    (a : ConnectiveKGroups.groupCarrier (FGProjectiveCat.{max uR uM} R) 2) :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    letI := ConnectiveKGroups.groupStructure (FGProjectiveCat.{max uR uM} R) 2;
    let currentCmp : ConnectiveKGroups.groupCarrier (FGProjectiveCat.{max uR uM} R) 2 ≃*
        K2 R := currentFGProjectiveK2MulEquiv.{uR, uM, uProbe} R;
    let plusCmp : ConnectiveKGroups.groupCarrier (FGProjectiveCat.{max uR uM} R) 2 ≃*
        HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
          (StableGL.independentBGLCellPoint R) :=
      currentFGProjectivePlusSecondMulEquiv.{uR, uM, uProbe} R;
    let connecting : HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R) →*
        FundamentalGroup (StableGL.independentPlusFiber R)
          (StableGL.independentPlusFiberPoint R) :=
      StableGL.independentPlusFiberConnectingHom R;
    let fiberCmp : FundamentalGroup (StableGL.independentPlusFiber R)
        (StableGL.independentPlusFiberPoint R) ≃* StableSteinberg R :=
      StableGL.independentPlusFiberSteinbergMulEquiv R;
    K2.inclusion.app (RingCat.of R) (currentCmp a) = fiberCmp (connecting (plusCmp a)) := by
  letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩
  letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
      (StableGL.independentBGLCellPoint R)) :=
    HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
      (x := StableGL.independentBGLCellPoint R) (Fin 2)
  letI := ConnectiveKGroups.groupStructure (FGProjectiveCat.{max uR uM} R) 2
  let currentCmp : ConnectiveKGroups.groupCarrier (FGProjectiveCat.{max uR uM} R) 2 ≃*
      K2 R := currentFGProjectiveK2MulEquiv.{uR, uM, uProbe} R
  let plusCmp : ConnectiveKGroups.groupCarrier (FGProjectiveCat.{max uR uM} R) 2 ≃*
      HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R) :=
    currentFGProjectivePlusSecondMulEquiv.{uR, uM, uProbe} R
  let connecting : HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
      (StableGL.independentBGLCellPoint R) →*
      FundamentalGroup (StableGL.independentPlusFiber R)
        (StableGL.independentPlusFiberPoint R) :=
    StableGL.independentPlusFiberConnectingHom R
  let fiberCmp : FundamentalGroup (StableGL.independentPlusFiber R)
      (StableGL.independentPlusFiberPoint R) ≃* StableSteinberg R :=
    StableGL.independentPlusFiberSteinbergMulEquiv R
  let scalarCmp : HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
      (StableGL.independentBGLCellPoint R) ≃* K2 R := StableGL.independentPlusK2MulEquiv R
  have hCurrent : currentCmp a = scalarCmp (plusCmp a) :=
    currentFGProjectiveK2MulEquiv_apply R a
  have hScalar : K2.inclusion.app (RingCat.of R) (scalarCmp (plusCmp a)) =
      fiberCmp (connecting (plusCmp a)) :=
    StableGL.independentPlusK2MulEquiv_inclusion R (plusCmp a)
  exact (congrArg (fun b : K2 R =>
    (K2.inclusion.app (RingCat.of R) b : StableSteinberg R)) hCurrent).trans hScalar

/-- The whole current second-group homomorphism satisfies the original inclusion diagram. -/
theorem currentFGProjectiveK2MulEquiv_inclusion_hom (R : Type uR) [Ring R] :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    letI := ConnectiveKGroups.groupStructure (FGProjectiveCat.{max uR uM} R) 2;
    let currentCmp : ConnectiveKGroups.groupCarrier (FGProjectiveCat.{max uR uM} R) 2 ≃*
        K2 R := currentFGProjectiveK2MulEquiv.{uR, uM, uProbe} R;
    let plusCmp : ConnectiveKGroups.groupCarrier (FGProjectiveCat.{max uR uM} R) 2 ≃*
        HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
          (StableGL.independentBGLCellPoint R) :=
      currentFGProjectivePlusSecondMulEquiv.{uR, uM, uProbe} R;
    let connecting : HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R) →*
        FundamentalGroup (StableGL.independentPlusFiber R)
          (StableGL.independentPlusFiberPoint R) :=
      StableGL.independentPlusFiberConnectingHom R;
    let fiberCmp : FundamentalGroup (StableGL.independentPlusFiber R)
        (StableGL.independentPlusFiberPoint R) ≃* StableSteinberg R :=
      StableGL.independentPlusFiberSteinbergMulEquiv R;
    (K2.inclusion.app (RingCat.of R)).hom.comp currentCmp.toMonoidHom =
      fiberCmp.toMonoidHom.comp (connecting.comp plusCmp.toMonoidHom) := by
  letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩
  letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
      (StableGL.independentBGLCellPoint R)) :=
    HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
      (x := StableGL.independentBGLCellPoint R) (Fin 2)
  letI := ConnectiveKGroups.groupStructure (FGProjectiveCat.{max uR uM} R) 2
  let currentCmp : ConnectiveKGroups.groupCarrier (FGProjectiveCat.{max uR uM} R) 2 ≃*
      K2 R := currentFGProjectiveK2MulEquiv.{uR, uM, uProbe} R
  let plusCmp : ConnectiveKGroups.groupCarrier (FGProjectiveCat.{max uR uM} R) 2 ≃*
      HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R) :=
    currentFGProjectivePlusSecondMulEquiv.{uR, uM, uProbe} R
  let connecting : HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
      (StableGL.independentBGLCellPoint R) →*
      FundamentalGroup (StableGL.independentPlusFiber R)
        (StableGL.independentPlusFiberPoint R) :=
    StableGL.independentPlusFiberConnectingHom R
  let fiberCmp : FundamentalGroup (StableGL.independentPlusFiber R)
      (StableGL.independentPlusFiberPoint R) ≃* StableSteinberg R :=
    StableGL.independentPlusFiberSteinbergMulEquiv R
  apply MonoidHom.ext
  intro a
  exact currentFGProjectiveK2MulEquiv_inclusion R a

/-- The inverse current dictionary returns the original inverse normalized point chart. -/
theorem currentFGProjectiveK2MulEquiv_symm_apply (R : Type uR) [Ring R] (a : K2 R) :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    letI := ConnectiveKGroups.groupStructure (FGProjectiveCat.{max uR uM} R) 2;
    (currentFGProjectiveK2MulEquiv.{uR, uM, uProbe} R).symm a =
      canonicalOriginalPlusQPositiveComparison.{uR, uM, uProbe} R 1
        ((StableGL.independentPlusK2MulEquiv R).symm a) := by
  let _ := ConnectiveKGroups.groupStructure (FGProjectiveCat.{max uR uM} R) 2
  rfl

/-- Original Quillen K₂ in all six independent source roles is the categorical algebraic K₂. -/
def quillenIndependentPlusK2MulEquiv (R : Type uR) [Ring R] :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    HomotopyGroup.Pi 2
      (sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
      (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) ≃* K2 R :=
  (quillenIndependentPlusPositiveHomotopyEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R 1).trans
    (StableGL.independentPlusLiftK2MulEquiv.{uR, max uNative
      (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R)

/-- The complete Quillen K₂ value retains the actual forward projection and carrier descent. -/
theorem quillenIndependentPlusK2MulEquiv_apply (R : Type uR) [Ring R]
    (a : HomotopyGroup.Pi 2
      (sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
      (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)) :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    quillenIndependentPlusK2MulEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R a =
      StableGL.independentPlusK2MulEquiv R
      (HomotopyGroup.mapHomOfEq (StableGL.independentBGLCellTargetDown.{uR, max uNative
        (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R)
        (StableGL.independentBGLCellTargetDown_point R) 1
        (HomotopyGroup.mapHomOfEq
          (quillenIndependentPlusForwardProjection.{uR, uM, uObj, uHom, uNative, uProbe} R)
          (quillenIndependentPlusForwardProjection_point R) 1 a)) := by
  let down := StableGL.independentBGLCellTargetDown.{uR, max uNative
    (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R
  let hDown := StableGL.independentBGLCellTargetDown_point.{uR, max uNative
    (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R
  have h := quillenIndependentPlusPositiveHomotopyEquiv_apply.{uR, uM, uObj,
    uHom, uNative, uProbe} R 1 a
  exact (StableGL.independentPlusLiftK2MulEquiv_apply R
    (quillenIndependentPlusPositiveHomotopyEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R 1 a)).trans
      (congrArg (fun b : HomotopyGroup.Pi 2
          (plusSpace.{uR, uM, uObj, uHom, uNative} R)
          (plusPoint.{uR, uM, uObj, uHom, uNative} R) =>
        StableGL.independentPlusK2MulEquiv R (HomotopyGroup.mapHomOfEq down hDown 1 b)) h)

/-- The original Quillen value has the original Steinberg inclusion of its actual boundary. -/
theorem quillenIndependentPlusK2MulEquiv_inclusion (R : Type uR) [Ring R]
    (a : HomotopyGroup.Pi 2
      (sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
      (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)) :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    let fullCmp : HomotopyGroup.Pi 2
        (sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) ≃* K2 R :=
      quillenIndependentPlusK2MulEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R;
    let forward : HomotopyGroup.Pi 2
        (sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) →*
        HomotopyGroup.Pi 2 (plusSpace.{uR, uM, uObj, uHom, uNative} R)
          (plusPoint.{uR, uM, uObj, uHom, uNative} R) :=
      HomotopyGroup.mapHomOfEq
        (quillenIndependentPlusForwardProjection.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (quillenIndependentPlusForwardProjection_point R) 1;
    let down : HomotopyGroup.Pi 2 (plusSpace.{uR, uM, uObj, uHom, uNative} R)
        (plusPoint.{uR, uM, uObj, uHom, uNative} R) →*
        HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
          (StableGL.independentBGLCellPoint R) :=
      HomotopyGroup.mapHomOfEq (StableGL.independentBGLCellTargetDown.{uR, max uNative
        (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R)
        (StableGL.independentBGLCellTargetDown_point R) 1;
    let connecting : HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R) →*
        FundamentalGroup (StableGL.independentPlusFiber R)
          (StableGL.independentPlusFiberPoint R) :=
      StableGL.independentPlusFiberConnectingHom R;
    let fiberCmp : FundamentalGroup (StableGL.independentPlusFiber R)
        (StableGL.independentPlusFiberPoint R) ≃* StableSteinberg R :=
      StableGL.independentPlusFiberSteinbergMulEquiv R;
    K2.inclusion.app (RingCat.of R) (fullCmp a) = fiberCmp (connecting (down (forward a))) := by
  letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩
  letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
      (StableGL.independentBGLCellPoint R)) :=
    HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
      (x := StableGL.independentBGLCellPoint R) (Fin 2)
  let fullCmp : HomotopyGroup.Pi 2
      (sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
      (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) ≃* K2 R :=
    quillenIndependentPlusK2MulEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R
  let forward : HomotopyGroup.Pi 2
      (sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
      (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) →*
      HomotopyGroup.Pi 2 (plusSpace.{uR, uM, uObj, uHom, uNative} R)
        (plusPoint.{uR, uM, uObj, uHom, uNative} R) :=
    HomotopyGroup.mapHomOfEq
      (quillenIndependentPlusForwardProjection.{uR, uM, uObj, uHom, uNative, uProbe} R)
      (quillenIndependentPlusForwardProjection_point R) 1
  let down : HomotopyGroup.Pi 2 (plusSpace.{uR, uM, uObj, uHom, uNative} R)
      (plusPoint.{uR, uM, uObj, uHom, uNative} R) →*
      HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R) :=
    HomotopyGroup.mapHomOfEq (StableGL.independentBGLCellTargetDown.{uR, max uNative
      (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R)
      (StableGL.independentBGLCellTargetDown_point R) 1
  let connecting : HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
      (StableGL.independentBGLCellPoint R) →*
      FundamentalGroup (StableGL.independentPlusFiber R)
        (StableGL.independentPlusFiberPoint R) :=
    StableGL.independentPlusFiberConnectingHom R
  let fiberCmp : FundamentalGroup (StableGL.independentPlusFiber R)
      (StableGL.independentPlusFiberPoint R) ≃* StableSteinberg R :=
    StableGL.independentPlusFiberSteinbergMulEquiv R
  let scalarCmp : HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
      (StableGL.independentBGLCellPoint R) ≃* K2 R := StableGL.independentPlusK2MulEquiv R
  have hFull : fullCmp a = scalarCmp (down (forward a)) :=
    quillenIndependentPlusK2MulEquiv_apply R a
  have hScalar : K2.inclusion.app (RingCat.of R) (scalarCmp (down (forward a))) =
      fiberCmp (connecting (down (forward a))) :=
    StableGL.independentPlusK2MulEquiv_inclusion R (down (forward a))
  exact (congrArg (fun b : K2 R =>
    (K2.inclusion.app (RingCat.of R) b : StableSteinberg R)) hFull).trans hScalar

/-- The inverse Quillen K₂ dictionary retains the actual plus lift and inverse zero section. -/
theorem quillenIndependentPlusK2MulEquiv_symm_apply (R : Type uR) [Ring R] (a : K2 R) :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    (quillenIndependentPlusK2MulEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R).symm a =
      HomotopyGroup.mapHomOfEq
        (quillenIndependentPlusInverseSection.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (quillenIndependentPlusInverseSection_point R) 1
        (HomotopyGroup.mapHomOfEq (StableGL.independentBGLCellTargetUp.{uR, max uNative
          (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R)
          (StableGL.independentBGLCellTargetUp_point R) 1
          ((StableGL.independentPlusK2MulEquiv R).symm a)) := by
  change (quillenIndependentPlusPositiveHomotopyEquiv.{uR, uM, uObj, uHom,
    uNative, uProbe} R 1).symm
    ((StableGL.independentPlusLiftK2MulEquiv R).symm a) = _
  rw [quillenIndependentPlusPositiveHomotopyEquiv_symm_apply,
    StableGL.independentPlusLiftK2MulEquiv_symm_apply]

end QuillenPlus

end AlgebraicKTheory

end
