/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.KTheory.Ring.K2.SteinbergQuillenComparison

/-!
# Original kernel and independent-universe clients of the second K-group comparison
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w uR uM uObj uHom uNative uProbe

attribute [local instance 1001] Nat.instNeZeroSucc

namespace AlgebraicKTheory

/-- The same actual fiber group has its unique original lift to any central target extension. -/
theorem original_plus_fiber_universal_target_test (R : Type u) [Ring R]
    {N : Type v} {E : Type w} [Group N] [Group E]
    (T : GroupExtension N E (StableE R)) (hT : T.IsCentral) :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    ∃! f : FundamentalGroup (StableGL.independentPlusFiber R)
        (StableGL.independentPlusFiberPoint R) →* E,
      T.rightHom.comp f = StableGL.independentPlusFiberToStableE R :=
  by
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2)
    let S : GroupExtension
        (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
          (StableGL.independentBGLCellPoint R))
        (FundamentalGroup (StableGL.independentPlusFiber R)
          (StableGL.independentPlusFiberPoint R)) (StableE R) :=
      StableGL.independentPlusFiberExtension R
    have hU : GroupExtension.IsUniversalFor.{u, u, u, v, w} S :=
      StableGL.independentPlusFiberExtension_isUniversalFor R
    exact hU.2 T hT

/-- The kernel constructor returns the same Steinberg element through the original boundary. -/
theorem original_steinberg_kernel_boundary_test (R : Type u) [Ring R]
    (z : StableSteinberg R) (hz : StableSteinberg.toStableE z = 1) :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    let connecting : HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R) →*
        FundamentalGroup (StableGL.independentPlusFiber R)
          (StableGL.independentPlusFiberPoint R) :=
      StableGL.independentPlusFiberConnectingHom R;
    let plusCmp : HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R) ≃* K2 R :=
      StableGL.independentPlusK2MulEquiv R;
    let fiberCmp : FundamentalGroup (StableGL.independentPlusFiber R)
        (StableGL.independentPlusFiberPoint R) ≃* StableSteinberg R :=
      StableGL.independentPlusFiberSteinbergMulEquiv R;
    fiberCmp (connecting (plusCmp.symm (K2.ofKer z hz))) = z := by
  letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩
  letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
      (StableGL.independentBGLCellPoint R)) :=
    HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
      (x := StableGL.independentBGLCellPoint R) (Fin 2)
  let connecting : HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
      (StableGL.independentBGLCellPoint R) →*
      FundamentalGroup (StableGL.independentPlusFiber R)
        (StableGL.independentPlusFiberPoint R) :=
    StableGL.independentPlusFiberConnectingHom R
  let plusCmp : HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
      (StableGL.independentBGLCellPoint R) ≃* K2 R :=
    StableGL.independentPlusK2MulEquiv R
  let fiberCmp : FundamentalGroup (StableGL.independentPlusFiber R)
      (StableGL.independentPlusFiberPoint R) ≃* StableSteinberg R :=
    StableGL.independentPlusFiberSteinbergMulEquiv R
  have hForward : K2.inclusion.app (RingCat.of R)
      (plusCmp (plusCmp.symm (K2.ofKer z hz))) =
      fiberCmp (connecting (plusCmp.symm (K2.ofKer z hz))) :=
    StableGL.independentPlusK2MulEquiv_inclusion R (plusCmp.symm (K2.ofKer z hz))
  have h : fiberCmp (connecting (plusCmp.symm (K2.ofKer z hz))) =
      K2.inclusion.app (RingCat.of R) (plusCmp (plusCmp.symm (K2.ofKer z hz))) :=
    hForward.symm
  rw [MulEquiv.apply_symm_apply, K2.inclusion_ofKer] at h
  exact h

/-- Both original group comparisons recover the original fiber loop of an included K₂ class. -/
theorem original_plus_second_group_inverse_test (R : Type u) [Ring R] (a : K2 R) :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    let connecting : HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R) →*
        FundamentalGroup (StableGL.independentPlusFiber R)
          (StableGL.independentPlusFiberPoint R) :=
      StableGL.independentPlusFiberConnectingHom R;
    let plusCmp : HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R) ≃* K2 R :=
      StableGL.independentPlusK2MulEquiv R;
    let fiberCmp : FundamentalGroup (StableGL.independentPlusFiber R)
        (StableGL.independentPlusFiberPoint R) ≃* StableSteinberg R :=
      StableGL.independentPlusFiberSteinbergMulEquiv R;
    connecting (plusCmp.symm a) = fiberCmp.symm (K2.inclusion.app (RingCat.of R) a) :=
  StableGL.independentPlusK2MulEquiv_symm_boundary R a

namespace QuillenPlus

open UniverseAssembly

/-- The actual original normalized plus class is unchanged by the current K₂ dictionary. -/
theorem original_current_second_group_plus_test (R : Type uR) [Ring R]
    (a : HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
      (StableGL.independentBGLCellPoint R)) :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    letI := ConnectiveKGroups.groupStructure (FGProjectiveCat.{max uR uM} R) 2;
    currentFGProjectiveK2MulEquiv.{uR, uM, uProbe} R
      (canonicalOriginalPlusQPositiveComparison.{uR, uM, uProbe} R 1 a) =
        StableGL.independentPlusK2MulEquiv R a := by
  let _ := ConnectiveKGroups.groupStructure (FGProjectiveCat.{max uR uM} R) 2
  rw [currentFGProjectiveK2MulEquiv_apply]
  change StableGL.independentPlusK2MulEquiv R
      ((canonicalOriginalPlusQPositiveComparison.{uR, uM, uProbe} R 1).symm
        (canonicalOriginalPlusQPositiveComparison.{uR, uM, uProbe} R 1 a)) = _
  rw [MulEquiv.symm_apply_apply]

/-- The native current dictionary and its actual inclusion have the original whole hom diagram. -/
theorem original_current_second_group_inclusion_test (R : Type uR) [Ring R]
    (a : ConnectiveKGroups.groupCarrier (FGProjectiveCat.{max uR uM} R) 2) :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    let currentCmp : @MulEquiv
        (ConnectiveKGroups.groupCarrier (FGProjectiveCat.{max uR uM} R) 2) (K2 R)
        (ConnectiveKGroups.groupStructure
          (FGProjectiveCat.{max uR uM} R) 2).toMulOneClass.toMulOne.toMul
        inferInstance := currentFGProjectiveK2MulEquiv.{uR, uM, uProbe} R;
    let plusCmp : @MulEquiv
        (ConnectiveKGroups.groupCarrier (FGProjectiveCat.{max uR uM} R) 2)
        (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
          (StableGL.independentBGLCellPoint R))
        (ConnectiveKGroups.groupStructure
          (FGProjectiveCat.{max uR uM} R) 2).toMulOneClass.toMulOne.toMul
        inferInstance := currentFGProjectivePlusSecondMulEquiv.{uR, uM, uProbe} R;
    let connecting : HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R) →*
        FundamentalGroup (StableGL.independentPlusFiber R)
          (StableGL.independentPlusFiberPoint R) :=
      StableGL.independentPlusFiberConnectingHom R;
    let fiberCmp : FundamentalGroup (StableGL.independentPlusFiber R)
        (StableGL.independentPlusFiberPoint R) ≃* StableSteinberg R :=
      StableGL.independentPlusFiberSteinbergMulEquiv R;
    K2.inclusion.app (RingCat.of R) (currentCmp a) = fiberCmp (connecting (plusCmp a)) :=
  currentFGProjectiveK2MulEquiv_inclusion R a

/-- An actual kernel element survives the complete original six-universe Quillen round trip. -/
theorem original_quillen_second_group_kernel_test (R : Type uR) [Ring R]
    (z : StableSteinberg R) (hz : StableSteinberg.toStableE z = 1) :
    letI : Nonempty (Fin 2) := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩;
    letI : Group (HomotopyGroup.Pi 2 (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R)) :=
      HomotopyGroup.group (X := StableGL.independentBGLCellTarget R)
        (x := StableGL.independentBGLCellPoint R) (Fin 2);
    K2.inclusion.app (RingCat.of R)
      (quillenIndependentPlusK2MulEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R
        ((quillenIndependentPlusK2MulEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R).symm
          (K2.ofKer z hz))) = z := by
  rw [MulEquiv.apply_symm_apply, K2.inclusion_ofKer]

end QuillenPlus

end AlgebraicKTheory

end
