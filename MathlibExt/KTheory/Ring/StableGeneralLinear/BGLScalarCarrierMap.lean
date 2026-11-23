/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.BGLScalarLoopPiOneCalibration
public import MathlibExt.KTheory.Ring.StableGeneralLinear.IndependentPlusUniverseLift

/-!
# The actual scalar source map in a common carrier frame

The ring universes remain independent. Only the original source spaces are
lifted to max uR uS uCarrier, using literal carrier up/down maps. The based
fundamental-group square and subgroup-image law are derived from the same
original mixed-world source map and its actual point equation.
-/

noncomputable section

open CategoryTheory
open scoped ContinuousMap

universe uR uS uCarrier

namespace AlgebraicKTheory.StableGL

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- The actual mixed-ring source map, lifted only at its two original carriers. -/
public def ordinaryBGLScalarCarrierMap (f : R →+* S) :
    independentBGLSourceLift.{uR, max uS uCarrier} R ⟶
      independentBGLSourceLift.{uS, max uR uCarrier} S :=
  TopCat.ofHom
    ⟨fun x => ULift.up (ordinaryBGLScalarMap f x.down),
      continuous_uliftUp.comp ((ordinaryBGLScalarMap f).continuous.comp continuous_uliftDown)⟩

private theorem ordinaryBGLScalarCarrierMap_point_computed (f : R →+* S) :
    ordinaryBGLScalarCarrierMap.{uR, uS, uCarrier} f
      (independentBGLSourcePointLift.{uR, max uS uCarrier} R) =
        independentBGLSourcePointLift.{uS, max uR uCarrier} S := by
  change ULift.up (ordinaryBGLScalarMap f (ordinaryBGLBasepoint R)) =
    ULift.up (ordinaryBGLBasepoint S)
  exact congrArg ULift.up (ordinaryBGLScalarMap_point f)

/-- The literal source lift retains both original marked vertices. -/
public theorem ordinaryBGLScalarCarrierMap_point (f : R →+* S) :
    ordinaryBGLScalarCarrierMap.{uR, uS, uCarrier} f
      (independentBGLSourcePointLift.{uR, max uS uCarrier} R) =
        independentBGLSourcePointLift.{uS, max uR uCarrier} S :=
  ordinaryBGLScalarCarrierMap_point_computed f

private theorem ordinaryBGLScalarCarrierMap_down_square_computed (f : R →+* S) :
    (Homeomorph.ulift :
      independentBGLSourceLift.{uS, max uR uCarrier} S ≃ₜ ordinaryBGL S).toHomotopyEquiv.toFun.comp
        (ordinaryBGLScalarCarrierMap.{uR, uS, uCarrier} f).hom =
      (ordinaryBGLScalarMap f).comp
        (Homeomorph.ulift :
          independentBGLSourceLift.{uR, max uS uCarrier} R ≃ₜ ordinaryBGL R).toHomotopyEquiv.toFun
              := by
  apply ContinuousMap.ext
  intro x
  rfl

/-- Every original source value satisfies the strict carrier-down square. -/
public theorem ordinaryBGLScalarCarrierMap_down_square (f : R →+* S) :
    (Homeomorph.ulift :
      independentBGLSourceLift.{uS, max uR uCarrier} S ≃ₜ ordinaryBGL S).toHomotopyEquiv.toFun.comp
        (ordinaryBGLScalarCarrierMap.{uR, uS, uCarrier} f).hom =
      (ordinaryBGLScalarMap f).comp
        (Homeomorph.ulift :
          independentBGLSourceLift.{uR, max uS uCarrier} R ≃ₜ ordinaryBGL R).toHomotopyEquiv.toFun
              :=
  ordinaryBGLScalarCarrierMap_down_square_computed f

/-- The actual based source maps commute with both original carrier projections. -/
public theorem ordinaryBGLScalarCarrierMap_pi1_down_square (f : R →+* S) :
    (FundamentalGroup.UniverseLift.downMap.{uS, max uR uCarrier}
      (ordinaryBGL S) (ordinaryBGLBasepoint S)).comp
        (FundamentalGroup.mapOfEq (ordinaryBGLScalarCarrierMap.{uR, uS, uCarrier} f).hom
          (ordinaryBGLScalarCarrierMap_point.{uR, uS, uCarrier} f)) =
      (FundamentalGroup.mapOfEq (ordinaryBGLScalarMap f) (ordinaryBGLScalarMap_point f)).comp
        (FundamentalGroup.UniverseLift.downMap.{uR, max uS uCarrier}
          (ordinaryBGL R) (ordinaryBGLBasepoint R)) := by
  let X := independentBGLSourceLift.{uR, max uS uCarrier} R
  let x := independentBGLSourcePointLift.{uR, max uS uCarrier} R
  let Y := independentBGLSourceLift.{uS, max uR uCarrier} S
  let y := independentBGLSourcePointLift.{uS, max uR uCarrier} S
  let F := (ordinaryBGLScalarCarrierMap.{uR, uS, uCarrier} f).hom
  let dR := (Homeomorph.ulift : X ≃ₜ ordinaryBGL R).toHomotopyEquiv.toFun
  let dS := (Homeomorph.ulift : Y ≃ₜ ordinaryBGL S).toHomotopyEquiv.toFun
  let hF := ordinaryBGLScalarCarrierMap_point.{uR, uS, uCarrier} f
  have hL : (dS.comp F) x = ordinaryBGLBasepoint S := (congrArg dS hF).trans rfl
  have hR : ((ordinaryBGLScalarMap f).comp dR) x = ordinaryBGLBasepoint S :=
    ordinaryBGLScalarMap_point f
  have hMaps :
      (⟨dS.comp F, hL⟩ : {m : C(X, ordinaryBGL S) // m x = ordinaryBGLBasepoint S}) =
        ⟨(ordinaryBGLScalarMap f).comp dR, hR⟩ :=
    Subtype.ext (ordinaryBGLScalarCarrierMap_down_square.{uR, uS, uCarrier} f)
  have hEq := congrArg
    (fun m : {m : C(X, ordinaryBGL S) // m x = ordinaryBGLBasepoint S} =>
      FundamentalGroup.mapOfEq m.val m.property) hMaps
  have hCompL := FundamentalGroup.mapOfEq_comp F dS hF rfl hL
  have hCompR := FundamentalGroup.mapOfEq_comp dR (ordinaryBGLScalarMap f) rfl
    (ordinaryBGLScalarMap_point f) hR
  exact hCompL.symm.trans (hEq.trans hCompR)

/-- The exact transported original plus subgroup maps into the transported target subgroup. -/
public theorem ordinaryBGLScalarCarrierMap_preservesPlusSubgroup (f : R →+* S)
    (p : FundamentalGroup (independentBGLSourceLift.{uR, max uS uCarrier} R)
      (independentBGLSourcePointLift.{uR, max uS uCarrier} R))
    (hp : p ∈ BGLPlusSubgroupLift.{uR, max uS uCarrier} R) :
    FundamentalGroup.mapOfEq (ordinaryBGLScalarCarrierMap.{uR, uS, uCarrier} f).hom
      (ordinaryBGLScalarCarrierMap_point.{uR, uS, uCarrier} f) p ∈
        BGLPlusSubgroupLift.{uS, max uR uCarrier} S := by
  have h := congrArg (fun m => m p) (ordinaryBGLScalarCarrierMap_pi1_down_square.{uR, uS, uCarrier}
      f)
  change FundamentalGroup.UniverseLift.downMap.{uS, max uR uCarrier}
      (ordinaryBGL S) (ordinaryBGLBasepoint S)
        (FundamentalGroup.mapOfEq (ordinaryBGLScalarCarrierMap.{uR, uS, uCarrier} f).hom
          (ordinaryBGLScalarCarrierMap_point.{uR, uS, uCarrier} f) p) ∈ BGLPlusSubgroup S
  have hImage := ordinaryBGLScalarMap_preservesPlusSubgroup f
    (FundamentalGroup.UniverseLift.downMap.{uR, max uS uCarrier}
      (ordinaryBGL R) (ordinaryBGLBasepoint R) p) hp
  exact Eq.mpr (congrArg (fun q => q ∈ BGLPlusSubgroup S) h) hImage


private theorem scalarCarrierMap_apply_computed (f : R →+* S)
    (x : independentBGLSourceLift.{uR, max uS uCarrier} R) :
    ordinaryBGLScalarCarrierMap.{uR, uS, uCarrier} f x =
      ULift.up (ordinaryBGLScalarMap f x.down) := rfl

/-- Every lifted source value is sent by the same original scalar map and literal carrier up. -/
public theorem ordinaryBGLScalarCarrierMap_apply (f : R →+* S)
    (x : independentBGLSourceLift.{uR, max uS uCarrier} R) :
    ordinaryBGLScalarCarrierMap.{uR, uS, uCarrier} f x =
      ULift.up (ordinaryBGLScalarMap f x.down) :=
  scalarCarrierMap_apply_computed.{uR, uS, uCarrier} f x

end AlgebraicKTheory.StableGL

end
