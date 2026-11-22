/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.StabilizationTransformation
import MathlibExt.CategoryTheory.Monoidal.TensorPowerFunctor

/-!
# Function-spectrum delooping of symmetric spectra

Identifies the function spectrum from a free zero-sphere with the native right shift. Delooping preserves Omega spectra, and the comparison from an Omega spectrum to the scalar loop of its delooping is level weak. The first-degree specialization uses the canonical one-sphere coefficient isomorphism.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CGWH.modelCategory

namespace NativeOmegaRecovery.NativeSymmetricDelooping

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev J := PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} J.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}
attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK

/-- The full source function spectrum from the original free zero-sphere at r. -/
def delooping (r : I) : Carrier.{u, v} ⥤ Carrier.{u, v} :=
  NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v}
    (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} r)
      (S.{u, v}.functor.obj (𝟙_ I)))

/-- The whole original free-zero-sphere comparison retains its genuine native right shift. -/
def deloopingComparison (r : I) : delooping.{u, v} r ≅
    PointedCGWH.SymmetricShift.functor.{u, v} r :=
  NativeSymmetricFreeFunction.nativeFreeSphereUnitComparison r

/-- Every original zero-sphere function delooping retains the full Omega family. -/
theorem delooping_isOmega (r : I) (E : Carrier.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    Actual.SymmetricIsOmega ((delooping r).obj E) :=
  NativeOmegaIsoTransport.isOmega_obj_of_natIso Actual.symmetricFamily
    (deloopingComparison r) E (NativeSymmetricShiftOmega.shift_isOmega E hE r)

/-- The actual native scalar loop of that original function delooping. -/
def functionLoop (r : I) : Carrier.{u, v} ⥤ Carrier.{u, v} :=
  delooping r ⋙ cotensor (S.{u, v}.functor.obj r)

/-- Original adjoint maps and the original free comparison give the whole function-loop map. -/
def toFunctionLoop (r : I) : 𝟭 Carrier.{u, v} ⟶ functionLoop.{u, v} r :=
  comparisonNat r ≫
    (Functor.isoWhiskerRight (deloopingComparison r).symm
      (cotensor (S.{u, v}.functor.obj r))).hom

/-- Its whole source and target action uses those same two original natural transformations. -/
theorem toFunctionLoop_original (r : I) :
    toFunctionLoop.{u, v} r = comparisonNat r ≫
      (Functor.isoWhiskerRight (deloopingComparison r).symm
        (cotensor (S.{u, v}.functor.obj r))).hom := rfl

/-- The complete function-loop comparison is weak on every original Omega object. -/
theorem toFunctionLoop_weak (r : I) (E : Carrier.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    weakEquivalences Carrier.{u, v} ((toFunctionLoop r).app E) := by
  let j := (Functor.isoWhiskerRight (deloopingComparison r).symm
    (cotensor (S.{u, v}.functor.obj r))).hom.app E
  have hj : weakEquivalences Carrier.{u, v} j :=
    (weakEquivalences Carrier.{u, v}).of_isIso j
  exact (weakEquivalences Carrier.{u, v}).comp_mem (comparison r E) j
    (comparison_weak r E hE) hj

/-- The original first finite-bijection index is the cardinal one object. -/
abbrev firstIndex : I := Operad.SmallFinBijGroupoid.card 1

/-- The first original sphere coefficient is canonically the native one-sphere. -/
def firstCoefficientIso : S.{u, v}.functor.obj firstIndex ≅ PointedCGWH.sphereOne.{u, v} := by
  change CategoryTheory.MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} 1 ≅ _
  exact CategoryTheory.MonoidalCategory.TensorPower.tensorPowObjOneIso PointedCGWH.sphereOne

/-- Complete scalar cotensor contravariance carries the original first coefficient iso. -/
def firstLoopIso : cotensor (I := J.{u, v}) (S.{u, v}.functor.obj firstIndex) ≅
    cotensor (I := J.{u, v}) PointedCGWH.sphereOne.{u, v} :=
  (ScalarLeibniz.cotensorBifunctor (V := V.{u, v}) (A := J.{u, v})).mapIso
    firstCoefficientIso.symm.op

/-- The source's actual Omega delooping is the whole function spectrum from its first free S0. -/
def firstDelooping : Carrier.{u, v} ⥤ Carrier.{u, v} := delooping firstIndex

/-- The actual native one-sphere loop of the source's first function delooping. -/
def firstDeloopingLoop : Carrier.{u, v} ⥤ Carrier.{u, v} :=
  firstDelooping ⋙ cotensor PointedCGWH.sphereOne.{u, v}

/-- The genuine original comparison E to the native loop of its first-free-S0 function spectrum. -/
def delta : 𝟭 Carrier.{u, v} ⟶ firstDeloopingLoop.{u, v} :=
  toFunctionLoop firstIndex ≫ (Functor.isoWhiskerLeft firstDelooping firstLoopIso).hom

/-- The entire first function delooping is Omega for every original Omega E. -/
theorem firstDelooping_isOmega (E : Carrier.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    Actual.SymmetricIsOmega (firstDelooping.obj E) := delooping_isOmega firstIndex E hE

/-- The original comparison is natural in every full native transformation. -/
theorem delta_naturality {E E' : Carrier.{u, v}} (t : E ⟶ E') :
    t ≫ delta.app E' = delta.app E ≫ firstDeloopingLoop.map t := delta.naturality t

/-- The comparison to the actual native one-sphere loop is level weak on every Omega E. -/
theorem delta_weak (E : Carrier.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    weakEquivalences Carrier.{u, v} (delta.app E) := by
  let j := (Functor.isoWhiskerLeft firstDelooping firstLoopIso).hom.app E
  have hj : weakEquivalences Carrier.{u, v} j :=
    (weakEquivalences Carrier.{u, v}).of_isIso j
  exact (weakEquivalences Carrier.{u, v}).comp_mem ((toFunctionLoop firstIndex).app E) j
    (toFunctionLoop_weak firstIndex E hE) hj

end NativeOmegaRecovery.NativeSymmetricDelooping
