/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeSphereUnitComparison
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.ShiftUnitComparison

/-!
# Function-spectrum unit isomorphisms

The native function-spectrum functor of the free object at the index tensor
unit and the coefficient tensor unit is naturally the identity. A second
comparison uses the sphere-sequence coefficient at that index. Their forward
and inverse natural transformations are the free-function comparisons
composed with the unit-shift right-unitor maps, in the displayed orders.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat

namespace NativeOmegaRecovery.NativeSymmetricFreeFunction

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal

/-- The actual function spectrum from the original free native unit at index zero
is naturally the identity, through the original free and index unit comparisons. -/
def nativeUnitComparison :
    NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v}
        (Free.object
          (PointedCGWH.symmetricOperatorObj.{u, v} (𝟙_ Operad.SmallFinBijGroupoid))
          (𝟙_ PointedCGWH.{u, v})) ≅
      𝟭 (EnrichedFunctorCat PointedCGWH.{u, v}
        PointedCGWH.SymmetricOperatorIndex.{u, v}) :=
  nativeFreeUnitComparison (𝟙_ Operad.SmallFinBijGroupoid) ≪≫ NativeSymmetricShiftUnit.comparison

/-- The same complete function unit at the original zero-sphere retains its
chosen sphere coefficient unit and original index right unitor. -/
def nativeSphereUnitComparison :
    NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v}
        (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} (𝟙_ Operad.SmallFinBijGroupoid))
          (PointedCGWH.sphereSequence.{u, v}.functor.obj
            (𝟙_ Operad.SmallFinBijGroupoid))) ≅
      𝟭 (EnrichedFunctorCat PointedCGWH.{u, v}
        PointedCGWH.SymmetricOperatorIndex.{u, v}) :=
  nativeFreeSphereUnitComparison (𝟙_ Operad.SmallFinBijGroupoid) ≪≫
    NativeSymmetricShiftUnit.comparison

/-- The whole forward function unit is the unchanged free comparison followed
by the original complete native index right-unitor transformation. -/
theorem nativeUnitComparison_hom :
    nativeUnitComparison.{u, v}.hom =
      (nativeFreeUnitComparison (𝟙_ Operad.SmallFinBijGroupoid)).hom ≫
        NativeSymmetricShiftUnit.homNat := rfl

/-- Its whole inverse is the original inverse index transformation followed
by the complete free-function inverse. -/
theorem nativeUnitComparison_inv :
    nativeUnitComparison.{u, v}.inv =
      NativeSymmetricShiftUnit.invNat ≫
        (nativeFreeUnitComparison (𝟙_ Operad.SmallFinBijGroupoid)).inv := rfl

/-- The full sphere unit retains the chosen sphere comparison and right-unitor map. -/
theorem nativeSphereUnitComparison_hom :
    nativeSphereUnitComparison.{u, v}.hom =
      (nativeFreeSphereUnitComparison (𝟙_ Operad.SmallFinBijGroupoid)).hom ≫
        NativeSymmetricShiftUnit.homNat := rfl

/-- Its full inverse retains those same original inverse maps in their correct order. -/
theorem nativeSphereUnitComparison_inv :
    nativeSphereUnitComparison.{u, v}.inv =
      NativeSymmetricShiftUnit.invNat ≫
        (nativeFreeSphereUnitComparison (𝟙_ Operad.SmallFinBijGroupoid)).inv := rfl

end NativeOmegaRecovery.NativeSymmetricFreeFunction
