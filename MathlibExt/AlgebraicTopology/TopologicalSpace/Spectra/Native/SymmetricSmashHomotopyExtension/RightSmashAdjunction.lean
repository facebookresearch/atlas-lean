/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricSmashHomotopyExtension.TensorScalarCoefficient

/-!
# Right smash adjunction for symmetric spectra

Right smash with a fixed native symmetric spectrum is left adjoint to its function-spectrum
functor. A separate monoidal lemma transports an endpoint through supplied
tensor-coefficient and unit comparison isomorphisms, assuming their two compatibility
squares.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalCategory MonoidalClosed

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmashHomotopyExtension.Primitive

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]

/-- The actual unit and coefficient squares preserve the complete inverse-unit endpoint. -/
theorem endpointInterchange {S₀ S : C ⥤ C} (q : S₀ ⟶ S) (X Y : C)
    (c₀ : S₀.obj (X ⊗ Y) ≅ S₀.obj X ⊗ Y)
    (c : S.obj (X ⊗ Y) ≅ S.obj X ⊗ Y)
    (lX : S₀.obj X ≅ X) (lXY : S₀.obj (X ⊗ Y) ≅ X ⊗ Y)
    (hCoefficient : q.app (X ⊗ Y) ≫ c.hom = c₀.hom ≫ (q.app X ▷ Y))
    (hUnit : c₀.hom ≫ (lX.hom ▷ Y) = lXY.hom) :
    (lXY.inv ≫ q.app (X ⊗ Y)) ≫ c.hom = (lX.inv ≫ q.app X) ▷ Y := by
  have hInv : lXY.inv ≫ c₀.hom = lX.inv ▷ Y := by
    apply (cancel_mono (whiskerRightIso lX Y).hom).mp
    change (lXY.inv ≫ c₀.hom) ≫ (lX.hom ▷ Y) =
      (whiskerRightIso lX Y).inv ≫ (whiskerRightIso lX Y).hom
    rw [Category.assoc, hUnit]
    exact lXY.inv_hom_id.trans (whiskerRightIso lX Y).inv_hom_id.symm
  calc
    _ = lXY.inv ≫ c₀.hom ≫ (q.app X ▷ Y) := by
      rw [Category.assoc, hCoefficient]
    _ = (lX.inv ▷ Y) ≫ (q.app X ▷ Y) := by
      rw [← Category.assoc, hInv]
    _ = _ := (comp_whiskerRight _ _ _).symm



end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmashHomotopyExtension.Primitive

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmashHomotopyExtension

/-- The category of pointed symmetric spectra presented as enriched functors on the symmetric
operator index. -/
abbrev Carrier := EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  SymmetricSmash.monoidalCategory SymmetricSmash.symmetricCategory SymmetricSmash.monoidalClosed

/-- The actual arbitrary right-spectrum smash keeps its original native function right adjoint. -/
def rightSmashAdjunction (Y : Carrier.{u, v}) :
    MonoidalCategory.tensorRight Y ⊣ NativeOmegaPreparation.NativeSymmetricFunction.functor Y :=
  (SymmetricSmash.actualClosedAdjunction Y).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight Y)



end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmashHomotopyExtension
