/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricSmashHomotopyExtension.RightSmashAdjunction

/-!
# Components of scalar-smash interchange

Identifies the components of the scalar-smash functor isomorphism with the represented
interchange map. The inverse comparison retains the same component isomorphisms and their
inverse arrows.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC

open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalCategory MonoidalClosed

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmashHomotopyExtension.Primitive

private theorem representedInterchange_app {C : Type uC} [Category.{vC} C]
    [MonoidalCategory C] (A : C) (S : C ⥤ C)
    (e : MonoidalCategory.tensorLeft A ≅ S) (X Y : C) :
    (CategoryTheory.TensorRepresentedInterchange.interchangeFunctorIso A S e Y).app X =
      CategoryTheory.TensorRepresentedInterchange.interchange A S e X Y := rfl

end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmashHomotopyExtension.Primitive

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmashHomotopyExtension

open SymmetricScalarSmash

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  SymmetricSmash.monoidalCategory SymmetricSmash.symmetricCategory SymmetricSmash.monoidalClosed

attribute [local irreducible] tensorScalarIso

/-- Every whole scalar-smash functor comparison has its unchanged original component. -/
theorem scalarSmashFunctorIso_app (T : PointedCGWH.{u, v}) (X Y : Carrier.{u, v}) :
    (scalarSmashFunctorIso T Y).app X = scalarSmashIso T X Y :=
  Primitive.representedInterchange_app (zeroFree T) (EnrichedFunctorCat.tensorLeft T)
    (tensorScalarIso T) X Y

/-- Every inverse whole scalar-smash comparison keeps the exact original inverse component. -/
theorem scalarSmashFunctorIso_symm_app_hom (T : PointedCGWH.{u, v}) (X Y : Carrier.{u, v}) :
    ((scalarSmashFunctorIso T Y).symm.app X).hom = (scalarSmashIso T X Y).inv :=
  congrArg (fun e => e.inv) (scalarSmashFunctorIso_app T X Y)




end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmashHomotopyExtension
