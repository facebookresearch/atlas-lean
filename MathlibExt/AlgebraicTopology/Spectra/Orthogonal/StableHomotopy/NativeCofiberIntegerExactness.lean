/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeStableCofiberIntegerExactness
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.IntegerGroups

/-!
# The original orthogonal integer cofiber exactness row

The actual orthogonal integer groups restrict along the original sequential
index embedding. The generic native exactness row retains the same source,
Q-cofiber inclusion, and predecessor-degree connecting homomorphisms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.NativeStableCofiberIntegerMaps
open HomotopicalAlgebra.EnrichedProjective.Native.NativeStableCofiberIntegerExactness
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open CategoryTheory.Spectra.SpectrumIndexMaps
open scoped CGWH.modelCategory

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

namespace PointedCGWH.Spectra.NativeStableCofiberIntegerExactness

/-- Every orthogonal raw map has the same original native legs in all three integer positions. -/
theorem orthogonal_integer_cofiber_long_exact (q : ℤ) (F : Arrow OrthogonalCarrier.{u, v}) :
    Function.MulExact ((OrthogonalIntegerHomotopy.integerPiFunctor q).map F.hom).hom
        (inclusionInteger (j := sequentialOrthogonalOperatorIndexFunctor.{u, v}) q F).hom ∧
      Function.MulExact
        (inclusionInteger (j := sequentialOrthogonalOperatorIndexFunctor.{u, v}) q F).hom
        (connecting (j := sequentialOrthogonalOperatorIndexFunctor.{u, v}) q F).hom ∧
      Function.MulExact
        (connecting (j := sequentialOrthogonalOperatorIndexFunctor.{u, v}) q F).hom
        ((OrthogonalIntegerHomotopy.integerPiFunctor (q - 1)).map F.hom).hom :=
  integer_cofiber_long_exact (j := sequentialOrthogonalOperatorIndexFunctor.{u, v}) q F

end PointedCGWH.Spectra.NativeStableCofiberIntegerExactness
