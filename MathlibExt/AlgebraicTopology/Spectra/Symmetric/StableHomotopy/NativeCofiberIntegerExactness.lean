/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeStableCofiberIntegerExactness
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.StableHomotopy.IntegerGroups

/-!
# The original symmetric integer cofiber exactness row

The actual symmetric integer groups restrict along the original sequential
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

/-- Every symmetric raw map has the original native Q-cofiber sequence on its actual integer
groups. -/
theorem symmetric_integer_cofiber_long_exact (q : ℤ) (F : Arrow SymmetricCarrier.{u, v}) :
    Function.MulExact ((SymmetricIntegerHomotopy.integerPiFunctor q).map F.hom).hom
        (inclusionInteger (j := sequentialSymmetricOperatorIndexFunctor.{u, v}) q F).hom ∧
      Function.MulExact
        (inclusionInteger (j := sequentialSymmetricOperatorIndexFunctor.{u, v}) q F).hom
        (connecting (j := sequentialSymmetricOperatorIndexFunctor.{u, v}) q F).hom ∧
      Function.MulExact
        (connecting (j := sequentialSymmetricOperatorIndexFunctor.{u, v}) q F).hom
        ((SymmetricIntegerHomotopy.integerPiFunctor (q - 1)).map F.hom).hom :=
  integer_cofiber_long_exact (j := sequentialSymmetricOperatorIndexFunctor.{u, v}) q F

end PointedCGWH.Spectra.NativeStableCofiberIntegerExactness
