/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.CofiberIntegerExactness

/-!
# The original sequential integer cofiber exactness row

The three original integer cofiber positions use the sequential source map,
Q-counit inclusion, and chosen-boundary connecting map. This corollary combines
the existing sequential exactness statements on those same homomorphisms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy
open scoped CGWH.modelCategory

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

namespace PointedCGWH.Spectra.NativeStableCofiberIntegerExactness

/-- Every sequential raw map has all three original integer cofiber exactness positions. -/
theorem sequential_integer_cofiber_long_exact (q : ℤ)
    (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    Function.MulExact ((integerStablePiFunctor q).map F.hom).hom
        (CofiberIntegerSequence.inclusionInteger q
          F).hom ∧
      Function.MulExact
        (CofiberIntegerSequence.inclusionInteger q
          F).hom
        (CofiberConnectingIntegerPiGeometry.connecting q F).hom ∧
      Function.MulExact
        (CofiberConnectingIntegerPiGeometry.connecting q F).hom
        ((integerStablePiFunctor (q - 1)).map F.hom).hom :=
  ⟨CofiberIntegerExactnessGeometry.source_inclusion_mulExact q F,
    CofiberIntegerExactnessGeometry.inclusion_connecting_mulExact q F,
    CofiberIntegerExactnessGeometry.connecting_source_mulExact q F⟩

end PointedCGWH.Spectra.NativeStableCofiberIntegerExactness
