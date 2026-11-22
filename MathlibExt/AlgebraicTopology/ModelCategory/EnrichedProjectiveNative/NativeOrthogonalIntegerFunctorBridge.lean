/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeStableCofiberIntegerMaps
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.IntegerGroups

/-!
# The original orthogonal integer functor and its native restriction

The full functor equality identifies the generic native restriction with
its original orthogonal integer functor at every signed integer degree.
It preserves all original object and arrow maps and requires no model or
fiber-comparison premise.
-/

set_option autoImplicit false
noncomputable section
universe u v

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
namespace OriginalFiberNullity

/-- The complete restricted integer functor is the actual original orthogonal integer functor. -/
theorem orthogonalIntegerPiFunctor_eq_actual (q : ℤ) :
    NativeStableCofiberIntegerMaps.integerPiFunctor
        CategoryTheory.Spectra.SpectrumIndexMaps.sequentialOrthogonalOperatorIndexFunctor q =
      Actual.OrthogonalIntegerHomotopy.integerPiFunctor q := rfl

end OriginalFiberNullity
end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
