/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.ConstructionDataComparison

/-!
# Production bridge to the exact closed original-cardinal middle functors

Both original equations follow from the complete constructed source packets
and their exact caller-bottom comparisons. This module imports production
data providers and retains the original cardinal, inverse and entire Z.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC

open CategoryTheory HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.NativePresentation.ClosedData

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  {C : Type uC} [Category.{vC} C]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The entire given source I middle uses the exact constructed native original data. -/
theorem cofibrant_middle_functor_closed
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (NativePresentation.cofibrantFactorizationData e).Z =
      e.functor.mapArrow ⋙ (Native.Construction.cofibrantFactorizationData (A := A)).Z ⋙
        e.inverse :=
  (Construction.cofibrantFactorizationData_Z_eq_existing e).symm.trans
    (Construction.cofibrantFactorizationData_Z e)

/-- The entire given source J middle uses the exact constructed native original data. -/
theorem fibrant_middle_functor_closed
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (NativePresentation.fibrantFactorizationData e).Z =
      e.functor.mapArrow ⋙ (Native.Construction.fibrantFactorizationData (A := A)).Z ⋙
        e.inverse :=
  (Construction.fibrantFactorizationData_Z_eq_existing e).symm.trans
    (Construction.fibrantFactorizationData_Z e)

end HomotopicalAlgebra.EnrichedProjective.NativePresentation.ClosedData
