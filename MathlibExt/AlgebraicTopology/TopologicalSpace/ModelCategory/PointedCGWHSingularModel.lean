/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.SingularMappingModelCompatibility

/-!
# Fibrations under the original pointed singular functor

The native pointed singular functor sends every fibration to a Kan
fibration and every trivial fibration to a Kan--Quillen trivial fibration.
The proof uses the original realized horn right class and the existing
weak-equivalence comparison on the same pointed map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory HomotopicalAlgebra
open scoped CGWH.modelCategory SSet.modelCategoryQuillen

namespace PointedCGWH.SingularModel
open SingularHomotopyGeometry

/-- The whole original singular functor preserves fibrations on every pointed map. -/
theorem preservesFibrations : PreservesFibrations singularFunctor.{u, v} := by
  intro X Y p hp
  change SSet.modelCategoryQuillen.J.rlp
    (TopCat.toSSet.map (CGWH.cgwhToTop.map p.right))
  apply TopCat.hornRLP_iff_toSSet_mem_J_rlp.mp
  change TopCat.realizedHornInclusions.rlp (CGWH.cgwhToTop.map p.right) at hp
  exact hp

/-- The same original singular functor preserves both classes of a trivial fibration. -/
theorem preservesTrivialFibrations : PreservesTrivialFibrations singularFunctor.{u, v} := by
  intro X Y p hp
  refine ⟨preservesFibrations p hp.1, ?_⟩
  change SSet.realizationWeakEquivalences (singularFunctor.map p)
  exact (HomotopicalAlgebra.EnrichedProjective.Native.SingularMapping.singularFunctor_weak_iff p).mpr hp.2

end PointedCGWH.SingularModel
