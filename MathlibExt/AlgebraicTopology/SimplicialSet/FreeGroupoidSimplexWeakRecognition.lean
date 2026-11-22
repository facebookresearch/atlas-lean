/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidSimplexGroupoidality
import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidSimplexSkeletalWeakComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.GroupoidalWeakClassComparison

/-!
# The original k-image weak-class classifier

Actual groupoidality of both k-image homotopy categories gives the genuine
groupoidal weak-class comparison on the same k-image map. Both original global
kComparison components are realization weak. Their original natural square
and full two-of-three return weakness of the original map.

The comparison kComparison:Id→kFunctor is distinct from the unit of the
kFunctor/kRightFunctor adjunction. Wrapped functors and Quillen properties
are subsequent constructions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace SSet.FreeGroupoidSimplex

/-- The same arbitrary original map is realization weak exactly when its actual
k image is categorical weak; no original endpoint hypothesis is required. -/
theorem categoricalEquivalences_kFunctor_map_iff
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    categoricalEquivalences (kFunctor.map f) ↔ realizationWeakEquivalences f := by
  let _ : IsGroupoid (kFunctor.obj X).HomotopyCategory :=
    kFunctor_obj_isGroupoid_homotopyCategory X
  let _ : IsGroupoid (kFunctor.obj Y).HomotopyCategory :=
    kFunctor_obj_isGroupoid_homotopyCategory Y
  have hnat : f ≫ kComparison.app Y = kComparison.app X ≫ kFunctor.map f := by
    simpa only [CategoryTheory.Functor.id_map] using kComparison.naturality f
  calc
    categoricalEquivalences (kFunctor.map f) ↔
        realizationWeakEquivalences (kFunctor.map f) :=
      categoricalEquivalences_iff_realizationWeakEquivalences_of_isGroupoid (kFunctor.map f)
    _ ↔ realizationWeakEquivalences (kComparison.app X ≫ kFunctor.map f) :=
      (realizationWeakEquivalences.precomp_iff (kComparison.app X) (kFunctor.map f)
        (kComparison_realizationWeak X)).symm
    _ ↔ realizationWeakEquivalences (f ≫ kComparison.app Y) := by
      rw [hnat]
    _ ↔ realizationWeakEquivalences f :=
      realizationWeakEquivalences.postcomp_iff f (kComparison.app Y)
        (kComparison_realizationWeak Y)

end SSet.FreeGroupoidSimplex
