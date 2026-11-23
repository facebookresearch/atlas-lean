/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.SingularHomology.IntegerData

/-!
# Exactness of integer-graded singular homology
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- Integer-graded singular homology has an exact homology sequence for every pair. -/
noncomputable instance singularHomologyIntData_isExact (R : C) :
    (singularHomologyIntData C R).IsExact where
  exact_pairSequence n P := by
    simp only [TopPair.HomologyTheoryData.pairSequence,
      singularHomologyIntData_boundary,
      singularHomologyIntData_subspaceMap,
      singularHomologyIntData_toRelative,
      relativeSingularBoundaryIntRel_app]
    exact ComposableArrows.exact_of_δ₀
      ((singularPairShortComplexIntFunctor_obj_shortExact C R P).homology_exact₁
        n (n - 1) (by simp)).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        ((singularPairShortComplexIntFunctor_obj_shortExact C R P).homology_exact₂
          (n - 1)).exact_toComposableArrows
        ((singularPairShortComplexIntFunctor_obj_shortExact C R P).homology_exact₃
          (n - 1) ((n - 1) - 1) (by simp)).exact_toComposableArrows)

end AlgebraicTopology
