/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.Coproducts
public import MathlibExt.Algebra.Homology.ExactColimits
public import Mathlib.Algebra.Category.Grp.AB

/-!
# Singular homology preserves arbitrary coproducts

For `AddCommGrpCat`, the fixed-coefficient singular homology functor in each degree
preserves colimits of shape `Discrete J`.
-/

@[expose] public section

universe w

open CategoryTheory Limits AlgebraicTopology HomologicalComplex

namespace AlgebraicTopology

-- AB4 gives exactness of discrete colimits in `AddCommGrpCat`.
-- Hence `colim (Discrete J)` preserves finite limits.
-- As a left adjoint it also preserves finite colimits, yielding `PreservesHomology`.
-- Then `homologyFunctor` preserves `Discrete J` colimits, and composing with the
-- chain-level preservation gives the result.

noncomputable instance {J : Type w} :
    (colim (J := Discrete J) (C := AddCommGrpCat.{w})).PreservesHomology := by
  have : PreservesFiniteLimits (colim (J := Discrete J) (C := AddCommGrpCat.{w})) :=
    inferInstance
  have : PreservesFiniteColimits (colim (J := Discrete J) (C := AddCommGrpCat.{w})) :=
    inferInstance
  infer_instance

instance {J : Type w} (n : ℕ) :
    PreservesColimitsOfShape (Discrete J)
      (homologyFunctor AddCommGrpCat.{w} (ComplexShape.down ℕ) n) :=
  inferInstance

instance {J : Type w} (R : AddCommGrpCat.{w}) (n : ℕ) :
    PreservesColimitsOfShape (Discrete J)
      ((singularHomologyFunctor AddCommGrpCat.{w} n).obj R) := by
  have h : (singularHomologyFunctor AddCommGrpCat.{w} n).obj R =
      (singularChainComplexFunctor (C := AddCommGrpCat.{w})).obj R ⋙
        homologyFunctor AddCommGrpCat.{w} (ComplexShape.down ℕ) n := rfl
  rw [h]
  infer_instance

end AlgebraicTopology
