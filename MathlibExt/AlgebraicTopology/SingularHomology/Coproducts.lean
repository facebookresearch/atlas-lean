/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularSet.Coproducts
public import MathlibExt.AlgebraicTopology.SimplicialSet.ChainComplexColimits
public import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# Preservation of coproducts by fixed singular chain complex functor

The fixed-coefficient singular chain complex functor `TopCat ⥤ ChainComplex C`
is definitionally the composite `TopCat.toSSet ⋙ SSet.chainComplexFunctor.obj R`.
Since both factors preserve discrete colimits, so does the composite.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace AlgebraicTopology

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- For fixed coefficients `R : C`, the singular chain complex functor
`TopCat.{w} ⥤ ChainComplex C ℕ` preserves colimits of shape `Discrete J`
for any small discrete shape `J : Type w`.

The proof is the composite `TopCat.toSSet ⋙ (SSet.chainComplexFunctor.obj R)`:
`toSSet` preserves discrete colimits by `toSSetMapSigmaCofanIsColimit`,
and the simplicial chain functor preserves all small colimits by
`SSet.chainComplexFunctorObj_preservesColimitsOfShape`.  The composite
hence preserves discrete colimits. -/
instance singularChainComplexFunctorObj_preservesColimitsOfShape_discrete
    (R : C) (J : Type w) :
    PreservesColimitsOfShape (Discrete J)
      ((singularChainComplexFunctor (C := C)).obj R) := by
  have h : (singularChainComplexFunctor (C := C)).obj R =
      TopCat.toSSet.{w} ⋙ (SSet.chainComplexFunctor C).obj R := rfl
  rw [h]
  infer_instance

end AlgebraicTopology
