/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Limits.Preserves.Retract
public import MathlibExt.AlgebraicTopology.SimplicialSet.NormalizedFunctor
public import MathlibExt.AlgebraicTopology.SimplicialSet.ChainComplexColimits

/-!
# Colimits of normalized simplicial chain complexes

The normalized simplicial chain-complex functor is exhibited as a retract of
the unnormalized chain-complex functor. For a preadditive coefficient category
with the required coproducts, this retract transports preservation of colimits
of a given shape from the unnormalized functor to the normalized one.
-/

@[expose] public section

universe w v u vJ uJ

open CategoryTheory Limits

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- The normalized chain-complex functor is a retract of the unnormalized one. -/
noncomputable def normalizedChainComplexRetract (R : C) :
    Retract (SSet.normalizedChainComplexFunctorObj (C := C) R)
      ((SSet.chainComplexFunctor C).obj R) where
  i := SSet.fromNormalizedChainComplexNatTrans (C := C) R
  r := SSet.toNormalizedChainComplexNatTrans (C := C) R
  retract := by
    ext X n
    exact SSet.fromNormalizedChainComplex_f_toNormalizedChainComplex_f X R n

/-- Normalized simplicial chains preserve all colimits preserved by
`Type w` for the indexing shape. -/
instance normalizedChainComplexFunctorObj_preservesColimitsOfShape
    {J : Type uJ} [Category.{vJ} J] [HasColimitsOfShape J (Type w)] (R : C) :
    PreservesColimitsOfShape J
      (SSet.normalizedChainComplexFunctorObj (C := C) R) :=
  preservesColimitsOfShape_of_retract (normalizedChainComplexRetract (C := C) R)

end SSet
