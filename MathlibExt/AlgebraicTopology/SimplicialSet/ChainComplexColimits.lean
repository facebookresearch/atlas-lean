/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

/-!
# Colimits of simplicial chain complexes

The unnormalized simplicial chain-complex functor with a fixed coefficient
object preserves colimits of shapes whose colimits exist in the simplex-value
universe. Degreewise preservation uses evaluation and coproducts of copies of
the coefficient object.
-/

@[expose] public section

universe w v u vJ uJ

open CategoryTheory Limits

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- For a fixed coefficient object `R : C`, the unnormalized simplicial chain complex
functor `(SSet.chainComplexFunctor C).obj R : SSet.{w} ⥤ ChainComplex C ℕ`
preserves colimits of every indexing shape `J : Type uJ` with
`HasColimitsOfShape J (Type w)`.

The proof reduces to degreewise preservation via
`HomologicalComplex.preservesColimitsOfShape_of_eval`. In degree `n`,
the composite `((chainComplexFunctor C).obj R ⋙ eval n)` is definitionally
`SSet.evaluation.obj (op ⦋n⦌) ⋙ sigmaConst.obj R`, i.e. the simplicial evaluation
functor followed by the coproduct-of-copies functor. The evaluation functor
preserves colimits pointwise in `SSet` (a functor category into `Type`), and
`sigmaConst.obj R` preserves all colimits using only `HasCoproducts.{w} C`
(`Preserves.SigmaConst`). Their composite hence preserves colimits, and the
evaluation lemmas give the result for chain complexes.

No `Abelian C`, exactness, AB4, homology objects, or colimits in `C` are needed.
Requires only `[Category C] [HasCoproducts.{w} C] [Preadditive C]` on `C` and
`HasColimitsOfShape J (Type w)` on the diagram shape. -/
instance chainComplexFunctorObj_preservesColimitsOfShape
    {J : Type uJ} [Category.{vJ} J] [HasColimitsOfShape J (Type w)] (R : C) :
    PreservesColimitsOfShape J ((chainComplexFunctor C).obj R) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ fun n => by
    have h :
        (chainComplexFunctor C).obj R ⋙ HomologicalComplex.eval C (ComplexShape.down ℕ) n =
          SSet.evaluation.obj (Opposite.op (SimplexCategory.mk n)) ⋙ sigmaConst.obj R :=
      rfl
    rw [h]
    infer_instance

end SSet
