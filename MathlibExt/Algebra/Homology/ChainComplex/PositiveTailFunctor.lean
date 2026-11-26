/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import MathlibExt.Algebra.Homology.ChainComplex.PositiveTail
public import MathlibExt.Algebra.Homology.HomologicalComplexRescaling

/-!
# Colimits of positive tails and negated differentials

For a category C with zero morphisms, the positive-tail functor on nonnegative chain complexes
preserves colimits of every shape J for which C has J-shaped colimits: its degree-n evaluation
is evaluation of the original complex in degree n+1. In a preadditive category, negating the
differential of a complex of any shape also preserves such colimits, because its terms and
chain-map components remain unchanged.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe uC vC uJ vJ w

namespace ChainComplex

variable (C : Type uC) [Category.{vC} C] [HasZeroMorphisms C]

/-- Let C be a category with zero morphisms. The positive-tail functor sends a nonnegative chain
complex K to the complex with degree-n term K_{n+1} and differential d_K,n+2,n+1, and sends a
chain map f to its components f_{n+1}. -/
def positiveTailFunctor : ChainComplex C ℕ ⥤ ChainComplex C ℕ where
  obj K := positiveTail K
  map f := positiveTailMap f
  map_id K := positiveTailMap_id K
  map_comp f g := positiveTailMap_comp f g

/-- Let C be a category with zero morphisms, J a category, and assume that C has J-shaped colimits.
Then the positive-tail functor on natural-number-indexed chain complexes preserves J-shaped
colimits. The colimit in degree n is the colimit of the original complexes in degree n+1. -/
instance positiveTailFunctor_preservesColimitsOfShape
    (J : Type uJ) [Category.{vJ} J] [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (positiveTailFunctor C) where
  preservesColimit {F} :=
    { preserves {c} hc := ⟨HomologicalComplex.isColimitOfEval _ _ (fun n => by
        dsimp only [positiveTailFunctor]
        change IsColimit ((HomologicalComplex.eval C (ComplexShape.down ℕ) (n + 1)).mapCocone c)
        exact isColimitOfPreserves (HomologicalComplex.eval C (ComplexShape.down ℕ) (n + 1)) hc)⟩ }

end ChainComplex

namespace HomologicalComplex

variable (C : Type uC) [Category.{vC} C] [Preadditive C]
  {ι : Type w} {c : ComplexShape ι}

/-- Let C be preadditive, c a complex shape on an arbitrary index type, and J a category such that C
has J-shaped colimits. The functor on c-shaped complexes that replaces every differential d by
−d, while retaining the terms and morphism components, preserves J-shaped colimits. -/
instance negateFunctor_preservesColimitsOfShape
    (J : Type uJ) [Category.{vJ} J] [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (negateFunctor (C := C) (c := c)) where
  preservesColimit {F} :=
    { preserves {s} hs := ⟨HomologicalComplex.isColimitOfEval _ _ (fun n => by
        change IsColimit ((HomologicalComplex.eval C c n).mapCocone s)
        exact isColimitOfPreserves (HomologicalComplex.eval C c n) hs)⟩ }

end HomologicalComplex

namespace ChainComplex

variable (C : Type uC) [Category.{vC} C] [Preadditive C]

/-- Let C be a preadditive category. The negated positive-tail functor on nonnegative chain
complexes sends K to the complex with terms K_{n+1} and differential −d_K,n+2,n+1. Its maps have
the original components one degree higher. -/
abbrev negatedPositiveTailFunctor : ChainComplex C ℕ ⥤ ChainComplex C ℕ :=
  HomologicalComplex.negateFunctor ⋙ positiveTailFunctor C

end ChainComplex
