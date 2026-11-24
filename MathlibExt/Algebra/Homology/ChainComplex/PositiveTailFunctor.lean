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

Taking the positive tail and negating differentials preserve colimits.
Evaluation of a tail in degree `n` evaluates the original complex in degree
`n + 1`, while negating differentials leaves every evaluated object unchanged.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe uC vC uJ vJ w

namespace ChainComplex

variable (C : Type uC) [Category.{vC} C] [HasZeroMorphisms C]

/-- The actual positive-tail operation, using its already constructed chain maps. -/
def positiveTailFunctor : ChainComplex C ℕ ⥤ ChainComplex C ℕ where
  obj K := positiveTail K
  map f := positiveTailMap f
  map_id K := positiveTailMap_id K
  map_comp f g := positiveTailMap_comp f g

/-- Colimits of positive tails are computed by the native shifted evaluation family. -/
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

/-- Native differential negation preserves colimits because all evaluation functors are unchanged. -/
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

/-- The actual positive tail of the existing differential-negation functor. -/
abbrev negatedPositiveTailFunctor : ChainComplex C ℕ ⥤ ChainComplex C ℕ :=
  HomologicalComplex.negateFunctor ⋙ positiveTailFunctor C

end ChainComplex
