/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# complex functors preserve the colimits preserved by their coefficient functor

The proof is the degree-evaluation criterion. This is useful
for cokernel and cyclic quotient comparisons under the module universe
lift. No new complex, colimit or exactness engine is constructed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D J : Type*} [Category* C] [Category* D] [Category* J]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasColimitsOfShape J C]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesColimitsOfShape J F]
  {I : Type*} (c : ComplexShape I)

/-- The induced complex functor preserves the coefficient functor's colimits degreewise. -/
instance mapHomologicalComplex_preservesColimitsOfShape_of_eval :
    PreservesColimitsOfShape J (F.mapHomologicalComplex c) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun n => by
    change PreservesColimitsOfShape J (HomologicalComplex.eval C c n ⋙ F)
    infer_instance)

end CategoryTheory.Functor
