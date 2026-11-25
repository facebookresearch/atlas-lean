/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.Single

/-!
# Scalar linearity of homology functors

Short-complex homology, homological-complex homology and homotopy-category
homology are linear when the category has the specified scalar action.
The proofs transfer linearity through the short-complex and homotopy quotient
comparison functors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t u v

variable (R : Type t) [Semiring R]
  (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]
  {ι : Type*} (c : ComplexShape ι)

namespace HomologicalComplex

/-- Evaluation on a complex degree preserves the supplied scalars. -/
instance eval_linear (i : ι) : (eval C c i).Linear R where
  map_smul _ _ := rfl

/-- Complexes concentrated in one degree retain the supplied scalars. -/
instance single_linear [HasZeroObject C] [DecidableEq ι] (j : ι) :
    (single C c j).Linear R where
  map_smul {X Y} f r := by
    apply HomologicalComplex.hom_ext
    intro i
    by_cases hi : i = j
    · subst i
      simp only [single_map_f_self, HomologicalComplex.smul_f_apply,
        Linear.comp_smul, Linear.smul_comp]
    · exact (isZero_single_obj_X c j X i hi).eq_of_src _ _

/-- The three-degree short-complex functor is scalar-linear. -/
instance shortComplexFunctor'_linear (i j k : ι) :
    (shortComplexFunctor' C c i j k).Linear R where
  map_smul f r := by
    ext <;> rfl

/-- The prev/current/next short complex retains scalar linearity. -/
instance shortComplexFunctor_linear (i : ι) : (shortComplexFunctor C c i).Linear R := by
  dsimp only [shortComplexFunctor]
  infer_instance

/-- Complex homology maps preserve the supplied scalar action. -/
instance homologyFunctor_linear [CategoryWithHomology C] (i : ι) :
    (homologyFunctor C c i).Linear R where
  map_smul f r := by
    change CategoryTheory.ShortComplex.homologyMap
        ((shortComplexFunctor C c i).map (r • f)) =
      r • CategoryTheory.ShortComplex.homologyMap ((shortComplexFunctor C c i).map f)
    rw [Functor.map_smul, CategoryTheory.ShortComplex.homologyMap_smul]

end HomologicalComplex

namespace HomotopyCategory

/-- The homology functor on the homotopy category is linear. -/
instance homologyFunctor_linear [CategoryWithHomology C] (i : ι) :
    (homologyFunctor C c i).Linear R := by
  have : ((quotient C c) ⋙ homologyFunctor C c i).Linear R :=
    Functor.linear_of_iso R (homologyFunctorFactors C c i).symm
  exact (quotient C c).linear_of_full_essSurj_comp (homologyFunctor C c i)

end HomotopyCategory
