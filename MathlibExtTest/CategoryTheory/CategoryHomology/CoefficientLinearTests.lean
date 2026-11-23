/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.CoefficientLinear

public section

open CategoryTheory CategoryTheory.Limits

universe wS uJ vJ uV vV

namespace CategoryHomologyCoefficientLinearTests

variable {S : Type wS} [Semiring S]
  {J : Type uJ} [Category.{vJ} J]
  {V : Type uV} [Category.{vV} V] [Abelian V] [CategoryTheory.Linear S V]
  [HasCoproducts.{max uJ vJ} V]
  {M N : J ⥤ V} (f : M ⟶ N) (s : S)

theorem actual_bar_scalar :
    (CategoryHomology.coefficientBarSimplicialFunctor (C := J) (A := V)).map (s • f) =
      s • (CategoryHomology.coefficientBarSimplicialFunctor (C := J) (A := V)).map f := by
  exact Functor.map_smul _ s f

theorem actual_normalized_scalar :
    (CategoryHomology.normalizedCoefficientBarComplexFunctor (C := J) (A := V)).map (s • f) =
      s • (CategoryHomology.normalizedCoefficientBarComplexFunctor (C := J) (A := V)).map f := by
  exact Functor.map_smul _ s f

theorem actual_homology_scalar (n : ℕ) :
    (CategoryHomology.homologyWithCoefficientsFunctor (C := J) (A := V) n).map (s • f) =
      s • (CategoryHomology.homologyWithCoefficientsFunctor (C := J) (A := V) n).map f := by
  exact Functor.map_smul _ s f

end CategoryHomologyCoefficientLinearTests
