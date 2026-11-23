/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.BarSimplicial
public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedFiberHomology

/-!
# Category bar on the homology of cofibered fibers

The homology groups of the strict fibers of a cofibered functor form a
coefficient functor on the base.  This file applies the normalized category
bar construction to that coefficient functor and exposes the resulting
objects

`H_p(S; R ↦ H_q(Fiber(p,R)))`.

These are the expected entries of a future spectral sequence, but no page,
differential, abutment, or convergence statement is made here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.IsCofibered

variable {S : Type u₁} {X : Type u₂}
  [Category.{v₁} S] [Category.{v₂} X]
  {p : CategoryTheory.Functor X S} [p.IsCofibered]
  (A : Type u₃) [Category.{v₃} A] [Abelian A]
  [HasCoproducts.{max u₂ v₂} A]
  [HasCoproducts.{max u₁ v₁} A]
  (R : A)

/-- Simplicial category bar on degree-`q` homology of the strict fibers. -/
noncomputable def fiberHomologyBarSimplicial (q : ℕ) : SimplicialObject A :=
  CategoryHomology.coefficientBarSimplicial
    (fiberHomologyFunctor (p := p) A R q)

@[simp]
theorem fiberHomologyBarSimplicial_obj (q n : ℕ) :
    (fiberHomologyBarSimplicial (p := p) A R q).obj
        (Opposite.op (SimplexCategory.mk n)) =
      CategoryHomology.coefficientBarObj
        (fiberHomologyFunctor (p := p) A R q) n :=
  CategoryHomology.coefficientBarSimplicial_obj _ n

/-- Normalized category bar complex on degree-`q` homology of the strict
fibers. -/
noncomputable def fiberHomologyBarComplex (q : ℕ) : ChainComplex A ℕ :=
  CategoryHomology.normalizedCoefficientBarComplex
    (fiberHomologyFunctor (p := p) A R q)

/-- Category homology in degree `pDegree` with coefficients in degree
`qDegree` homology of the strict fibers. -/
noncomputable abbrev fiberHomologyCategoryHomology
    (pDegree qDegree : ℕ) : A :=
  CategoryHomology.homologyWithCoefficients
    (fiberHomologyFunctor (p := p) A R qDegree) pDegree

end CategoryTheory.Functor.IsCofibered

end
