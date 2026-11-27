/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

import MathlibExt.CategoryTheory.CategoryCohomology.RoosExact

/-!
# Exactness clients for Roos complexes

The clients use an epimorphic degree map and the kernel universal property
for a cochain-map annihilator. Their hypotheses are the coefficient short
exact sequence and correctly sized exact products.
-/

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryCohomology

universe v₁ v₂ u₁ u₂

namespace RoosExactTests

variable {I : Type u₁} [Category.{v₁} I]
  {A : Type u₂} [Category.{v₂} A] [Abelian A]
  [HasProducts.{max u₁ v₁} A] [AB4StarOfSize.{max u₁ v₁} A]

/-- Every actual last degree map of a Roos image short exact sequence is epic. -/
example (S : ShortComplex (I ⥤ A)) (hS : S.ShortExact) (n : ℕ) :
    Epi (((roosComplexFunctor (I := I) (A := A)).map S.g).f n) := by
  have hR := roosComplexFunctor_map_shortExact S hS
  have hn := hR.map_of_exact (HomologicalComplex.eval A (ComplexShape.up ℕ) n)
  change Epi (((S.map (roosComplexFunctor (I := I) (A := A))).map
    (HomologicalComplex.eval A (ComplexShape.up ℕ) n)).g)
  exact hn.epi_g

/-- Native kernel lifting factors an actual cochain map through the mapped first arrow. -/
example (S : ShortComplex (I ⥤ A)) (hS : S.ShortExact) (Z : CochainComplex A ℕ)
    (u : Z ⟶ (roosComplexFunctor (I := I) (A := A)).obj S.X₂)
    (hu : u ≫ (roosComplexFunctor (I := I) (A := A)).map S.g = 0) :
    ((roosComplexFunctor_map_shortExact S hS).fIsKernel.lift
        (KernelFork.ofι u hu)) ≫ (roosComplexFunctor (I := I) (A := A)).map S.f = u := by
  exact (roosComplexFunctor_map_shortExact S hS).fIsKernel.fac
    (KernelFork.ofι u hu) WalkingParallelPair.zero

end RoosExactTests

end
