/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryCohomology.RoosExact
public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.FromNonnegativeCochains

/-!
# The cohomological Roos δ-functor

Exact products make a short exact sequence of coefficient diagrams into a
short exact sequence of Roos cochain complexes. Their cohomology and connecting
maps form a cohomological δ-functor. The comparison with nonnegative cochain
homology identifies both its degree functors and its connecting morphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryCohomology

variable {I : Type u₁} [Category.{v₁} I]
  {A : Type u₂} [Category.{v₂} A] [Abelian A]
  [HasProducts.{max u₁ v₁} A] [AB4StarOfSize.{max u₁ v₁} A]

/-- The full Roos complexes form a cohomological δ-functor. -/
def roosCohomologicalDeltaFunctor : CohomologicalDeltaFunctor (I ⥤ A) A :=
  CohomologicalDeltaFunctor.ofNonnegativeCochains (I ⥤ A) A
    (roosComplexFunctor (I := I) (A := A))
    (fun S ↦ roosComplexFunctor_map_shortExact S.obj S.property)

/-- Its degree values are the homology of the given Nat Roos complexes. -/
def roosDeltaFunctorHomologyIso (n : ℕ) :
    (roosCohomologicalDeltaFunctor (I := I) (A := A)).T n ≅
      roosComplexFunctor ⋙ HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n :=
  CohomologicalDeltaFunctor.ofNonnegativeCochainsHomologyIso (I ⥤ A) A
    roosComplexFunctor (fun S ↦ roosComplexFunctor_map_shortExact S.obj S.property) n

/-- The Roos connecting map transports the Nat boundary. -/
theorem roosCohomologicalDeltaFunctor_connecting_app (n : ℕ)
    (S : ShortComplex.ShortExactSequences (I ⥤ A)) :
    (roosDeltaFunctorHomologyIso (I := I) (A := A) n).hom.app S.obj.X₃ ≫
        (roosComplexFunctor_map_shortExact S.obj S.property).δ n (n + 1) (by rfl) =
      ((roosCohomologicalDeltaFunctor (I := I) (A := A)).connecting n).app S ≫
        (roosDeltaFunctorHomologyIso (I := I) (A := A) (n + 1)).hom.app S.obj.X₁ :=
  CohomologicalDeltaFunctor.ofNonnegativeCochains_connecting_app (I ⥤ A) A
    roosComplexFunctor (fun S ↦ roosComplexFunctor_map_shortExact S.obj S.property) n S

end CategoryTheory.CategoryCohomology

end
