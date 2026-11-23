/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.BarFunctoriality

/-!
# Morphism-inverting coefficients on a category with an initial object

If a coefficient functor sends every morphism to an isomorphism and the
indexing category has an initial object, then the coefficient functor is
naturally isomorphic to its constant value at that object.  Functoriality of
the normalized coefficient bar transports this to category homology.

No constant-coefficient vanishing result is claimed here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryHomology

variable {C : Type u₁} [Category.{v₁} C]
  {A : Type u₂} [Category.{v₂} A]
  [HasCoproducts.{max u₁ v₁} A]
  (M : CategoryTheory.Functor C A)
  [∀ {X Y : C} (f : X ⟶ Y), IsIso (M.map f)]

/-- A morphism-inverting functor on a category with an initial object is
naturally isomorphic to its constant value at that object. -/
noncomputable def constIsoOfIsInitial (i : C) (hi : IsInitial i) :
    (Functor.const C).obj (M.obj i) ≅ M :=
  NatIso.ofComponents (fun X ↦ asIso (M.map (hi.to X))) (fun {X Y} f ↦ by
    dsimp
    rw [Category.id_comp, ← M.map_comp]
    congr 1
    exact hi.hom_ext _ _)

variable [Abelian A]

/-- Category homology with morphism-inverting coefficients on an initial
category reduces to category homology with the corresponding constant
coefficient object. -/
noncomputable def homologyWithCoefficientsIsoConstOfIsInitial
    (i : C) (hi : IsInitial i) (n : ℕ) :
    homologyWithCoefficients ((Functor.const C).obj (M.obj i)) n ≅
      homologyWithCoefficients M n :=
  (homologyWithCoefficientsFunctor (C := C) (A := A) n).mapIso
    (constIsoOfIsInitial M i hi)

end CategoryTheory.CategoryHomology

end
