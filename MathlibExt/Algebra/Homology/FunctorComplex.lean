/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Homology.Functor

/-!
# Functors into complexes as complexes of functors

This file supplies the reverse direction to
`HomologicalComplex.complexOfFunctorsToFunctorToComplex`: a functor into
complexes is equivalently a complex in the corresponding functor category.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory CategoryTheory.Limits

universe vT uT vV uV w

namespace HomologicalComplex

variable {T : Type uT} [Category.{vT} T]
variable {V : Type uV} [Category.{vV} V] [HasZeroMorphisms V]
variable {ι : Type w} (c : ComplexShape ι)

/-- A functor to complexes gives a complex in the functor category. This is
the reverse direction to `complexOfFunctorsToFunctorToComplex`. -/
@[simps]
def functorToComplexToComplexOfFunctors :
    (T ⥤ HomologicalComplex V c) ⥤ HomologicalComplex (T ⥤ V) c where
  obj F :=
    { X := fun i => F ⋙ eval V c i
      d := fun i j => Functor.whiskerLeft F (dNatTrans V c i j)
      d_comp_d' := fun i j k _ _ => by
        ext t
        exact (F.obj t).d_comp_d i j k
      shape := fun i j h => by
        ext t
        exact (F.obj t).shape i j h }
  map {F G} η :=
    { f := fun i => Functor.whiskerRight η (eval V c i)
      comm' := fun i j _ => by
        ext t
        exact (η.app t).comm i j }
  map_id F := by
    ext i t
    simp
  map_comp η θ := by
    ext i t
    simp

instance : (functorToComplexToComplexOfFunctors
    (T := T) (V := V) c).PreservesZeroMorphisms where
  map_zero {F G} := by
    ext i t
    rfl

end HomologicalComplex
