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
# A functor to complexes as a complex of functors

For a category T and a category V with zero morphisms, a functor F : T → HomologicalComplex V
c defines a complex of T-functors. Its degree-i object is t ↦ F(t)_i, and its differential has
component F(t).d i j.

Natural transformations are sent to their degreewise components. This construction preserves
zero morphisms and retains the independent category object, morphism and degree-index
universes.
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

/-- The functor from complex-valued diagrams to complexes of functors.

Send F to the complex with objects F followed by degree evaluation and differentials given by
its differential natural transformations. Send a diagram map to its degreewise natural
transformations. -/
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
