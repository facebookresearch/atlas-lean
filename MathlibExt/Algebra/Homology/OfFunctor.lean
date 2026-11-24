/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.Functor

@[expose] public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {J : Type*} [Category* J] {C : Type*} [Category* C]
variable [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}

/-- `ofFunctor` is the object-level inverse to `HomologicalComplex.asFunctor`: it turns a
diagram `K : J ⥤ HomologicalComplex C c` into a complex in the functor category
`HomologicalComplex (J ⥤ C) c`.  The degree `n` is the composite `K ⋙ eval C c n`, and
the differential is pointwise the differential of `K.obj j`, with naturality coming from
the fact that `K.map f` is a chain map. -/
def ofFunctor (K : J ⥤ HomologicalComplex C c) : HomologicalComplex (J ⥤ C) c where
  X n := K ⋙ eval C c n
  d i j :=
    { app := fun t => (K.obj t).d i j
      naturality := fun _ _ f => (K.map f).comm i j }
  shape _ _ h := by
    ext t
    exact (K.obj t).shape _ _ h
  d_comp_d' _ _ _ _ _ := by
    ext t
    exact (K.obj t).d_comp_d _ _ _

@[simp]
theorem ofFunctor_asFunctor (K : J ⥤ HomologicalComplex C c) :
    (ofFunctor K).asFunctor = K :=
  rfl

end HomologicalComplex
