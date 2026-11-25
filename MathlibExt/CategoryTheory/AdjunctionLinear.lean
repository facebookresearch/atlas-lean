/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Linearity of a left adjoint to a linear functor

The proof uses the naturality of the unit.
This lemma introduces no chosen comparison or linearity assumption on the
left adjoint.
-/

@[expose] public section

namespace MathlibExt.CategoryTheory

open _root_.CategoryTheory

variable (R : Type*) [Ring R]
  {C D : Type*} [Category C] [Category D]
  [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
  {F : C ⥤ D} {G : D ⥤ C}

/-- A left adjoint of an `R`-linear functor is `R`-linear. -/
theorem linear_leftAdjoint (adj : F ⊣ G) [Functor.Linear R G] :
    Functor.Linear R F where
  map_smul f r := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_unit, adj.homEquiv_unit, G.map_smul,
      Linear.comp_smul]
    have hf := adj.unit.naturality f
    have hr := adj.unit.naturality (r • f)
    dsimp only [Functor.id_map, Functor.comp_map] at hf hr
    rw [← hr, ← hf, Linear.smul_comp]

end MathlibExt.CategoryTheory
