/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Exact heterogeneous tensor functors with independent carrier universes.
module

public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.RingTheory.Flat.Basic

/-!
# Exact heterogeneous tensor functors

The original native linear tensor preserves homology when its fixed
factor is flat. The two module carrier universes and the original ring
universe remain independent. The proof uses the native linear-map
exactness criterion and the universe-independent native flat tensor theorem.
It requires neither a monoidal unit in the target carrier world nor Small.

These generic providers support an internally free fixed
polynomial module in the polynomial-tower construction. They do not
assume flatness of any original coefficient or original target algebra.
Flatness concerns only the actual fixed factor of each generic functor.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- Evaluate the existing first-input additivity at the actual fixed second factor. -/
instance tensorBifunctorAt_flip_obj_additive (N : ModuleCat.{w} R) :
    ((tensorBifunctorAt.{u, v, w} R).flip.obj N).Additive where
  map_add {M M' f g} :=
    NatTrans.congr_app ((tensorBifunctorAt.{u, v, w} R).map_add (f := f) (g := g)) N

/-- Tensoring on the left by an actual flat fixed factor preserves homology,
with independent original module worlds. -/
theorem tensorBifunctorAt_obj_preservesHomology (M : ModuleCat.{v} R) [Module.Flat R M] :
    ((tensorBifunctorAt.{u, v, w} R).obj M).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact Module.Flat.lTensor_exact M hS

/-- Tensoring on the right by an actual flat fixed factor preserves homology,
with independent original module worlds. -/
theorem tensorBifunctorAt_flip_obj_preservesHomology (N : ModuleCat.{w} R) [Module.Flat R N] :
    ((tensorBifunctorAt.{u, v, w} R).flip.obj N).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact Module.Flat.rTensor_exact N hS

end ModuleCat

end
