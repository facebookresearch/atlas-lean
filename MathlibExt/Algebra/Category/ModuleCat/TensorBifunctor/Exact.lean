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
# Homology preservation by flat factors in independent tensor universes

Let R be a commutative ring in universe u, and let the two module carrier universes be v,w,
independently of u. The tensor bifunctor sends M,N to M⊗_R N in universe max(v,w). For fixed N,
the functor M↦M⊗_R N is additive.

If the fixed left factor M is flat over R, then N↦M⊗_R N preserves exactness of short complexes
and therefore homology. If the fixed right factor N is flat, the same holds for M↦M⊗_R N.
Flatness concerns the stated fixed factor, and the results impose no relation between the scalar
universe and either carrier universe.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- Let R be commutative in universe u and N an R-module in universe w. On R-modules M in an
independent universe v, the functor M↦M⊗_R N, valued in universe max(v,w), is additive. For
parallel maps f,g, (f+g)⊗id_N=(f⊗id_N)+(g⊗id_N). -/
instance tensorBifunctorAt_flip_obj_additive (N : ModuleCat.{w} R) :
    ((tensorBifunctorAt.{u, v, w} R).flip.obj N).Additive where
  map_add {M M' f g} :=
    NatTrans.congr_app ((tensorBifunctorAt.{u, v, w} R).map_add (f := f) (g := g)) N

/-- Let R be commutative in universe u and M an R-module in universe v, flat over R. The functor
N↦M⊗_R N from R-modules in universe w to modules in max(v,w) preserves homology. It sends every
exact short complex to an exact short complex by flat tensor exactness. The ring and both
carrier universes are independent. -/
theorem tensorBifunctorAt_obj_preservesHomology (M : ModuleCat.{v} R) [Module.Flat R M] :
    ((tensorBifunctorAt.{u, v, w} R).obj M).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact Module.Flat.lTensor_exact M hS

/-- Let R be commutative in universe u and N an R-module in universe w, flat over R. The functor
M↦M⊗_R N from R-modules in universe v to modules in max(v,w) preserves homology. Exactness is
preserved by right tensoring with the fixed flat N, with no restriction relating u,v,w. -/
theorem tensorBifunctorAt_flip_obj_preservesHomology (N : ModuleCat.{w} R) [Module.Flat R N] :
    ((tensorBifunctorAt.{u, v, w} R).flip.obj N).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact Module.Flat.rTensor_exact N hS

end ModuleCat

end
