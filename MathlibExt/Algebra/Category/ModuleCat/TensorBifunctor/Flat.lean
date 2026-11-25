/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor.Exact

/-!
# Compatibility names for the exact tensor bifunctor

These names abbreviate the tensor bifunctor and its `Exact` results.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe u w z

namespace ModuleCat

variable (k : Type u) [CommRing k] (M : ModuleCat.{w} k)

/-- Compatibility abbreviation for the canonical fixed-right tensor functor. -/
abbrev tensorRightFunctorAt : ModuleCat.{z} k ⥤ ModuleCat.{max w z} k :=
  (tensorBifunctorAt.{u, z, w} k).flip.obj M

/-- Compatibility spelling; the canonical flip instance supplies additivity. -/
abbrev tensorRightFunctorAt_additive : (tensorRightFunctorAt.{u, w, z} k M).Additive :=
  tensorBifunctorAt_flip_obj_additive.{u, z, w} k M

/-- Compatibility spelling for the canonical left-factor exactness provider. -/
abbrev tensorLeftAt_preservesHomology [Module.Flat k M] :
    ((tensorBifunctorAt.{u, w, z} k).obj M).PreservesHomology :=
  tensorBifunctorAt_obj_preservesHomology.{u, w, z} k M

/-- Compatibility spelling for the canonical right-factor exactness provider. -/
abbrev tensorRightAt_preservesHomology [Module.Flat k M] :
    (tensorRightFunctorAt.{u, w, z} k M).PreservesHomology :=
  tensorBifunctorAt_flip_obj_preservesHomology.{u, z, w} k M

end ModuleCat
