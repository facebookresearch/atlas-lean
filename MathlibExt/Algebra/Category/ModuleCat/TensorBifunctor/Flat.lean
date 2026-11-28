/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor.Exact

/-!
# Fixed-factor tensor functors and flat homology preservation

Let k be a commutative ring in universe u and M a coefficient module in universe w. For varying
modules X in an independent universe z, the right-factor functor is X↦X⊗_k M, with output
carrier universe max(w,z). It is additive in every module map.

If M is flat over k, both fixed-factor functors X↦M⊗_k X and X↦X⊗_k M preserve homology. The
ring universe u is independent of w,z. The declarations provide these functors and their
additive and exact tensor properties.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe u w z

namespace ModuleCat

variable (k : Type u) [CommRing k] (M : ModuleCat.{w} k)

/-- Let k be commutative in universe u and M a k-module in universe w. This functor sends a k-module
X in universe z to X⊗_k M in universe max(w,z), and a morphism f to f⊗id_M. The three universes
are independent. -/
abbrev tensorRightFunctorAt : ModuleCat.{z} k ⥤ ModuleCat.{max w z} k :=
  (tensorBifunctorAt.{u, z, w} k).flip.obj M

/-- For a commutative ring k in universe u and fixed module M in w, the functor X↦X⊗_k M on modules
in z is additive: it preserves sums of parallel morphisms. Its target carrier universe is
max(w,z), and no flatness hypothesis is required for additivity. -/
abbrev tensorRightFunctorAt_additive : (tensorRightFunctorAt.{u, w, z} k M).Additive :=
  tensorBifunctorAt_flip_obj_additive.{u, z, w} k M

/-- Let k be commutative in universe u and M a flat k-module in universe w. For modules X in
universe z, the functor X↦M⊗_k X preserves homology, with outputs in max(w,z). The property
follows from flat tensor exactness and has no smallness condition on k. -/
abbrev tensorLeftAt_preservesHomology [Module.Flat k M] :
    ((tensorBifunctorAt.{u, w, z} k).obj M).PreservesHomology :=
  tensorBifunctorAt_obj_preservesHomology.{u, w, z} k M

/-- Let k be commutative in universe u and M a flat k-module in universe w. The functor X↦X⊗_k M
from modules in z to modules in max(w,z) preserves homology. The fixed right factor is the flat
module, and the scalar and carrier universes are independent. -/
abbrev tensorRightAt_preservesHomology [Module.Flat k M] :
    (tensorRightFunctorAt.{u, w, z} k M).PreservesHomology :=
  tensorBifunctorAt_flip_obj_preservesHomology.{u, z, w} k M

end ModuleCat
