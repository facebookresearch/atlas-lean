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
ring universe u is independent of w,z. The canonical additive and homology-preservation
instances are supplied by the
imported exact tensor-bifunctor owner.
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

end ModuleCat
