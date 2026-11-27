/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Functorial K-injective resolutions

A functorial K-injective resolution of the cochain complexes of an abelian category: an
endofunctor of cochain complexes with a natural quasi-isomorphism from the identity, whose values
are K-injective. Applying an additive functor termwise to these resolutions computes its right
derived functor, so the record is the common input of the derived constructions on the
prismatic and syntomic sites.
-/

@[expose] public section

namespace MathlibExt

open CategoryTheory

universe u v

/-- A functorial K-injective resolution of the cochain complexes of `M`. -/
structure FunctorialKInjective (M : Type u) [Category.{v} M] [Abelian M] where
  functor : CochainComplex M ℤ ⥤ CochainComplex M ℤ
  unit : 𝟭 _ ⟶ functor
  quasiIso : ∀ K, QuasiIso (unit.app K)
  kInjective : ∀ K, (functor.obj K).IsKInjective

end MathlibExt
