/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Countability

/-!
# Countability under monomorphisms of simplicial sets

A monomorphism preserves nondegeneracy and is injective in every degree.
The actual dimension-preserving map of total nondegenerate simplices is
therefore injective. Countability descends along this injection.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet

/-- A monomorphism into a simplicial set with countably many total
nondegenerate simplices has countably many total nondegenerate simplices. -/
theorem countable_N_of_mono {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] [Countable Y.N] :
    Countable X.N := by
  apply Function.Injective.countable
    (f := fun s : X.N ↦ N.mk (i.app (op ⦋s.dim⦌) s.simplex)
      ((nonDegenerate_iff_of_mono i s.simplex).mpr s.nonDegenerate))
  intro s t h
  obtain ⟨n, ⟨x, hx⟩, rfl⟩ := s.mk_surjective
  obtain ⟨m, ⟨y, hy⟩, rfl⟩ := t.mk_surjective
  have hdim : n = m := congrArg (fun q : Y.N ↦ q.dim) h
  subst m
  have himage : i.app (op ⦋n⦌) x = i.app (op ⦋n⦌) y :=
    (S.ext_iff _ _).mp ((N.ext_iff _ _).mp h)
  have hxy : x = y := injective_of_mono (i.app (op ⦋n⦌)) himage
  subst y
  rfl

end SSet
