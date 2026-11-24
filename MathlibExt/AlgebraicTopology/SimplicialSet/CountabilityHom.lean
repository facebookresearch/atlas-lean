/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Countability
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite

/-!
# Countability of maps from a finite simplicial set

A simplicial map is determined by its values on all nondegenerate simplices
of its domain. If that set is finite and the target has countably many
nondegenerate simplices, the corresponding finite product of degree sets is
countable, so the whole set of maps is countable.

This is the elementary finite-domain countability input for the labelled
attachment size argument.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet

/-- All simplicial maps from a finite domain into a countable simplicial set
form a countable set. -/
theorem countable_hom_of_finite (K X : SSet.{u}) [K.Finite] [Countable X.N] :
    Countable (K ⟶ X) := by
  have : ∀ s : K.N, Countable (X _⦋s.dim⦌) := fun s =>
    countable_obj_of_countable_N X (op ⦋s.dim⦌)
  let φ : (K ⟶ X) → ∀ s : K.N, X _⦋s.dim⦌ := fun f s => f.app _ s.simplex
  apply Function.Injective.countable (f := φ)
  intro f g h
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨m, δ, _, y, rfl⟩ := K.exists_nonDegenerate x
  have hy : f.app (op ⦋m⦌) y.val = g.app (op ⦋m⦌) y.val :=
    congrFun h (N.mk y.val y.property)
  have hf := ConcreteCategory.congr_hom (f.naturality δ.op) y.val
  have hg := ConcreteCategory.congr_hom (g.naturality δ.op) y.val
  change f.app (op ⦋n⦌) (K.map δ.op y.val) = X.map δ.op (f.app (op ⦋m⦌) y.val) at hf
  change g.app (op ⦋n⦌) (K.map δ.op y.val) = X.map δ.op (g.app (op ⦋m⦌) y.val) at hg
  exact hf.trans ((congrArg (X.map δ.op) hy).trans hg.symm)

end SSet
