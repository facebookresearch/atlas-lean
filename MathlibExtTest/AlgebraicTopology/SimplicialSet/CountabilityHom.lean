/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.CountabilityHom

/-!
# Whole-map encoding and countability of the full labelled family
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.CountabilityHom

/-- The entire Hom-set admits an injective natural-number encoding. -/
theorem hom_encoding (K X : SSet.{u}) [K.Finite] [Countable X.N] :
    ∃ e : (K ⟶ X) → ℕ, Function.Injective e := by
  have : Countable (K ⟶ X) := SSet.countable_hom_of_finite K X
  exact Countable.exists_injective_nat _

/-- The whole label/attaching-map family is countable with its original index retained. -/
theorem labelled_family (I : Type u) [Countable I] (K : I → SSet.{u})
    [∀ i, (K i).Finite] (X : SSet.{u}) [Countable X.N] :
    Countable (Σ i : I, K i ⟶ X) := by
  have : ∀ i : I, Countable (K i ⟶ X) := fun i => SSet.countable_hom_of_finite (K i) X
  infer_instance

end MathlibExtTest.AlgebraicTopology.SimplicialSet.CountabilityHom
