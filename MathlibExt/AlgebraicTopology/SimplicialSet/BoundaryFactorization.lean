/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SmallObject
public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem

/-! # The boundary weak factorization system

The boundary small object argument gives functorial factorization between
monomorphisms and their right lifting class. This module records both
orthogonality equalities and every-map factorization in the native WFS API.
The functorial and per-map data remain the existing named boundary data.
-/

@[expose] public section

universe u

open CategoryTheory MorphismProperty

namespace SSet

/-- Monomorphisms and their right lifting class form a weak factorization
system on simplicial sets in every value universe. The factorization is
provided by the existing boundary functorial small object argument. -/
theorem isWeakFactorizationSystem_monomorphisms :
    IsWeakFactorizationSystem (monomorphisms SSet.{u})
      (monomorphisms SSet.{u}).rlp where
  rlp := rfl
  llp := by
    rw [rlp_monomorphisms, modelCategoryQuillen.llp_rlp_I]
  hasFactorization := by
    have : HasFunctorialFactorization (monomorphisms SSet.{u})
        (monomorphisms SSet.{u}).rlp :=
      modelCategoryQuillen.monoFunctorialFactorization
    infer_instance

end SSet
