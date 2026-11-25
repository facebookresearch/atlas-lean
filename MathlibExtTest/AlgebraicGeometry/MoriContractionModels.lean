/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.MoriContractionModels

/-!
# Tests for small morphisms
-/

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.MoriContractionModels

/-- A small morphism has a source of dimension at least two: the codimension bound
is stated without natural-number subtraction, so it is not truncated in dimension one. -/
example {Y X : Scheme} (f : Y ⟶ X) : ¬ IsSmall f 1 := by
  rintro ⟨-, ⟨y, hy⟩, hdim, -, -⟩
  have : Nonempty (TopologicalSpace.IrreducibleCloseds (exceptionalLocus f)) :=
    ⟨⟨closure {⟨y, hy⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim (exceptionalLocus f) :=
    Order.krullDim_nonneg
  have h2 : (0 : WithBot ℕ∞) + 2 ≤ ((1 : ℕ) : WithBot ℕ∞) := le_trans (by gcongr) hdim
  norm_num at h2
