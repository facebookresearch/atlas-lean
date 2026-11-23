/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import MathlibExt.Algebra.TensorProduct.Norm

open scoped TensorProduct

/-- Norm in a tensor product with the trivial Galois extension. -/
example (z : Polynomial ℚ ⊗[ℚ] ℚ) :
    algebraMap (Polynomial ℚ) (Polynomial ℚ ⊗[ℚ] ℚ) (Algebra.norm (Polynomial ℚ) z) =
      ∏ g : ℚ ≃ₐ[ℚ] ℚ,
        Algebra.TensorProduct.map (AlgHom.id ℚ (Polynomial ℚ)) (g : ℚ →ₐ[ℚ] ℚ) z :=
  Algebra.TensorProduct.algebraMap_norm_eq_prod_map_algEquiv ℚ ℚ (Polynomial ℚ) z
