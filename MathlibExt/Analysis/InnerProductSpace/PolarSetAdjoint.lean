/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.PolarSet
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

namespace MetaMathlibExt

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **Polar of a linear image.** Let $E$ and $F$ be finite-dimensional real inner product spaces,
let $f : E \to F$ be a linear map with adjoint $f^* : F \to E$, and let $K \subseteq E$. Writing
$S^\circ$ for the polar of a set $S$, we have $(f(K))^\circ = (f^*)^{-1}(K^\circ)$, that is,
$y \in F$ lies in the polar of $f(K)$ if and only if $f^*(y)$ lies in the polar of $K$.

This is the set-theoretic transformation used by the Mahler volume product. -/
theorem polarSet_image_eq_preimage_adjoint (f : E →ₗ[ℝ] F) (K : Set E) :
    polarSet (f '' K) = f.adjoint ⁻¹' polarSet K := by
  ext y
  change (∀ x ∈ f '' K, inner ℝ x y ≤ 1) ↔ ∀ x ∈ K, inner ℝ x (f.adjoint y) ≤ 1
  constructor
  · intro hy x hx
    rw [LinearMap.adjoint_inner_right]
    exact hy (f x) ⟨x, hx, rfl⟩
  · intro hy x hx
    rcases hx with ⟨z, hz, rfl⟩
    rw [← LinearMap.adjoint_inner_right]
    exact hy z hz

end MetaMathlibExt
