/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.InnerProductSpace.l2Space
import MathlibExt.Analysis.InnerProductSpace.SeparableHilbertIsoL2

/-!
# Tests for the isometric isomorphism of a separable Hilbert space with `ℓ²`

* An abstract infinite-dimensional separable Hilbert space admits a Hilbert
  basis indexed by `ℕ`.
* It is isometrically isomorphic to `ℓ²(ℕ)`, and the isomorphism preserves
  norms.
* `ℓ²(ℕ, ℝ)` itself admits a Hilbert basis indexed by `ℕ` (via the identity
  isomorphism), a sanity check on the conclusion type.
-/

open MathlibExt.Analysis.InnerProductSpace.SeparableHilbertIsoL2
open TopologicalSpace

namespace MathlibExtTest.Analysis.InnerProductSpace.SeparableHilbertIsoL2Tests

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- An infinite-dimensional separable Hilbert space admits a Hilbert basis
indexed by `ℕ`. -/
example [CompleteSpace H] [SeparableSpace H] (hInf : ¬FiniteDimensional 𝕜 H) :
    Nonempty (HilbertBasis ℕ 𝕜 H) :=
  exists_hilbertBasis_nat hInf

/-- An infinite-dimensional separable Hilbert space is isometrically
isomorphic to `ℓ²(ℕ)`. -/
example [CompleteSpace H] [SeparableSpace H] (hInf : ¬FiniteDimensional 𝕜 H) :
    Nonempty (H ≃ₗᵢ[𝕜] lp (fun _ : ℕ => 𝕜) 2) :=
  separable_hilbert_iso_l2 hInf

/-- The isomorphism with `ℓ²(ℕ)` preserves norms. -/
example [CompleteSpace H] [SeparableSpace H] (hInf : ¬FiniteDimensional 𝕜 H)
    (x : H) : ∃ e : H ≃ₗᵢ[𝕜] lp (fun _ : ℕ => 𝕜) 2, ‖e x‖ = ‖x‖ := by
  obtain ⟨e⟩ := separable_hilbert_iso_l2 (𝕜 := 𝕜) (H := H) hInf
  exact ⟨e, e.norm_map x⟩

/-- `ℓ²(ℕ, ℝ)` admits a Hilbert basis indexed by `ℕ`, via the identity
isomorphism. -/
example : Nonempty (HilbertBasis ℕ ℝ (lp (fun _ : ℕ => ℝ) 2)) :=
  ⟨HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ _)⟩

end MathlibExtTest.Analysis.InnerProductSpace.SeparableHilbertIsoL2Tests
