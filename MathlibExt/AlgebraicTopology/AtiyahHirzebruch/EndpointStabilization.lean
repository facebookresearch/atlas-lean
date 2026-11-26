/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.SpectralObject.EndpointStabilization

/-!
# Endpoint comparisons for spectral-object windows

Let Y be a spectral object in an abelian category, indexed by a preorder with endpoints, and
let i₀ ≤ i₁ ≤ i₂ ≤ i₃. If H_Yⁿ⁺¹(⊥,i₀) and H_Yⁿ⁻¹(i₃,⊤) are zero, extending the outer cuts
induces an isomorphism E_Yⁿ(i₀ ≤ i₁ ≤ i₂ ≤ i₃) ≅ E_Yⁿ(⊥ ≤ i₁ ≤ i₂ ≤ ⊤).

The endpoint window is the cokernel of the inclusion between the images of H_Yⁿ(⊥,i₁) and
H_Yⁿ(⊥,i₂) in H_Yⁿ(⊥,⊤). Both comparisons are natural in maps of spectral objects satisfying
the same interval vanishings. This import makes the definitions in
MathlibExt.Algebra.Homology.SpectralObject.EndpointStabilization available in every integer
degree.
-/
