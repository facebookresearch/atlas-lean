/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.Homology.DGCyclicMixedModels

/-!
# Low bar degrees of the DG Hochschild and Connes differentials

The Hochschild differential has no faces in bar degree zero. Connes's operator is `N`, then the
extra degeneracy `s`, then `1 - t`, where `t = (-1)^n τ` is the signed rotation of `A^{⊗(n+1)}`:
the rotation carries no sign on `A^{⊗1}` and the sign `-1` on `A^{⊗2}`. In bar degree zero the
norm `N` is the identity, so `B = (1 + τ) ∘ s`; in bar degree one it is `1 + t`. These pin the
sign and composition conventions for every DG algebra `A`.
-/

namespace MathlibExtTest.Algebra.Homology.DGCyclicMixedModels

open CategoryTheory MonoidalCategory
open MathlibExt.Algebra.Homology.DGCyclicBarModels
open MathlibExt.Algebra.Homology.DGCyclicMixedModels

variable {k : Type} [CommRing k] (A : DGAlgebra k)

/-- Bar degree zero has no faces. -/
example (r : ℤ) : faceBlock A r 0 = 0 := rfl

/-- The rotation carries no sign on `A^{⊗1}` and the sign `-1` on `A^{⊗2}`. -/
example : signedRotation A 0 = (cyclicRotation A.X 0).hom := by
  simp [signedRotation]

example : signedRotation A 1 = -(cyclicRotation A.X 1).hom := by
  simp [signedRotation]

/-- In bar degree zero the cyclic norm is the identity. -/
example : cyclicNorm A 0 = 𝟙 _ := by
  simp [cyclicNorm, cyclicIterate]

/-- In bar degree one the cyclic norm is `1 + t`. -/
example : cyclicNorm A 1 = 𝟙 _ + signedRotation A 1 := by
  simp [cyclicNorm, cyclicIterate, Finset.sum_range_succ]

/-- In bar degree zero Connes's operator is `(1 + τ) ∘ s`. -/
example : connesBar A 0 = extraDegeneracy A 0 ≫ (𝟙 _ + (cyclicRotation A.X 1).hom) := by
  simp [connesBar, cyclicNorm, cyclicIterate, signedRotation]

end MathlibExtTest.Algebra.Homology.DGCyclicMixedModels
