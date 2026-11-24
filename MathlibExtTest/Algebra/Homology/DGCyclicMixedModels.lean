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

On the bar-degree-`n` summand the total Hochschild differential is `(-1)^n d + b`, with no faces in
bar degree zero, and the total Connes map sends that summand to bar degree `n + 1` by its block.
That block is `N`, then the extra degeneracy `s`, then `1 - t`, where `t = (-1)^n τ` is the signed
rotation of `A^{⊗(n+1)}`: the rotation carries no sign on `A^{⊗1}` and the sign `-1` on `A^{⊗2}`.
In bar degree zero the norm `N` is the identity, so `B = (1 + τ) ∘ s`; in bar degree one it is
`1 + t`. These pin the sign and composition conventions for every DG algebra `A`.
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

/-- On the bar-degree-`n` summand the total Hochschild differential is `(-1)^n d + b`. -/
example (r : ℤ) (n : ℕ) (x : HochschildSummand A r n) :
    hochschildDifferential A r (includeHochschild A r n x) =
      ((-1 : ℤ) ^ n • internalBlock A r n + faceBlock A r n) x :=
  DirectSum.toModule_lof (M := HochschildSummand A r) (N := HochschildValues A (r + 1))
    (φ := fun m => (-1 : ℤ) ^ m • internalBlock A r m + faceBlock A r m) k n x

/-- The total Connes map sends the bar-degree-`n` summand to the bar-degree-`n + 1` summand by the
block `connesBar A n`, lowering the cohomological degree by one. -/
example (r : ℤ) : connesDifferential A r =
    DirectSum.toModule k ℕ (HochschildValues A (r - 1)) (fun n =>
      (includeHochschild A (r - 1) (n + 1)).comp
        ((degreeCast (tensorPower A.X (n + 2)) (by omega)).comp
          ((connesBar A n).f (r + (n : ℤ))).hom)) := rfl

end MathlibExtTest.Algebra.Homology.DGCyclicMixedModels
