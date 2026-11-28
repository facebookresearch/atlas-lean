/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Charpoly.Transpose

#check @LinearMap.charpoly_dualTranspose

-- The transpose of an endomorphism of `ℤ²` has the same characteristic polynomial.
example (f : Module.End ℤ (Fin 2 → ℤ)) :
    (Module.Dual.transpose (R := ℤ) f).charpoly = f.charpoly :=
  LinearMap.charpoly_dualTranspose f

-- The transpose has the same trace, the negated coefficient of `X ^ (n - 1)`.
example {A M : Type*} [CommRing A] [Nontrivial A] [AddCommGroup M] [Module A M]
    [Module.Free A M] [Module.Finite A M] (f : Module.End A M) :
    (Module.Dual.transpose (R := A) f).charpoly.coeff (Module.finrank A M - 1) =
      f.charpoly.coeff (Module.finrank A M - 1) := by
  rw [LinearMap.charpoly_dualTranspose]
