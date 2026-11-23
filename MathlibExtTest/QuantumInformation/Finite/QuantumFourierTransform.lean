/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.QuantumInformation.Finite.QuantumFourierTransform

/-!
# Quantum Fourier transform checks

Unitarity is used in the forms `A * Aᴴ = 1` and `Aᴴ * A = 1`; the one-state transform is the
`1 × 1` identity.
-/

@[expose] public section

open Matrix MathlibExt.QuantumInformation.Finite.QuantumFourierTransform

namespace QuantumFourierTransformTest

example (q : ℕ) : qftMatrix q * (qftMatrix q)ᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.1 (qftMatrix_mem_unitaryGroup q)

example (q : ℕ) : (qftMatrix q)ᴴ * qftMatrix q = 1 :=
  Matrix.mem_unitaryGroup_iff'.1 (qftMatrix_mem_unitaryGroup q)

example : qftMatrix 1 = 1 := by
  ext a c
  fin_cases a; fin_cases c
  simp [qftMatrix_apply]

example (q : ℕ) (a c : Fin q) : qftMatrix q a c = qftMatrix q c a := by
  exact congrFun (congrFun (qftMatrix_transpose q) c) a

end QuantumFourierTransformTest
