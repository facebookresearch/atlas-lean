/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.BernsteinVazirani

@[expose] public section

/-- For `n = 0`, orthogonality gives `2^0 = 1`. -/
example (s : Fin 0 → Bool) :
    ∑ x : Fin 0 → Bool, chi x s * chi x s = 1 := by
  rw [chi_sum]
  simp

end
