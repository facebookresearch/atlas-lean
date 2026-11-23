/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryFortyOne

open MetaMathlibExt

-- Zero is exactly the exponent for which every prime factor lies in the excluded set.
example (g : ℕ) :
    (∀ q : ℕ, q.Prime → q ∣ sigmaBiunitary (41 ^ g) → q ∈ ({2, 3, 5, 13} : Finset ℕ)) ↔
      g = 0 := by
  constructor
  · intro h
    by_contra hg
    obtain ⟨q, hq, hdvd, hout⟩ := exists_prime_dvd_sigmaBiunitary_fortyOne_pow g (by omega)
    exact hout (h q hq hdvd)
  · rintro rfl q hq hdvd
    simp [sigmaBiunitary_one, hq.not_dvd_one] at hdvd

-- The first odd and even exponents have witnesses 7 and 29, respectively.
example : sigmaBiunitary 41 = 2 * 3 * 7 := by decide

example : sigmaBiunitary (41 ^ 2) = 2 * 29 ^ 2 := by decide +kernel
