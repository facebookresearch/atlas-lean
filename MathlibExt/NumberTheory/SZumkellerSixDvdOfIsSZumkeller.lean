/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SZumkeller

/-!
# Even s-Zumkeller numbers are divisible by 6

Every even s-Zumkeller number is divisible by 6: it is even and divisible by 3.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Corollary 1.
-/

namespace MetaMathlibExt

/-- **Even s-Zumkeller numbers are divisible by 6.** Every even s-Zumkeller number is divisible
by $6$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Corollary 1. -/
public theorem six_dvd_of_isSZumkeller (n : ℕ) (h : IsSZumkeller n) (he : Even n) :
    6 ∣ n := by
  have h3 := three_dvd_of_isSZumkeller n h he
  obtain ⟨k, hk⟩ := he
  omega

end MetaMathlibExt
