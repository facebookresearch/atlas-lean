/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WilsonQuotientsExistsNatEqWilsonQuotientZPlusIff

namespace MathlibExtTest.NumberTheory.WilsonQuotientsExistsNatEqWilsonQuotientZPlusIff

open MathlibExt.NumberTheory.WilsonQuotientsWanted

-- The unit case is a natural number.
example : ∃ m : ℕ, (m : ℚ) = wilsonQuotientZPlus 1 :=
  (exists_nat_eq_wilsonQuotientZPlus_iff 1 (by decide)).mpr (Or.inr (Or.inl rfl))

-- An even prime gives a natural number.
example : ∃ m : ℕ, (m : ℚ) = wilsonQuotientZPlus 2 :=
  (exists_nat_eq_wilsonQuotientZPlus_iff 2 (by decide)).mpr (Or.inl (by decide))

-- An odd prime gives a natural number.
example : ∃ m : ℕ, (m : ℚ) = wilsonQuotientZPlus 3 :=
  (exists_nat_eq_wilsonQuotientZPlus_iff 3 (by decide)).mpr (Or.inr (Or.inr (by decide)))

-- An even composite gives a natural number.
example : ∃ m : ℕ, (m : ℚ) = wilsonQuotientZPlus 4 :=
  (exists_nat_eq_wilsonQuotientZPlus_iff 4 (by decide)).mpr (Or.inl (by decide))

-- An odd composite does not give a natural number.
example : ¬∃ m : ℕ, (m : ℚ) = wilsonQuotientZPlus 9 := by
  intro h
  exact absurd ((exists_nat_eq_wilsonQuotientZPlus_iff 9 (by decide)).mp h) (by decide)

end MathlibExtTest.NumberTheory.WilsonQuotientsExistsNatEqWilsonQuotientZPlusIff
