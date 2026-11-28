/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Finite.NormOneCount

/-!
# Tests for the count of norm-one elements of a finite field with $q^2$ elements
-/

set_option autoImplicit false

@[expose] public section

namespace NormOneCountTest

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
noncomputable local instance : Fintype (GaloisField 2 2) := Fintype.ofFinite _
noncomputable local instance : Fintype (GaloisField 3 2) := Fintype.ofFinite _
noncomputable local instance : Fintype (GaloisField 5 2) := Fintype.ofFinite _

open Classical in
/-- $\mathbb{F}_4$ has $3$ elements with $\beta^3 = 1$. -/
example : (Finset.univ.filter fun β : GaloisField 2 2 => β ^ (2 + 1) = 1).card = 2 + 1 :=
  FiniteField.card_pow_add_one_eq_one_of_card_eq_sq (by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 2 (by norm_num)])

open Classical in
/-- $\mathbb{F}_9$ has $4$ elements with $\beta^4 = 1$. -/
example : (Finset.univ.filter fun β : GaloisField 3 2 => β ^ 4 = 1).card = 4 :=
  FiniteField.card_pow_add_one_eq_one_of_card_eq_sq (q := 3) (by
    rw [Fintype.card_eq_nat_card, GaloisField.card 3 2 (by norm_num)])

open Classical in
/-- Exactly $6$ elements of $\mathbb{F}_{25}$ have norm $1$ over $\mathbb{F}_5$. -/
example : (Finset.univ.filter fun β : GaloisField 5 2 =>
    Algebra.norm (ZMod 5) β = 1).card = 6 :=
  FiniteField.card_norm_eq_one_of_card_eq_sq (q := 5) (ZMod.card 5) (by
    rw [Fintype.card_eq_nat_card, GaloisField.card 5 2 (by norm_num)])

end NormOneCountTest
