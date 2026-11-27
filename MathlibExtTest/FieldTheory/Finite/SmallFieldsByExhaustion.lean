/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Finite.SmallFieldsByExhaustion

/-!
# Tests for $U_q + U_q = \mathbb{F}_q$ for $q \in \{13, 16, 17, 19\}$
-/

set_option autoImplicit false

@[expose] public section

open scoped Pointwise

open FiniteField

namespace SmallFieldsByExhaustionTest

#check @tracesOfIrreducibleQuadratics_add_self_of_card_eq_thirteen
#check @tracesOfIrreducibleQuadratics_add_self_of_card_eq_sixteen
#check @tracesOfIrreducibleQuadratics_add_self_of_card_eq_seventeen
#check @tracesOfIrreducibleQuadratics_add_self_of_card_eq_nineteen
#check @tracesOfIrreducibleQuadratics_add_self_of_eleven_lt_card_of_card_lt_twentyThree

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

local instance : Fact (Nat.Prime 19) := ⟨by decide⟩

example :
    tracesOfIrreducibleQuadratics (ZMod 13) + tracesOfIrreducibleQuadratics (ZMod 13) =
      Set.univ :=
  tracesOfIrreducibleQuadratics_add_self_of_card_eq_thirteen (ZMod.card 13)

example :
    tracesOfIrreducibleQuadratics (ZMod 17) + tracesOfIrreducibleQuadratics (ZMod 17) =
      Set.univ :=
  tracesOfIrreducibleQuadratics_add_self_of_card_eq_seventeen (ZMod.card 17)

example :
    tracesOfIrreducibleQuadratics (ZMod 19) + tracesOfIrreducibleQuadratics (ZMod 19) =
      Set.univ :=
  tracesOfIrreducibleQuadratics_add_self_of_card_eq_nineteen (ZMod.card 19)

/-- The field with $16$ elements from Mathlib. -/
example :
    tracesOfIrreducibleQuadratics (GaloisField 2 4) +
      tracesOfIrreducibleQuadratics (GaloisField 2 4) = Set.univ := by
  have := Fintype.ofFinite (GaloisField 2 4)
  apply tracesOfIrreducibleQuadratics_add_self_of_card_eq_sixteen
  rw [Fintype.card_eq_nat_card, GaloisField.card 2 4 (by norm_num)]
  norm_num

/-- The range form, on `GaloisField 13 1`. -/
example :
    tracesOfIrreducibleQuadratics (GaloisField 13 1) +
      tracesOfIrreducibleQuadratics (GaloisField 13 1) = Set.univ := by
  have := Fintype.ofFinite (GaloisField 13 1)
  apply tracesOfIrreducibleQuadratics_add_self_of_eleven_lt_card_of_card_lt_twentyThree <;>
    rw [Fintype.card_eq_nat_card, GaloisField.card 13 1 (by norm_num)] <;> norm_num

/-- A consequence: $1 \in U_{13} + U_{13}$. -/
example : (1 : ZMod 13) ∈
    tracesOfIrreducibleQuadratics (ZMod 13) + tracesOfIrreducibleQuadratics (ZMod 13) := by
  rw [tracesOfIrreducibleQuadratics_add_self_of_card_eq_thirteen (ZMod.card 13)]
  trivial

end SmallFieldsByExhaustionTest
