/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.TuringMachine.Recursive.OfTM2
public meta import MathlibExt.Computability.TuringMachine.Recursive.OfTM2

@[expose] public section

/-!
# Tests for `computable_of_tm2Computable`

The binary encoding and its left inverse on small values, and the theorem applied to a real
machine: a one-stack `FinTM2` that halts immediately computes the identity, so the identity is
`Computable`.
-/

set_option autoImplicit false

open Computability Turing MetaMathlibExt.TM2Recursive

namespace MathlibExtTest.Computability.TuringMachine.Recursive

#guard encodeNat 6 = [false, true, true]
#guard bitsVal (encodeNat 37) = 37

/-- One stack of bits, one label, one state; the program halts at once. -/
def haltTM : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ ↦ Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m := fun _ ↦ .halt

/-- The halting machine computes the identity under `encodeNat`: one step turns the input
configuration into the halting configuration with the same stack. -/
def haltTMComputable : TM2Computable encodeNat encodeNat (id : ℕ → ℕ) where
  tm := haltTM
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  outputsFun _ := ⟨1, rfl⟩

/-- Hence the identity is `Computable`, through the simulation. -/
example : Computable (id : ℕ → ℕ) := computable_of_tm2Computable haltTMComputable

end MathlibExtTest.Computability.TuringMachine.Recursive
