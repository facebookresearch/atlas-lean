/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.UniversalHashing


/-!
# Tests for universal hashing

These client examples exercise the collision-count API, concrete
mod-prime hash values (including the `m = 1` boundary, where every key
collides), the exclusion of empty families from universality, and the
usability of the mod-prime universality theorem from a bare primality
assumption (no separate `NeZero` instance).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UniversalHashingTests

open Cslib.Algorithms.Lean.UniversalHashing

/-! ### Empty families are not universal -/

example : ¬ IsUniversal (∅ : Finset (Nat → Fin 3)) := not_isUniversal_empty

example (h : Nat → Nat → Fin 3) : ¬ IsUniversalOn (∅ : Finset Nat) h :=
  not_isUniversalOn_empty h

/-- The bound alone still holds vacuously for the empty family. -/
example (x y : Nat) (hxy : x ≠ y) :
    collisionCount (∅ : Finset (Nat → Fin 3)) x y * 3 ≤
      (∅ : Finset (Nat → Fin 3)).card :=
  isUniversal_bound_empty x y hxy

/-! ### Concrete collision counts -/

/-- Two constant functions and reduction modulo `3`, on the finite key
space `Fin 5` (so that the family is a literal `Finset` of functions). -/
public def fam3 : Finset (Fin 5 → Fin 3) :=
  {fun _ => 0, fun _ => 1, fun k => ⟨k.val % 3, Nat.mod_lt _ (by decide)⟩}

example : collisionCount fam3 0 1 = 2 := by decide

example : collisionCount fam3 0 3 = 3 := by decide

example : collisionCount fam3 2 2 = fam3.card := collisionCount_self fam3 2

example : collisionCount fam3 0 1 ≤ fam3.card := collisionCount_le_card fam3 0 1

/-- `fam3` is not universal: keys `0` and `1` collide under `2` of the `3`
functions, and `2 * 3 > 3`. -/
example : ¬ IsUniversal fam3 := by
  rintro ⟨-, -, hbound⟩
  have h := hbound 0 1 (by decide)
  have h1 : collisionCount fam3 0 1 = 2 := by decide
  have h2 : fam3.card = 3 := by decide
  omega

/-! ### Concrete mod-prime hash values -/

private theorem hm3 : 0 < 3 := by decide

/-- `h_{2,1}(3) = ((2 * 3 + 1) mod 7) mod 3 = 0`. -/
example : modPrimeHash 7 3 hm3 2 1 3 = 0 := by decide

/-- `h_{2,1}(4) = ((2 * 4 + 1) mod 7) mod 3 = 2`. -/
example : modPrimeHash 7 3 hm3 2 1 4 = 2 := by decide

/-- A concrete collision: `h_{1,0}(1) = 1 = h_{1,0}(4)` in `Fin 3`. -/
example : modPrimeHash 7 3 hm3 1 0 1 = modPrimeHash 7 3 hm3 1 0 4 := by
  decide

example : (modPrimeHash 7 3 hm3 2 1 4).val = (2 * 4 + 1 : ZMod 7).val % 3 :=
  modPrimeHash_val 7 3 hm3 2 1 4

/-! ### The `m = 1` boundary: one slot, everything collides -/

example : modPrimeHash 7 1 (by decide) 2 1 3 = modPrimeHash 7 1 (by decide) 5 6 4 := by
  decide

example (a b x : ZMod 7) : (modPrimeHash 7 1 (by decide) a b x).val = 0 := by
  rw [modPrimeHash_val]
  exact Nat.mod_one _

/-! ### Mod-prime universality from primality alone -/

/-- The public universality theorem needs only `Fact p.Prime`. -/
example {p m : Nat} [Fact p.Prime] (hm : 0 < m) :
    IsUniversalOn Finset.univ (modPrimeHashes p m hm) :=
  modPrime_isUniversalOn hm

example {p m : Nat} [Fact p.Prime] (hm : 0 < m) {x y : ZMod p} (hxy : x ≠ y) :
    (Finset.univ.filter fun ab : ModPrimeIndex p =>
      modPrimeHashes p m hm ab x = modPrimeHashes p m hm ab y).card * m ≤
      p * (p - 1) :=
  modPrime_collision_mul_le hm hxy

/-- For `p = 7` the index set has `7 * 6 = 42` elements and is nonempty,
as universality requires. -/
example : Fintype.card (ModPrimeIndex 7) = 42 := by
  rw [modPrimeIndex_card]

example : (Finset.univ : Finset (ModPrimeIndex 7)).Nonempty := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact (modPrime_isUniversalOn (p := 7) (m := 3) hm3).2.1

#print axioms modPrime_isUniversalOn
#print axioms modPrime_collision_mul_le

end Cslib.Algorithms.Lean.UniversalHashingTests
