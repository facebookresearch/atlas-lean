/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Basic

/-!
# Twisting a linear representation by a character

For a commutative ring `R`, a monoid `G`, a linear representation `ρ` of `G` on an `R`-module
`A`, a character `χ : G →* Rˣ` and `i : ℤ`, this file defines the twist
`Representation.twistByCharacter ρ χ i`: the same module, with `g` acting by `χ(g) ^ i • ρ(g)`.
It proves that the twist by `0` is `ρ` and that twisting by `i` and then by `j` is twisting by
`i + j`.

For the absolute Galois group `G_k` of a field, coefficients a quotient or limit of `ℤ_ℓ` and `χ`
the cyclotomic character, this is the `i`-th Tate twist of J. Neukirch, A. Schmidt,
K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition version 2.3 (May 2020),
Chapter VII, §3, (7.3.6) Definition, p. 397, with the rule `A(i + j) = A(i)(j)` of the remarks
after it on p. 398.
-/

@[expose] public section

set_option autoImplicit false

namespace Representation

variable {R G A : Type*} [CommRing R] [Monoid G] [AddCommGroup A] [Module R A]

/-- The `i`-th twist of a linear representation `ρ` of a monoid `G` on an `R`-module `A` by a
character `χ : G →* Rˣ`: the same module, with `g` acting by `χ(g) ^ i • ρ(g)`.

For the absolute Galois group `G_k` of a field and `χ` the cyclotomic character, this is the
twisted action `σ(a) := χ_cycl(σ)^i · σa` of the `i`-th Tate twist `A(i)`
(Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, (7.3.6) Definition, p. 397), here
for a module over a coefficient ring `R` through which the character acts. -/
noncomputable def twistByCharacter (ρ : Representation R G A) (χ : G →* Rˣ) (i : ℤ) :
    Representation R G A where
  toFun g := ((χ g ^ i : Rˣ) : R) • ρ g
  map_one' := by simp
  map_mul' g h := by
    ext a
    simp only [map_mul, mul_zpow, Units.val_mul, LinearMap.smul_apply, mul_apply_eq_comp,
      map_smul, smul_smul]
    rw [mul_comm ((χ h ^ i : Rˣ) : R)]

/-- In the twist of `ρ` by `χ ^ i`, `g` acts by `χ(g) ^ i • ρ(g)`. -/
theorem twistByCharacter_apply (ρ : Representation R G A) (χ : G →* Rˣ) (i : ℤ) (g : G)
    (a : A) : ρ.twistByCharacter χ i g a = ((χ g ^ i : Rˣ) : R) • ρ g a := rfl

/-- The twist of `ρ` by `χ ^ 0` is `ρ`: `A(0) = A` (Neukirch–Schmidt–Wingberg, remarks after
(7.3.6), p. 398). -/
theorem twistByCharacter_zero (ρ : Representation R G A) (χ : G →* Rˣ) :
    ρ.twistByCharacter χ 0 = ρ := by
  ext g a
  simp [twistByCharacter_apply]

/-- Twisting by `χ ^ i` and then by `χ ^ j` is twisting by `χ ^ (i + j)`: `A(i)(j) = A(i + j)`
(Neukirch–Schmidt–Wingberg, remarks after (7.3.6), p. 398). -/
theorem twistByCharacter_twistByCharacter (ρ : Representation R G A) (χ : G →* Rˣ)
    (i j : ℤ) :
    (ρ.twistByCharacter χ i).twistByCharacter χ j = ρ.twistByCharacter χ (i + j) := by
  ext g a
  simp only [twistByCharacter_apply, smul_smul, zpow_add, Units.val_mul]
  rw [mul_comm]

end Representation
