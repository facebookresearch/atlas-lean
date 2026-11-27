/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularCurve_PeriodMap.lean`,
`Definitions/Def_ModularCurve_PDPairing.lean`
and
`Definitions/Def_ModularCurve_CupPairing.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The rational cup pairing on parabolic homomorphisms

For a subgroup `Γ` of `SL(2, ℤ)` we define

* `ModularCurve.Period.IsParabolicHom`: a homomorphism `Additive Γ →+ A` that vanishes on
  every element of `Γ` whose trace squares to `4` (the parabolic elements, up to sign);
* `ModularCurve.Period.parabolicHoms R Γ A`: the `R`-submodule of such homomorphisms;
* `ModularCurve.PDPairing.omega φ ψ`: the alternating `2`-cocycle
  `(g, g') ↦ φ g * ψ g' - ψ g * φ g'`;
* `ModularCurve.PDPairing.OrientedCusp Γ`: the orbits of `⟨T⟩` on `SL(2, ℤ) ⧸ Γ` (the oriented
  cusps of `Γ`), with a chosen generator `orientedCuspGen Γ q ∈ Γ` of each oriented-cusp
  stabilizer and the sum `orientedCuspSum` of a function over these generators. The stabilizer
  of `∞` in `SL(2, ℤ)` is `±⟨T⟩`, so these are the cusps of `Γ` when `-1 ∈ Γ`; when `-1 ∉ Γ`,
  two oriented cusps, exchanged by `-1`, lie over each regular cusp, and one over each irregular
  cusp;
* `ModularCurve.CupPairing.pair Γ φ ψ`: the rational cup pairing. When `Γ` has finite index
  and `omega φ ψ` has a primitive `h : Γ → ℚ`, it is `orientedCuspSum Γ h / (2 * mult Γ)`,
  where `mult Γ` is `1` if `-1 ∈ Γ` and `2` otherwise; otherwise it is `0`.
-/

@[expose] public section

open scoped MatrixGroups

namespace ModularCurve.Period

/-- A homomorphism on `Γ` is parabolic if it vanishes on every element of `Γ` whose trace
squares to `4`. -/
def IsParabolicHom (Γ : Subgroup SL(2, ℤ)) {A : Type*} [AddCommGroup A] (φ : Additive Γ →+ A) :
    Prop :=
  ∀ γ : Γ, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 →
    φ (Additive.ofMul γ) = 0

section ParabolicHoms

variable (R : Type*) [Semiring R] (Γ : Subgroup SL(2, ℤ)) (A : Type*) [AddCommGroup A] [Module R A]

/-- The `R`-submodule of parabolic homomorphisms `Additive Γ →+ A`. -/
def parabolicHoms : Submodule R (Additive Γ →+ A) where
  carrier := {φ | IsParabolicHom Γ φ}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro φ ψ hφ hψ γ hγ
    change φ (Additive.ofMul γ) + ψ (Additive.ofMul γ) = 0
    rw [hφ γ hγ, hψ γ hγ, add_zero]
  smul_mem' := by
    intro c φ hφ γ hγ
    change c • φ (Additive.ofMul γ) = 0
    rw [hφ γ hγ, smul_zero]

variable {R Γ A}

theorem mem_parabolicHoms_iff {φ : Additive Γ →+ A} :
    φ ∈ parabolicHoms R Γ A ↔ IsParabolicHom Γ φ :=
  Iff.rfl

end ParabolicHoms

end ModularCurve.Period

namespace ModularCurve.PDPairing

section Omega

variable {Φ : Type*} [Group Φ] {R : Type*} [CommRing R]

/-- The alternating `2`-cocycle `(g, g') ↦ φ g * ψ g' - ψ g * φ g'` attached to two
homomorphisms `φ ψ : Additive Φ →+ R`. -/
def omega (φ ψ : Additive Φ →+ R) (g g' : Φ) : R :=
  φ (Additive.ofMul g) * ψ (Additive.ofMul g') - ψ (Additive.ofMul g) * φ (Additive.ofMul g')

theorem omega_one_left (φ ψ : Additive Φ →+ R) (g : Φ) : omega φ ψ 1 g = 0 := by
  simp [omega]

theorem omega_one_right (φ ψ : Additive Φ →+ R) (g : Φ) : omega φ ψ g 1 = 0 := by
  simp [omega]

theorem omega_cocycle (φ ψ : Additive Φ →+ R) (g h k : Φ) :
    omega φ ψ g h + omega φ ψ (g * h) k = omega φ ψ h k + omega φ ψ g (h * k) := by
  simp only [omega, ofMul_mul, map_add]
  ring

theorem omega_swap (φ ψ : Additive Φ →+ R) (g h : Φ) : omega ψ φ g h = -omega φ ψ g h := by
  simp only [omega]
  ring

end Omega

section OrientedCusps

open MulAction

variable (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] {R : Type*} [CommRing R]

/-- The oriented cusps of `Φ`: the orbits of the translation subgroup `⟨T⟩` on `SL(2, ℤ) ⧸ Φ`.

These are not the cusps of `Φ` in general. The stabilizer of `∞` in `SL(2, ℤ)` is `±⟨T⟩`, so the
cusps of `Φ` correspond to the orbits of `±⟨T⟩` on `SL(2, ℤ) ⧸ Φ`, and each oriented cusp lies
over one cusp. If `-1 ∈ Φ`, then `-1` fixes every coset and the two notions agree. Otherwise `-1`
acts freely on `SL(2, ℤ) ⧸ Φ` and commutes with `T`: two oriented cusps, exchanged by `-1`, lie
over each regular cusp, and one over each irregular cusp. The factor `CupPairing.mult` in
`CupPairing.pair` accounts for this. -/
abbrev OrientedCusp : Type :=
  Quotient (orbitRel (Subgroup.zpowers ModularGroup.T) (SL(2, ℤ) ⧸ Φ))

noncomputable instance : Fintype (OrientedCusp Φ) := Fintype.ofFinite _

/-- A chosen generator in `Φ` of the stabilizer of the oriented cusp `q`: the conjugate of the
smallest power of `T` fixing a representative coset. For the chosen representative `g` of `q` it
generates `Φ ∩ g⁻¹ ⟨T⟩ g`, which has index `2` in the stabilizer `Φ ∩ g⁻¹ (±⟨T⟩) g` in `Φ` of
the cusp `g⁻¹ ∞` when `-1 ∈ Φ` or that cusp is irregular, and index `1` otherwise. -/
noncomputable def orientedCuspGen (q : OrientedCusp Φ) : Φ :=
  ⟨q.out.out⁻¹ * ModularGroup.T ^ Function.minimalPeriod (ModularGroup.T • ·) q.out *
      q.out.out,
    QuotientGroup.out_conj_pow_minimalPeriod_mem Φ ModularGroup.T q.out⟩

/-- The sum of `f` over the chosen generators `orientedCuspGen Φ q` of the oriented cusps `q`
of `Φ`. -/
noncomputable def orientedCuspSum (f : Φ → R) : R :=
  ∑ q : OrientedCusp Φ, f (orientedCuspGen Φ q)

theorem orientedCuspSum_add (f g : Φ → R) :
    orientedCuspSum Φ (f + g) = orientedCuspSum Φ f + orientedCuspSum Φ g := by
  simp [orientedCuspSum, Finset.sum_add_distrib]

theorem orientedCuspSum_smul (r : R) (f : Φ → R) :
    orientedCuspSum Φ (r • f) = r * orientedCuspSum Φ f := by
  simp [orientedCuspSum, Finset.mul_sum]

end OrientedCusps

end ModularCurve.PDPairing

namespace ModularCurve.CupPairing

/-- `h` is a primitive of the cocycle `omega φ ψ`:
`h (g * g') = h g + h g' - omega φ ψ g g'` for all `g g'`. -/
def IsPrimitive {G : Type*} [Group G] {R : Type*} [CommRing R] (φ ψ : Additive G →+ R)
    (h : G → R) : Prop :=
  ∀ g g' : G, h (g * g') = h g + h g' - ModularCurve.PDPairing.omega φ ψ g g'

/-- The multiplicity factor: `1` if `-1 ∈ Γ`, and `2` otherwise. -/
noncomputable def mult (Γ : Subgroup SL(2, ℤ)) : ℚ := by
  classical
  exact if (-1 : SL(2, ℤ)) ∈ Γ then 1 else 2

/-- The rational cup pairing of two homomorphisms `Additive Γ →+ ℚ`:
`orientedCuspSum Γ h / (2 * mult Γ)` for a chosen primitive `h` of `omega φ ψ` when `Γ` has
finite index and a primitive exists, and `0` otherwise. -/
noncomputable def pair (Γ : Subgroup SL(2, ℤ)) (φ ψ : Additive Γ →+ ℚ) : ℚ := by
  classical
  exact if hΓ : Γ.FiniteIndex then
      if hp : ∃ h : Γ → ℚ, IsPrimitive φ ψ h then
        (@ModularCurve.PDPairing.orientedCuspSum Γ hΓ ℚ _ (Classical.choose hp)) / (2 * mult Γ)
      else 0
    else 0

theorem pair_eq_dif (Γ : Subgroup SL(2, ℤ)) [hΓ : Γ.FiniteIndex] (φ ψ : Additive Γ →+ ℚ)
    (hp : ∃ h : Γ → ℚ, IsPrimitive φ ψ h) :
    pair Γ φ ψ =
      ModularCurve.PDPairing.orientedCuspSum Γ (Classical.choose hp) / (2 * mult Γ) := by
  unfold pair
  rw [dite_eq_left hΓ, dite_eq_left hp]

theorem pair_eq_zero_of_not_exists (Γ : Subgroup SL(2, ℤ)) (φ ψ : Additive Γ →+ ℚ)
    (hp : ¬ ∃ h : Γ → ℚ, IsPrimitive φ ψ h) : pair Γ φ ψ = 0 := by
  unfold pair
  split_ifs <;> rfl

theorem pair_eq_zero_of_not_finiteIndex (Γ : Subgroup SL(2, ℤ)) (φ ψ : Additive Γ →+ ℚ)
    (hΓ : ¬ Γ.FiniteIndex) : pair Γ φ ψ = 0 := by
  unfold pair
  rw [dite_eq_right hΓ]

theorem mult_ne_zero (Γ : Subgroup SL(2, ℤ)) : mult Γ ≠ 0 := by
  unfold mult
  split_ifs <;> norm_num

end ModularCurve.CupPairing
