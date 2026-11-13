/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Matrix.Basic
/-!

# Stoichiometric balance and reaction extents

Balanced reactions, advanced by arbitrary extents, leave every balance coordinate unchanged.

## i. Overview

Species identities are indexed by a finite type `ι`. Species with the same elemental formula
but a different phase or isomer identity are different indices: that distinction lives in the
choice of `ι`, not in the composition matrix. Balance coordinates are indexed by a type `κ`; in
the intended use they are the elements together with one coordinate for total electric charge.

A composition matrix `A : Matrix κ ι R` over a commutative ring `R` records in `A b s` the
amount of the balance coordinate `b` carried by one formula unit of the species `s`: the
subscript of the element `b`, or the signed charge on the charge coordinate. A reaction is a
vector `ν : ι → R` of signed stoichiometric coefficients, positive for products and negative
for reactants. Its net total of the coordinate `b`, the sum over species of coefficient times
subscript (or charge), is `(A *ᵥ ν) b`, and the reaction is balanced when `A *ᵥ ν = 0`, that
is, when reactants and products carry equal totals of every coordinate.

Starting from initial amounts `n₀ : ι → R`, advancing a finite family of reactions `ν r` by
arbitrary extents `ξ r` gives the amounts `n₀ + ∑ r, ξ r • ν r`. The main result is that if
every `ν r` is balanced for the same `A`, these amounts have the same balance coordinates as
`n₀`.

The amount vectors and extents here are numerical coordinates after a consistent choice of
amount unit. Composition entries and stoichiometric coefficients are dimensionless counts and
charges, not amounts of substance. A later bridge to dimensional quantities may wrap these
coordinates without changing the linear theorem.

The results are algebraic. They do not assert that amounts stay nonnegative, that an extent is
feasible or maximal, which reagent is limiting, what the yield is, that coefficients are unique
or minimal, that every kernel vector of `A` is a chemically realizable reaction, or that nature
follows the model.

## ii. Key results

- `IsBalanced` : a reaction is balanced for a composition matrix.
- `amountAfterExtents` : the amounts after a finite family of reactions advances by given
  extents.
- `mulVec_amountAfterExtents_of_isBalanced` : balanced reactions advanced by arbitrary extents
  conserve every balance coordinate.
- `mulVec_add_smul_of_isBalanced` : the same statement for a single reaction.
- `IsBalanced.intCast` : a reaction balanced over `ℤ` is balanced over `ℚ`.

## iii. Table of contents

- A. Balanced reactions
- B. Amounts after reaction extents
- C. Conservation of balance coordinates
- D. Integer reactions over the rationals

## iv. References

- OpenStax, *Chemistry 2e*, §4.1, "Writing and Balancing Chemical Equations".
- OpenStax, *Chemistry 2e*, §4.3, "Reaction Stoichiometry".
- IUPAC, *Quantities, Units and Symbols in Physical Chemistry* (the Green Book).

-/

@[expose] public section

namespace Chemistry.Stoichiometry

open Matrix

/-!

## A. Balanced reactions

-/

/-- The reaction `ν` is balanced for the composition matrix `A` when it carries a zero net total
of every balance coordinate, `A *ᵥ ν = 0`. Here `A b s` is the amount of the coordinate `b` (an
element subscript or a signed charge) in one formula unit of the species `s`, and `ν` is
positive on products and negative on reactants. -/
def IsBalanced {κ ι R : Type*} [CommRing R] [Fintype ι] (A : Matrix κ ι R) (ν : ι → R) :
    Prop :=
  A *ᵥ ν = 0

/-!

## B. Amounts after reaction extents

-/

/-- The amounts `n₀ + ∑ r, ξ r • ν r` reached from the initial amounts `n₀` when each reaction
`ν r` of a finite family advances by the extent `ξ r`. Extents and resulting amounts may have
any sign. -/
def amountAfterExtents {ι ρ R : Type*} [CommRing R] [Fintype ρ]
    (n₀ : ι → R) (ν : ρ → ι → R) (ξ : ρ → R) : ι → R :=
  n₀ + ∑ r, ξ r • ν r

/-!

## C. Conservation of balance coordinates

-/

/-- If every reaction `ν r` of a finite family is balanced for the same composition matrix `A`,
then advancing the reactions by arbitrary extents `ξ r` leaves every balance coordinate of the
initial amounts `n₀` unchanged. -/
lemma mulVec_amountAfterExtents_of_isBalanced {κ ι ρ R : Type*} [CommRing R] [Fintype ι]
    [Fintype ρ] (A : Matrix κ ι R) (n₀ : ι → R) (ν : ρ → ι → R) (ξ : ρ → R)
    (h : ∀ r, IsBalanced A (ν r)) :
    A *ᵥ amountAfterExtents n₀ ν ξ = A *ᵥ n₀ := by
  have hr (r : ρ) : A *ᵥ (ξ r • ν r) = 0 := by
    have hb : A *ᵥ ν r = 0 := h r
    rw [mulVec_smul, hb, smul_zero]
  rw [amountAfterExtents, mulVec_add, mulVec_sum, Finset.sum_eq_zero fun r _ => hr r, add_zero]

/-- A balanced reaction `ν` advanced by an extent `ξ` leaves every balance coordinate of the
initial amounts `n₀` unchanged. -/
lemma mulVec_add_smul_of_isBalanced {κ ι R : Type*} [CommRing R] [Fintype ι]
    (A : Matrix κ ι R) (n₀ ν : ι → R) (ξ : R) (h : IsBalanced A ν) :
    A *ᵥ (n₀ + ξ • ν) = A *ᵥ n₀ := by
  simpa [amountAfterExtents] using
    mulVec_amountAfterExtents_of_isBalanced A n₀ (fun _ : Unit => ν) (fun _ => ξ) fun _ => h

/-!

## D. Integer reactions over the rationals

-/

/-- A reaction balanced for an integer composition matrix stays balanced when the matrix and the
coefficients are cast to `ℚ`. -/
lemma IsBalanced.intCast {κ ι : Type*} [Fintype ι] {A : Matrix κ ι ℤ} {ν : ι → ℤ}
    (h : IsBalanced A ν) :
    IsBalanced (A.map (Int.cast : ℤ → ℚ)) (fun s => (ν s : ℚ)) := by
  funext b
  have key := (Int.castRingHom ℚ).map_mulVec A ν b
  have hb : (A *ᵥ ν) b = 0 := congrFun h b
  rw [hb, map_zero] at key
  exact key.symm

end Chemistry.Stoichiometry
