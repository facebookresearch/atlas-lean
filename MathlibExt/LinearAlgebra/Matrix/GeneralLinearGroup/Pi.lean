/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Product
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Ring.Pi

/-!
# General linear groups over a Pi of semirings

Compose the existing entrywise Matrix.piRingEquiv with Mathlib's Pi-units
equivalence. Coordinates retain the original ring evaluations, and the
inverse recombines original matrix entries. No stable or K-theory carrier
is defined here.
-/

@[expose] public section

set_option autoImplicit false

universe uR uS v

namespace Matrix.GeneralLinearGroup

variable {ι : Type} (R : ι → Type uR) [∀ i, Semiring (R i)]

/-- Let `ι : Type` be any coefficient index type and `R : ι → Type uR` a family of
semirings, possibly noncommutative or zero. For any finite matrix index type `n : Type v`
with decidable equality, entrywise evaluation gives a group isomorphism
`GL n (∀ i, R i) ≃* ∀ i, GL n (R i)`. Empty coefficient and matrix indices are included. -/
def piSemiringEquiv (n : Type v) [Fintype n] [DecidableEq n] :
    GL n (∀ i, R i) ≃* ∀ i, GL n (R i) :=
  (Units.mapEquiv (Matrix.piRingEquiv (β := R) (n := n)).toMulEquiv).trans
    MulEquiv.piUnits

/-- Let `ι : Type` index a family of semirings `R : ι → Type uR`, and let `n : Type v`
be finite with decidable equality. For every `A : GL n (∀ i, R i)` and `i : ι`, coordinate
`i` of the semiring Pi equivalence is exactly the GL map induced by the unital semiring
homomorphism evaluating coefficients at `i`. Commutativity and nonzero rings are not required. -/
@[simp]
theorem piSemiringEquiv_apply (n : Type v) [Fintype n] [DecidableEq n]
    (A : GL n (∀ i, R i)) (i : ι) :
    piSemiringEquiv R n A i = mapRingHom (Pi.evalRingHom R i) A := by
  apply Units.ext
  rfl

/-- Let `ι : Type` index semirings `R : ι → Type uR`, and let `n : Type v` be finite
with decidable equality. For every family `A : ∀ i, GL n (R i)`, the inverse semiring Pi
equivalence forms a matrix over `∀ i, R i` whose `(p,q)` coefficient evaluated at `i`
is exactly the `(p,q)` entry of `A i`, for all `p q : n` and `i : ι`. -/
@[simp]
theorem coe_piSemiringEquiv_symm_apply (n : Type v) [Fintype n] [DecidableEq n]
    (A : ∀ i, GL n (R i)) (p q : n) (i : ι) :
    ((↑((piSemiringEquiv R n).symm A) : Matrix n n (∀ i, R i)) p q) i =
      (A i : Matrix n n (R i)) p q := rfl

/-- Let `ι : Type` index independent families of semirings `R : ι → Type uR` and
`S : ι → Type uS`. Let `n : Type v` be finite with decidable equality, and let
`φ : ∀ i, R i →+* S i` be unital semiring homomorphisms. For every
`A : GL n (∀ i, R i)` and `i : ι`, evaluating the family coefficient map at `i`
equals applying the GL map of `φ i` to coordinate `i` of the semiring Pi equivalence. -/
theorem piSemiringEquiv_mapRingHom {S : ι → Type uS} [∀ i, Semiring (S i)]
    (n : Type v) [Fintype n] [DecidableEq n] (φ : ∀ i, R i →+* S i)
    (A : GL n (∀ i, R i)) (i : ι) :
    piSemiringEquiv S n
        (mapRingHom (RingHom.pi (fun j => (φ j).comp (Pi.evalRingHom R j))) A) i =
      mapRingHom (φ i) (piSemiringEquiv R n A i) := by
  apply Units.ext
  rfl

end Matrix.GeneralLinearGroup
