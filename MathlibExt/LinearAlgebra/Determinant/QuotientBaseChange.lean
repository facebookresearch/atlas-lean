/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Linear endomorphisms after quotient base change

Let `S` be a finite free algebra over a commutative ring `R`, let `I` be an
ideal of `R`, and let `f : S →ₗ[R] S`.  This file transports the ordinary
scalar extension of `f` across the canonical algebra equivalence

```text
S / I S  ≃  (R / I) ⊗[R] S.
```

The resulting endomorphism `f.quotientBaseChange I` sends the class
of `x` to the class of `f x`, and its determinant is the reduction of
`det f` modulo `I`.

For a local base ring, bijectivity of the residue endomorphism therefore
shows that `det f` is a unit.  The bundled determinant unit has residue equal
to the determinant unit of the induced residue equivalence.

## Main declarations

* `LinearMap.quotientBaseChange`: quotient-valued scalar extension of an
  arbitrary finite-free algebra endomorphism.
* `LinearMap.quotientBaseChange_mk`: representative formula.
* `LinearMap.det_quotientBaseChange`: determinant commutes with reduction.
* `LinearMap.isUnit_det_of_bijective_quotientBaseChange`: local unit
  detection from a bijective residue map.
* `LinearMap.detUnitOfBijectiveQuotientBaseChange`: the resulting determinant
  unit, with its value and residue formulas.

## Informal proof

The canonical equivalence
`Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I` sends the class of
`x : S` to `1 ⊗ x`.  Conjugate the scalar extension
`f.baseChange (R / I)` by the inverse of this equivalence.  Since scalar
extension sends `1 ⊗ x` to `1 ⊗ f x`, conjugation gives the representative
formula.

Determinants are invariant under conjugation, and
`LinearMap.det_baseChange` identifies the determinant of the scalar extension
with `Ideal.Quotient.mk I (det f)`.  This proves determinant reduction without
choosing a basis of either quotient presentation.

Now suppose `R` is local and use its maximal ideal.  If the quotient map is
bijective, it is a linear equivalence, so its determinant is a unit and in
particular is nonzero in the residue field.  Determinant reduction says that
this nonzero element is the residue of `det f`.  An element of a local ring
has nonzero residue exactly when it is a unit.  Bundling that unit and applying
the same determinant equality proves the final residue formula.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe uR uS

namespace LinearMap

variable {R : Type uR} {S : Type uS}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- Scalar extension of an algebra endomorphism to `R / I`, transported from
the tensor-product presentation to the quotient presentation `S / I S`.

This is the arbitrary-linear-map analogue of quotient base change for
algebra norms; it reuses the same canonical tensor/quotient equivalence. -/
noncomputable def quotientBaseChange (f : S →ₗ[R] S) (I : Ideal R) :
    (S ⧸ I.map (algebraMap R S)) →ₗ[R ⧸ I]
      (S ⧸ I.map (algebraMap R S)) := by
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I
  exact e.symm.toLinearEquiv.conj (f.baseChange (R ⧸ I))

/-- Quotient base change sends a represented class to the class of its image
under the original endomorphism. -/
@[simp]
theorem quotientBaseChange_mk (f : S →ₗ[R] S) (I : Ideal R) (x : S) :
    f.quotientBaseChange I
        (Ideal.Quotient.mk (I.map (algebraMap R S)) x) =
      Ideal.Quotient.mk (I.map (algebraMap R S)) (f x) := by
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I
  apply e.injective
  simp [quotientBaseChange, e]

section Finite

variable [Module.Free R S] [Module.Finite R S]

/-- The determinant of quotient base change is the reduction of the original
determinant modulo the base ideal. -/
theorem det_quotientBaseChange (f : S →ₗ[R] S) (I : Ideal R) :
    (f.quotientBaseChange I).det = Ideal.Quotient.mk I f.det := by
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I
  change LinearMap.det
      (e.symm.toLinearEquiv.conj (f.baseChange (R ⧸ I))) = _
  calc
    _ = LinearMap.det (f.baseChange (R ⧸ I)) := by
      rw [LinearEquiv.conj_apply, LinearMap.comp_assoc]
      exact LinearMap.det_conj
        (f.baseChange (R ⧸ I)) e.symm.toLinearEquiv
    _ = _ := LinearMap.det_baseChange f

section Local

variable [IsLocalRing R]

/-- If the endomorphism induced on the closed fiber of a finite free algebra
is bijective, then the original determinant is a unit of the local base. -/
theorem isUnit_det_of_bijective_quotientBaseChange
    (f : S →ₗ[R] S)
    (hf : Function.Bijective
      (f.quotientBaseChange (IsLocalRing.maximalIdeal R))) :
    IsUnit f.det := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit f.det).mp
  change Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) f.det ≠ 0
  rw [← det_quotientBaseChange]
  exact (LinearEquiv.ofBijective _ hf).isUnit_det'.ne_zero

/-- The determinant unit supplied by bijectivity of the closed-fiber
endomorphism. -/
noncomputable def detUnitOfBijectiveQuotientBaseChange
    (f : S →ₗ[R] S)
    (hf : Function.Bijective
      (f.quotientBaseChange (IsLocalRing.maximalIdeal R))) : Rˣ :=
  (isUnit_det_of_bijective_quotientBaseChange f hf).unit

/-- The underlying value of the determinant unit is the original
determinant. -/
@[simp]
theorem coe_detUnitOfBijectiveQuotientBaseChange
    (f : S →ₗ[R] S)
    (hf : Function.Bijective
      (f.quotientBaseChange (IsLocalRing.maximalIdeal R))) :
    (detUnitOfBijectiveQuotientBaseChange f hf : R) = f.det :=
  (isUnit_det_of_bijective_quotientBaseChange f hf).unit_spec

/-- The residue of the bundled determinant unit is the determinant unit of
the induced closed-fiber equivalence. -/
theorem residue_detUnitOfBijectiveQuotientBaseChange
    (f : S →ₗ[R] S)
    (hf : Function.Bijective
      (f.quotientBaseChange (IsLocalRing.maximalIdeal R))) :
    Units.map
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)).toMonoidHom
        (detUnitOfBijectiveQuotientBaseChange f hf) =
      LinearEquiv.det
        (LinearEquiv.ofBijective
          (f.quotientBaseChange (IsLocalRing.maximalIdeal R)) hf) := by
  apply Units.ext
  simp only [Units.coe_map, LinearEquiv.coe_det,
    coe_detUnitOfBijectiveQuotientBaseChange]
  change Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) f.det =
    (f.quotientBaseChange (IsLocalRing.maximalIdeal R)).det
  rw [det_quotientBaseChange]

end Local

end Finite

end LinearMap

end
