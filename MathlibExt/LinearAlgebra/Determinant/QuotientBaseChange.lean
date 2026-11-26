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
# Quotient base change and determinant units

Let R,S be commutative rings with an R-algebra structure on S, I an ideal of R and f:S→S
R-linear. Put S_I=S/IS. The quotient base-change map f_I:S_I→S_I is R/I-linear with
f_I([x])=[f(x)]. If S is finite free over R, det(f_I) is det(f) reduced modulo I. For local R,
a bijective residue map makes det(f) a unit.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe uR uS

namespace LinearMap

variable {R : Type uR} {S : Type uS}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- **Linear endomorphism after quotient base change.**

Let R,S be commutative rings with an R-algebra structure on S, I an ideal of R and f:S→S
R-linear. Put S_I=S/IS. The quotient base-change map f_I:S_I→S_I is R/I-linear with
f_I([x])=[f(x)]. The map quotientBaseChange f I is f_I, using S/IS≃(R/I)⊗_RS.
-/
noncomputable def quotientBaseChange (f : S →ₗ[R] S) (I : Ideal R) :
    (S ⧸ I.map (algebraMap R S)) →ₗ[R ⧸ I]
      (S ⧸ I.map (algebraMap R S)) := by
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I
  exact e.symm.toLinearEquiv.conj (f.baseChange (R ⧸ I))

/-- **Value of quotient base change on a representative.**

Let R,S be commutative rings with an R-algebra structure on S, I an ideal of R and f:S→S
R-linear. Put S_I=S/IS. The quotient base-change map f_I:S_I→S_I is R/I-linear with
f_I([x])=[f(x)]. For x∈S, quotientBaseChange f I ([x])=[f(x)].
-/
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

/-- **Determinant reduced under quotient base change.**

Let R,S be commutative rings with an R-algebra structure on S, I an ideal of R and f:S→S
R-linear. Put S_I=S/IS. The quotient base-change map f_I:S_I→S_I is R/I-linear with
f_I([x])=[f(x)]. If S is finite free over R, det_(R/I)(f_I)=q_I(det_R f), where q_I:R→R/I is
the quotient map.
-/
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

/-- **Bijective residue endomorphism gives a determinant unit.**

Let R be a commutative local ring with maximal ideal 𝔪 and S a commutative finite free
R-algebra. If f:S→S is R-linear and its induced residue map f̄:S/𝔪S→S/𝔪S is bijective, then
det(f) is a unit in R. This is isUnit_det_of_bijective_quotientBaseChange.
-/
theorem isUnit_det_of_bijective_quotientBaseChange
    (f : S →ₗ[R] S)
    (hf : Function.Bijective
      (f.quotientBaseChange (IsLocalRing.maximalIdeal R))) :
    IsUnit f.det := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit f.det).mp
  change Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) f.det ≠ 0
  rw [← det_quotientBaseChange]
  exact (LinearEquiv.ofBijective _ hf).isUnit_det'.ne_zero

/-- **Determinant unit defined by a bijective residue map.**

Let R be a commutative local ring with maximal ideal 𝔪 and S a commutative finite free
R-algebra. If f:S→S is R-linear and its induced residue map f̄:S/𝔪S→S/𝔪S is bijective, then
det(f) is a unit in R. The unit detUnitOfBijectiveQuotientBaseChange f hf∈Rˣ has underlying
value det(f).
-/
noncomputable def detUnitOfBijectiveQuotientBaseChange
    (f : S →ₗ[R] S)
    (hf : Function.Bijective
      (f.quotientBaseChange (IsLocalRing.maximalIdeal R))) : Rˣ :=
  (isUnit_det_of_bijective_quotientBaseChange f hf).unit

/-- **Underlying value of the residue-detected determinant unit.**

Let R be a commutative local ring with maximal ideal 𝔪 and S a commutative finite free
R-algebra. If f:S→S is R-linear and its induced residue map f̄:S/𝔪S→S/𝔪S is bijective, then
det(f) is a unit in R. For D=detUnitOfBijectiveQuotientBaseChange f hf, (D:R)=det(f).
-/
@[simp]
theorem coe_detUnitOfBijectiveQuotientBaseChange
    (f : S →ₗ[R] S)
    (hf : Function.Bijective
      (f.quotientBaseChange (IsLocalRing.maximalIdeal R))) :
    (detUnitOfBijectiveQuotientBaseChange f hf : R) = f.det :=
  (isUnit_det_of_bijective_quotientBaseChange f hf).unit_spec

/-- **Residue of the determinant unit.**

Let R be a commutative local ring with maximal ideal 𝔪 and S a commutative finite free
R-algebra. If f:S→S is R-linear and its induced residue map f̄:S/𝔪S→S/𝔪S is bijective, then
det(f) is a unit in R. The image of D=detUnitOfBijectiveQuotientBaseChange f hf in (R/𝔪)ˣ
equals the determinant unit of the linear equivalence defined by f̄.
-/
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
