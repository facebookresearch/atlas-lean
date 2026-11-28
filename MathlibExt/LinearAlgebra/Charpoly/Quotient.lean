/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import MathlibExt.LinearAlgebra.Determinant.QuotientBaseChange

/-!
# Characteristic polynomials under quotient and compatible scalar change

Let R,S be commutative rings, S a finite free R-algebra and I an ideal of R. If S/IS is finite
free over R/I, left multiplication on S/IS has characteristic polynomial equal to coefficient
reduction of that on S. For modules over equivalent scalar rings with compatible actions,
characteristic polynomials transport by the ring equivalence. The statements use the given
algebra, free-module and finite-module instances.
-/

@[expose] public section

set_option autoImplicit false

open Polynomial

namespace LinearMap

section MapCoeffs

variable {R S M : Type*} [CommRing R] [CommRing S]
  [AddCommGroup M] [Module R M] [Module S M]
  [Module.Free R M] [Module.Finite R M] [Module.Free S M] [Module.Finite S M]

/-- **Compatible scalar transport of a characteristic polynomial.**

Let R,S be commutative rings, e:R≃+*S, and M a finite free module over each ring with
e(c)•x=c•x. If f_R:M→ₗ[R]M and f_S:M→ₗ[S]M agree at every x, then χ_R(f_R) mapped
coefficientwise by e equals χ_S(f_S). Both scalar actions and the module instances are given.
-/
theorem charpoly_mapCoeffs (e : R ≃+* S)
    (h : ∀ (c : R) (x : M), e c • x = c • x)
    (fR : M →ₗ[R] M) (fS : M →ₗ[S] M) (hf : ∀ x, fS x = fR x) :
    fR.charpoly.map e.toRingHom = fS.charpoly := by
  classical
  let b := Module.Free.chooseBasis R M
  have hmatrix :
      LinearMap.toMatrix (b.mapCoeffs e h) (b.mapCoeffs e h) fS =
        (LinearMap.toMatrix b b fR).map e.toRingHom := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply,
      Module.Basis.mapCoeffs_apply, Module.Basis.mapCoeffs_repr,
      LinearMap.toMatrix_apply]
    change e (b.repr (fS (b j)) i) = e (b.repr (fR (b j)) i)
    rw [hf]
  rw [← LinearMap.charpoly_toMatrix fR b,
    ← LinearMap.charpoly_toMatrix fS (b.mapCoeffs e h), hmatrix, Matrix.charpoly_map]

end MapCoeffs

end LinearMap

namespace Algebra

section Quotient

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **Quotient base change of left multiplication.**

Let S be a commutative R-algebra, I an ideal of R and s∈S. The quotient base change of left
multiplication by s is left multiplication by its class in S/IS over R/I.
-/
@[simp]
theorem lmul_quotientBaseChange (s : S) (I : Ideal R) :
    (Algebra.lmul R S s).quotientBaseChange I =
      Algebra.lmul (R ⧸ I) (S ⧸ I.map (algebraMap R S)) (Ideal.Quotient.mk _ s) := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  let q : S →+* S ⧸ I.map (algebraMap R S) :=
    Ideal.Quotient.mk (I.map (algebraMap R S))
  calc
    (Algebra.lmul R S s).quotientBaseChange I (q x) =
        q ((Algebra.lmul R S s) x) :=
      LinearMap.quotientBaseChange_mk (Algebra.lmul R S s) I x
    _ = q (s * x) := by rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
    _ = q s * q x := q.map_mul s x
    _ = Algebra.lmul (R ⧸ I) (S ⧸ I.map (algebraMap R S)) (q s) (q x) := by
      rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']

variable [Module.Free R S] [Module.Finite R S]

/-- **Ideal reduction of a left-multiplication characteristic polynomial.**

Let S be a commutative finite free R-algebra, I an ideal of R and s∈S. If S/IS is finite free
over R/I with the given module instances, χ_(R/I)(L_[s]) is χ_R(L_s) reduced modulo I.
-/
theorem charpoly_lmul_quotient_map (s : S) (I : Ideal R)
    [Module.Free (R ⧸ I) (S ⧸ I.map (algebraMap R S))]
    [Module.Finite (R ⧸ I) (S ⧸ I.map (algebraMap R S))] :
    (Algebra.lmul (R ⧸ I) (S ⧸ I.map (algebraMap R S))
        (Ideal.Quotient.mk _ s)).charpoly =
      (Algebra.lmul R S s).charpoly.map (Ideal.Quotient.mk I) := by
  simpa only [lmul_quotientBaseChange] using
    LinearMap.charpoly_quotientBaseChange (Algebra.lmul R S s) I

/-- **Residue-field reduction of a left-multiplication characteristic polynomial.**

Let R be a commutative local ring with maximal ideal 𝔪, S a commutative R-algebra finite free
over R and s∈S. With given finite free instances for S/𝔪S over R/𝔪, χ_(R/𝔪)(L_[s]) is
χ_R(L_s) with coefficients reduced by R→R/𝔪.
-/
theorem charpoly_lmul_quotient_maximalIdeal_map [IsLocalRing R] (s : S)
    [Module.Free (R ⧸ IsLocalRing.maximalIdeal R)
      (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))]
    [Module.Finite (R ⧸ IsLocalRing.maximalIdeal R)
      (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))] :
    (Algebra.lmul (R ⧸ IsLocalRing.maximalIdeal R)
        (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (Ideal.Quotient.mk _ s)).charpoly =
      (Algebra.lmul R S s).charpoly.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)) :=
  charpoly_lmul_quotient_map s (IsLocalRing.maximalIdeal R)

end Quotient

section MapRingEquiv

variable {k k' E : Type*} [Field k] [Field k'] [CommRing E]
  [Algebra k E] [Algebra k' E] [Module.Finite k E] [Module.Finite k' E]

/-- **Compatible field-equivalence transport of a left-multiplication characteristic polynomial.**

Let k,k′ be fields, φ:k≃+*k′ and E a commutative algebra finite-dimensional over each field.
For the given algebra structures, assume φ(c)•y=c•y. For x∈E, χ_k(L_x) mapped coefficientwise
by φ equals χ_(k′)(L_x).
-/
theorem charpoly_lmul_map_ringEquiv (φ : k ≃+* k')
    (h : ∀ (c : k) (y : E), φ c • y = c • y) (x : E) :
    (Algebra.lmul k E x).charpoly.map φ.toRingHom = (Algebra.lmul k' E x).charpoly :=
  LinearMap.charpoly_mapCoeffs φ h (Algebra.lmul k E x) (Algebra.lmul k' E x)
    (fun y ↦ by simp only [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply'])

end MapRingEquiv

end Algebra
