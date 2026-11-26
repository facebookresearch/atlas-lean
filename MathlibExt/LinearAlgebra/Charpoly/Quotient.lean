/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.RingTheory.LocalRing.Quotient

/-!
# Left-multiplication characteristic polynomials under scalar change

Let R be a commutative local ring, S a commutative R-algebra finite free over R and 𝔪 its
maximal ideal. Left multiplication on S/𝔪S has characteristic polynomial equal to coefficient
reduction of that on S. Scalar reindexing along a field equivalence likewise maps the
characteristic polynomial coefficients.
-/

@[expose] public section

set_option autoImplicit false

open Polynomial

namespace Algebra

section QuotientMaximalIdeal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [Module.Finite R S] [Module.Free R S]

/-- **Residue-field reduction of a left-multiplication characteristic polynomial.**

Let R be a commutative local ring with maximal ideal 𝔪, S a commutative R-algebra finite free
over R and s∈S. For k=R/𝔪 and S̄=S/𝔪S, χ_k(L_s̄) is χ_R(L_s) with coefficients reduced by R→k.
-/
theorem charpoly_lmul_quotient_maximalIdeal_map (s : S) :
    let _ : Module.Free (R ⧸ IsLocalRing.maximalIdeal R)
        (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) :=
      Module.Free.of_basis (IsLocalRing.basisQuotient
        (Module.Free.chooseBasis R S))
    let _ : Module.Finite (R ⧸ IsLocalRing.maximalIdeal R)
        (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) :=
      Module.Finite.of_basis (IsLocalRing.basisQuotient
        (Module.Free.chooseBasis R S))
    (Algebra.lmul (R ⧸ IsLocalRing.maximalIdeal R)
        (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (Ideal.Quotient.mk _ s)).charpoly
      = (Algebra.lmul R S s).charpoly.map
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)) := by
  classical
  let b := Module.Free.chooseBasis R S
  have _ : Module.Free (R ⧸ IsLocalRing.maximalIdeal R)
      (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) :=
    Module.Free.of_basis (IsLocalRing.basisQuotient b)
  have _ : Module.Finite (R ⧸ IsLocalRing.maximalIdeal R)
      (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) :=
    Module.Finite.of_basis (IsLocalRing.basisQuotient b)
  have hmat : LinearMap.toMatrix (IsLocalRing.basisQuotient b)
        (IsLocalRing.basisQuotient b)
        (Algebra.lmul (R ⧸ IsLocalRing.maximalIdeal R)
          (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
          (Ideal.Quotient.mk _ s))
      = (LinearMap.toMatrix b b (Algebra.lmul R S s)).map
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply,
      LinearMap.toMatrix_apply, IsLocalRing.basisQuotient_apply]
    have hmul : (Algebra.lmul (R ⧸ IsLocalRing.maximalIdeal R)
          (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
          (Ideal.Quotient.mk _ s)) (Ideal.Quotient.mk _ (b j))
        = Ideal.Quotient.mk _ (s * b j) := by
      simp [Algebra.coe_lmul_eq_mul]
    rw [hmul, IsLocalRing.basisQuotient_repr]
    simp [Algebra.coe_lmul_eq_mul]
  change (Algebra.lmul (R ⧸ IsLocalRing.maximalIdeal R)
        (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (Ideal.Quotient.mk _ s)).charpoly
      = (Algebra.lmul R S s).charpoly.map
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))
  rw [← LinearMap.charpoly_toMatrix _ (IsLocalRing.basisQuotient b),
    ← LinearMap.charpoly_toMatrix _ b, hmat, Matrix.charpoly_map]

end QuotientMaximalIdeal

section MapRingEquiv

variable {k k' E : Type*} [Field k] [Field k'] [CommRing E]
  [Algebra k' E] [Module.Finite k' E]

/-- **Field-equivalence transport of a left-multiplication characteristic polynomial.**

Let k,k′ be fields, φ:k≃+*k′ and E a commutative finite-dimensional k′-algebra. Regard E as a
k-algebra by c↦algebraMap(k′,E)(φ(c)). For x∈E, χ_k(L_x) mapped coefficientwise by φ equals
χ_(k′)(L_x).
-/
theorem charpoly_lmul_map_ringEquiv (φ : k ≃+* k') (x : E) :
    letI : Algebra k E :=
      ((algebraMap k' E).comp φ.toRingHom).toAlgebra
    let _ : Module.Finite k E :=
      Module.Finite.of_basis ((Module.finBasis k' E).mapCoeffs φ.symm
        (fun c y => by
          have hmap : algebraMap k E
              = (algebraMap k' E).comp φ.toRingHom := rfl
          simp only [hmap, Algebra.smul_def, RingHom.comp_apply]
          change algebraMap k' E (φ (φ.symm c)) * y
            = algebraMap k' E c * y
          rw [RingEquiv.apply_symm_apply]))
    (Algebra.lmul k E x).charpoly.map φ.toRingHom
      = (Algebra.lmul k' E x).charpoly := by
  classical
  let _ : Algebra k E :=
    ((algebraMap k' E).comp φ.toRingHom).toAlgebra
  have hsmul : ∀ (c : k) (y : E), c • y = φ c • y := fun c y => by
    have hmap : algebraMap k E
        = (algebraMap k' E).comp φ.toRingHom := rfl
    simp only [hmap, Algebra.smul_def, RingHom.comp_apply]
    rfl
  let b := Module.finBasis k' E
  let b' := b.mapCoeffs φ.symm (fun c y => by
    simpa only [RingEquiv.apply_symm_apply] using hsmul (φ.symm c) y)
  have _ : Module.Finite k E :=
    Module.Finite.of_basis b'
  have hmat : LinearMap.toMatrix b'
        b' (Algebra.lmul k E x)
      = (LinearMap.toMatrix b b (Algebra.lmul k' E x)).map
          φ.symm.toRingHom := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply,
      LinearMap.toMatrix_apply]
    simp only [b', Module.Basis.mapCoeffs_apply, Module.Basis.mapCoeffs_repr,
      Algebra.coe_lmul_eq_mul]
    rfl
  have key : (Algebra.lmul k E x).charpoly
      = (Algebra.lmul k' E x).charpoly.map φ.symm.toRingHom := by
    rw [← LinearMap.charpoly_toMatrix _ b',
      ← LinearMap.charpoly_toMatrix _ b, hmat, Matrix.charpoly_map]
  have hcomp : φ.toRingHom.comp φ.symm.toRingHom = RingHom.id k' := by
    ext a
    simp
  change (Algebra.lmul k E x).charpoly.map φ.toRingHom
    = (Algebra.lmul k' E x).charpoly
  rw [key, Polynomial.map_map, hcomp, Polynomial.map_id]

end MapRingEquiv

end Algebra
