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
# Characteristic polynomials under quotient and base-ring equivalence

* `Algebra.charpoly_lmul_quotient_maximalIdeal_map`: over a local
  ring `R`, the characteristic polynomial of left multiplication by the
  class of `s` on the special fiber `S ⧸ 𝔪S` is the reduction modulo
  `𝔪` of the characteristic polynomial of left multiplication by `s`
  on `S`.
* `Algebra.charpoly_lmul_map_ringEquiv`: if the scalars of an
  algebra are reindexed along a ring equivalence `φ : k ≃+* k'`, the
  characteristic polynomial of left multiplication is mapped along
  `φ`.

Both proofs compare matrices in corresponding bases: the reduced basis
`IsLocalRing.basisQuotient` in the first case, and the transferred
basis `Module.Basis.mapCoeffs` (the same vectors, with coordinates
reindexed along `φ.symm`) in the second; in each case the matrices
differ entrywise by the relevant ring homomorphism and
`Matrix.charpoly_map` concludes.

The freeness and finiteness instances needed to *form* the
characteristic polynomials in the statements are not automatic (the
quotient module is free only because `basisQuotient` is a basis, and
finiteness over the reindexed scalars only because a transferred basis
is still finite), so they are supplied explicitly by `let` in the
statements from those bases.  Both classes are propositions, so clients
whose context provides different instance terms can still apply the
lemmas up to defeq.
-/

@[expose] public section

set_option autoImplicit false

open Polynomial

namespace Algebra

section QuotientMaximalIdeal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [Module.Finite R S] [Module.Free R S]

/-- Quotient base-change for the characteristic polynomial of left
multiplication: over a local ring `R` with maximal ideal `𝔪`,
the characteristic polynomial of left multiplication by the class of
`s` on `S ⧸ 𝔪S` over the residue field `R ⧸ 𝔪` is the reduction
modulo `𝔪` of the characteristic polynomial of left multiplication by
`s` on `S`. -/
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

/-- Characteristic polynomial of left multiplication under a base-ring
equivalence: if `E` is viewed as a `k`-algebra along
`φ : k ≃+* k'`, then mapping the `k`-characteristic polynomial of left
multiplication by `x` along `φ` gives the `k'`-characteristic
polynomial of left multiplication by `x`. -/
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
