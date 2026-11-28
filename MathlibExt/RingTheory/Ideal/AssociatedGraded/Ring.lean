/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.Module.Torsion.Basic
public import MathlibExt.RingTheory.Ideal.AssociatedGraded.Basic

/-!
# The quotient coefficient algebra of an associated graded ring

For an ideal `I` in a commutative ring `R`, the associated graded ring is `⨁ n : ℕ,
I^n/I^(n+1)` with product `[x]_m [y]_n = [xy]_(m+n)`. Its degree-zero piece is `R/I`.

The quotient coefficient `r mod I` enters as the degree-zero initial form `[r]_0`, and its
action on degree `n` is `(r mod I) • [x]_n = [rx]_n`. These maps give the graded algebra
structure over `R/I`.

Reference: Atiyah and Macdonald, *Introduction to Commutative Algebra*, Chapter 10.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace Ideal

variable {R : Type u} [CommRing R]

private theorem idealPow_cast_coe (I : Ideal R) {m n : ℕ} (h : m = n)
    (x : (I ^ m : Ideal R)) :
    ((cast (congrArg (fun k => ((I ^ k : Ideal R) : Type u)) h) x :
      (I ^ n : Ideal R)) : R) = x := by
  subst h
  rfl

private theorem initialForm_cast (I : Ideal R) {m n : ℕ} (h : m = n)
    (x : (I ^ m : Ideal R)) :
    cast (congrArg (AssociatedGradedPiece I) h) (initialForm I m x) =
      initialForm I n
        (cast (congrArg (fun k => ((I ^ k : Ideal R) : Type u)) h) x) := by
  subst h
  rfl

private def degreeZeroRaw (I : Ideal R) :
    R →ₗ[R] AssociatedGradedPiece I 0 where
  toFun r := initialForm I 0 ⟨r, by simp⟩
  map_add' r s := by
    rw [← map_add]
    congr 1
  map_smul' r s := by
    rw [← map_smul]
    congr 1

private theorem le_degreeZeroRaw_ker (I : Ideal R) :
    (I : Submodule R R) ≤ (degreeZeroRaw I).ker := by
  intro r hr
  rw [LinearMap.mem_ker]
  change initialForm I 0 ⟨r, by simp⟩ = 0
  rw [initialForm_eq_zero_iff]
  simpa using hr

private def degreeZeroMapR (I : Ideal R) :
    (R ⧸ I) →ₗ[R] AssociatedGradedPiece I 0 :=
  I.liftQ (degreeZeroRaw I) (le_degreeZeroRaw_ker I)

private def degreeZeroMap (I : Ideal R) :
    (R ⧸ I) →ₗ[R ⧸ I] AssociatedGradedPiece I 0 :=
  (degreeZeroMapR I).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

@[simp]
private theorem degreeZeroMap_mk (I : Ideal R) (r : R) :
    degreeZeroMap I (Ideal.Quotient.mk I r) =
      initialForm I 0 ⟨r, by simp⟩ :=
  rfl

private theorem degreeZeroMap_bijective (I : Ideal R) :
    Function.Bijective (degreeZeroMap I) := by
  constructor
  · intro a b hab
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
    apply Ideal.Quotient.eq.mpr
    have hz :
        initialForm I 0 (⟨r - s, by simp⟩ : (I ^ 0 : Ideal R)) = 0 := by
      rw [show initialForm I 0 (⟨r - s, by simp⟩ : (I ^ 0 : Ideal R)) =
        initialForm I 0 ⟨r, by simp⟩ - initialForm I 0 ⟨s, by simp⟩ by
          rw [← map_sub]
          congr 1]
      rw [← degreeZeroMap_mk, ← degreeZeroMap_mk, hab, sub_self]
    simpa using (initialForm_eq_zero_iff I 0 _).mp hz
  · intro a
    obtain ⟨x, hx⟩ := initialForm_surjective I 0 a
    refine ⟨Ideal.Quotient.mk I x, ?_⟩
    rw [degreeZeroMap_mk]
    exact hx

/-- For an ideal `I` in a commutative ring `R`, `associatedGradedDegreeZeroEquiv I` is the
`R/I`-linear equivalence `R/I ≃ₗ[R/I] I.AssociatedGradedPiece 0`. It sends `r mod I` to the
degree-zero class `[r]_0`, using `I^0 = R`. -/
@[no_expose]
noncomputable def associatedGradedDegreeZeroEquiv (I : Ideal R) :
    (R ⧸ I) ≃ₗ[R ⧸ I] AssociatedGradedPiece I 0 :=
  LinearEquiv.ofBijective (degreeZeroMap I) (degreeZeroMap_bijective I)

@[simp]
theorem associatedGradedDegreeZeroEquiv_mk (I : Ideal R) (r : R) :
    associatedGradedDegreeZeroEquiv I (Ideal.Quotient.mk I r) =
      initialForm I 0 ⟨r, by simp⟩ := by
  rw [associatedGradedDegreeZeroEquiv]
  rfl

theorem associatedGradedDegreeZeroEquiv_symm_initialForm
    (I : Ideal R) (x : (I ^ 0 : Ideal R)) :
    (associatedGradedDegreeZeroEquiv I).symm (initialForm I 0 x) =
      Ideal.Quotient.mk I x := by
  apply (associatedGradedDegreeZeroEquiv I).injective
  rw [LinearEquiv.apply_symm_apply, associatedGradedDegreeZeroEquiv_mk]

private theorem associatedGradedGAlgebra_map_one (I : Ideal R) :
    (associatedGradedDegreeZeroEquiv I).toLinearMap.toAddMonoidHom 1 =
      GradedMonoid.GOne.one := by
  change associatedGradedDegreeZeroEquiv I 1 =
    initialForm I 0 ⟨1, by simp⟩
  rw [show (1 : R ⧸ I) = Ideal.Quotient.mk I 1 by rfl,
    associatedGradedDegreeZeroEquiv_mk]

private theorem associatedGradedGAlgebra_map_mul (I : Ideal R)
    (r s : R ⧸ I) :
    GradedMonoid.mk 0
        ((associatedGradedDegreeZeroEquiv I).toLinearMap.toAddMonoidHom (r * s)) =
      GradedMonoid.mk (0 + 0)
        (GradedMonoid.GMul.mul
          ((associatedGradedDegreeZeroEquiv I).toLinearMap.toAddMonoidHom r)
          ((associatedGradedDegreeZeroEquiv I).toLinearMap.toAddMonoidHom s)) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  change GradedMonoid.mk 0
      (associatedGradedDegreeZeroEquiv I (Ideal.Quotient.mk I (r * s))) =
    GradedMonoid.mk (0 + 0)
      (adicGradedMul I 0 0
        (associatedGradedDegreeZeroEquiv I (Ideal.Quotient.mk I r))
        (associatedGradedDegreeZeroEquiv I (Ideal.Quotient.mk I s)))
  rw [associatedGradedDegreeZeroEquiv_mk,
    associatedGradedDegreeZeroEquiv_mk,
    associatedGradedDegreeZeroEquiv_mk,
    show I.initialForm = I.adicSymbol from rfl,
    adicGradedMul_symbol]

private theorem associatedGradedGAlgebra_smul_def (I : Ideal R)
    (r : R ⧸ I) (x : GradedMonoid (AssociatedGradedPiece I)) :
    r • x =
      GradedMonoid.mk 0
        ((associatedGradedDegreeZeroEquiv I).toLinearMap.toAddMonoidHom r) * x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨n, x⟩ := x
  obtain ⟨y, hy⟩ := initialForm_surjective I n x
  subst x
  apply Sigma.ext (zero_add n).symm
  change HEq
    (Ideal.Quotient.mk I r • initialForm I n y)
    (adicGradedMul I 0 n
      (associatedGradedDegreeZeroEquiv I (Ideal.Quotient.mk I r))
      (initialForm I n y))
  rw [associatedGradedDegreeZeroEquiv_mk,
    show I.initialForm = I.adicSymbol from rfl,
    adicGradedMul_symbol]
  rw [adicSymbol_apply, Module.Quotient.mk_smul_mk]
  change HEq (initialForm I n
      ⟨r • y, (I ^ n : Ideal R).smul_mem r y.2⟩)
    (initialForm I (0 + n)
      ⟨(r : R) * y, by
        rw [pow_add]
        exact Ideal.mul_mem_mul (by simp) y.2⟩)
  refine heq_of_cast_eq
    (congrArg (AssociatedGradedPiece I) (zero_add n).symm) ?_
  rw [initialForm_cast I (zero_add n).symm]
  apply congrArg (initialForm I (0 + n))
  apply Subtype.ext
  rw [idealPow_cast_coe I (zero_add n).symm]
  exact smul_eq_mul r y

/-- For an ideal `I` in a commutative ring `R`, the family `n ↦ I.AssociatedGradedPiece n` is a
graded algebra over `R/I`. The coefficient map sends `r mod I` to `[r]_0`, and scalar
multiplication on a homogeneous class is `(r mod I) • [x]_n = [rx]_n`. -/
@[no_expose]
noncomputable instance associatedGradedGAlgebra (I : Ideal R) :
    DirectSum.GAlgebra (R ⧸ I) (AssociatedGradedPiece I) := by
  exact {
    toFun := (associatedGradedDegreeZeroEquiv I).toLinearMap.toAddMonoidHom
    map_one := associatedGradedGAlgebra_map_one I
    map_mul := associatedGradedGAlgebra_map_mul I
    commutes := fun r x =>
      @DirectSum.GCommSemiring.mul_comm ℕ I.AssociatedGradedPiece
        inferInstance (fun _ => inferInstance)
        (I.instGCommRingAdicGradedPiece.toGCommSemiring) _ x
    smul_def := associatedGradedGAlgebra_smul_def I }

/-- For an ideal `I` in a commutative ring `R` and `r : R`, `(associatedGradedGAlgebra I).toFun
(Ideal.Quotient.mk I r)` is the degree-zero class `[r]_0` in `I.AssociatedGradedPiece 0`.
Equivalently, it is `initialForm I 0 x`, where `x : I^0` has underlying value `r`. -/
@[simp]
theorem associatedGradedGAlgebra_toFun_mk (I : Ideal R) (r : R) :
    (associatedGradedGAlgebra I).toFun (Ideal.Quotient.mk I r) =
      initialForm I 0 ⟨r, by simp⟩ := by
  exact associatedGradedDegreeZeroEquiv_mk I r

end Ideal
