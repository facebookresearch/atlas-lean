/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveScheme
public import MathlibExt.AlgebraicGeometry.ProjectiveSpectrum.IsIntegral
public import MathlibExt.AlgebraicGeometry.ProjectiveSpectrum.Dimension
public import MathlibExt.RingTheory.Ideal.IntegralKrullDim
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field

/-!
# The projective Weierstrass curve is proper, and an integral curve over a field

Let `W` be a Weierstrass curve over a commutative ring `R`, with homogeneous coordinate ring
`S_W = R[X, Y, Z] / (F)` graded by total degree. We prove:

* `WeierstrassCurve.gradeZeroEquiv`: `R → (S_W)₀` is a ring isomorphism, for every `R`; the degree
  `0` part of `S_W` consists of the classes of constants, and `(F) ∩ R = 0` since `F` is
  homogeneous of degree `3`.
* `WeierstrassCurve.isProper_projectiveSchemeToSpec`: `Proj S_W → Spec R` is proper, for every
  commutative ring `R`.
* `WeierstrassCurve.isIntegral_projectiveScheme`: if `R` is a domain with unique factorization
  (e.g. a field), `Proj S_W` is an integral scheme.
* `WeierstrassCurve.topologicalKrullDim_projectiveScheme`: over a field, `Proj S_W` has topological
  Krull dimension `1`.

## References

* B. Conrad, "Minimal models for elliptic curves", notes (version of 21 November 2015), §2, p. 2.
* J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, Chapter II, §1, p. 46.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The constant coefficient of the homogeneous Weierstrass polynomial is `0`. -/
private theorem constantCoeff_polynomial : constantCoeff W.toProjective.polynomial = 0 := by
  rw [constantCoeff_eq]
  exact (Projective.isHomogeneous_polynomial _).coeff_eq_zero (by simp)

/-- **The degree zero part of `S_W` is `R`.** For a Weierstrass curve `W` over any commutative ring
`R`, the structure map `R → (S_W)₀` into the degree `0` part of `S_W = R[X, Y, Z] / (F)` is
bijective: `(S_W)₀` is the image of the constants, and a constant lying in `(F)` is `0` because
`F` has constant coefficient `0`. -/
theorem bijective_algebraMap_gradeZero :
    Function.Bijective (algebraMap R (W.projectiveGrading 0)) := by
  constructor
  · intro r s hrs
    rw [← sub_eq_zero, ← map_sub] at hrs
    rw [← sub_eq_zero]
    have h := congrArg Subtype.val hrs
    change Ideal.Quotient.mk _ (C (r - s)) = 0 at h
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have := congrArg constantCoeff hg
    rwa [map_mul, constantCoeff_polynomial, mul_zero, constantCoeff_C, eq_comm] at this
  · rintro ⟨_, p, hp, rfl⟩
    have hp' : p.IsHomogeneous 0 := (mem_homogeneousSubmodule _ _).mp hp
    refine ⟨p.coeff 0, Subtype.ext ?_⟩
    change Ideal.Quotient.mk _ (C (p.coeff 0)) = Ideal.Quotient.mk _ p
    rw [← totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hp'.totalDegree_le)]

/-- **The degree zero part of `S_W` is `R`**, as a ring isomorphism `R ≃+* (S_W)₀`, for a
Weierstrass curve over any commutative ring. -/
noncomputable def gradeZeroEquiv : R ≃+* W.projectiveGrading 0 :=
  RingEquiv.ofBijective (algebraMap R (W.projectiveGrading 0)) W.bijective_algebraMap_gradeZero

instance : IsScalarTower R (W.projectiveGrading 0) W.HomogeneousCoordinateRing :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := W.projectiveGrading 0)
    (A := W.HomogeneousCoordinateRing) fun _ => rfl

/-- `S_W` is of finite type over its degree zero part. -/
instance finiteType_gradeZero :
    Algebra.FiniteType (W.projectiveGrading 0) W.HomogeneousCoordinateRing :=
  Algebra.FiniteType.of_restrictScalars_finiteType R _ _

/-- **The projective Weierstrass curve is proper.** For a Weierstrass curve `W` over any commutative
ring `R`, the structure morphism `Proj S_W → Spec R` is proper: `Proj S_W → Spec (S_W)₀` is proper
since `S_W` is of finite type over `(S_W)₀`, and `Spec (S_W)₀ → Spec R` is a closed immersion
(indeed an isomorphism, `WeierstrassCurve.gradeZeroEquiv`). (B. Conrad, "Minimal models for
elliptic curves", §2, p. 2; J. S. Milne, *Elliptic Curves*, 2nd ed., Ch. II, §1, p. 46.) -/
instance isProper_projectiveSchemeToSpec : IsProper W.projectiveSchemeToSpec := by
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap R (W.projectiveGrading 0)))) :=
    IsClosedImmersion.spec_of_surjective _ W.bijective_algebraMap_gradeZero.2
  unfold projectiveSchemeToSpec
  infer_instance

/-- Over a nontrivial ring, the coordinate `Y` is nonzero in `S_W`: evaluating at the point
`(0 : 1 : 0)`, where `F` vanishes, sends `Y` to `1`. -/
theorem projectiveCoordinate_one_ne_zero [Nontrivial R] : W.projectiveCoordinate 1 ≠ 0 := by
  intro h
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have := congrArg (eval ![0, 1, 0]) hg
  rw [map_mul, Projective.eval_polynomial] at this
  simp at this

/-- `S_W` has a nonzero homogeneous element of positive degree (the coordinate `Y`) over a
nontrivial ring. -/
theorem exists_ne_zero_of_pos [Nontrivial R] :
    ∃ i, 0 < i ∧ ∃ a ∈ W.projectiveGrading i, a ≠ 0 :=
  ⟨1, one_pos, _, W.projectiveCoordinate_mem 1, W.projectiveCoordinate_one_ne_zero⟩

/-- **The projective Weierstrass curve is integral.** For a Weierstrass curve `W` (of any
discriminant) over a domain `R` with unique factorization, in particular over a field, the scheme
`Proj S_W` is integral: `S_W` is a domain
(`WeierstrassCurve.Projective.isDomain_quotient_span_polynomial`) with the nonzero degree one
element `Y`. (B. Conrad, "Minimal models for elliptic curves", §2, p. 2: the special fiber is
irreducible and reduced; J. S. Milne, *Elliptic Curves*, 2nd ed., Ch. II, §1, p. 46.) The
density of the affine chart over a field is
`WeierstrassCurve.isIntegral_isProper_dim_one_dense_affineChart`; geometric integrality is not
asserted here. -/
theorem isIntegral_projectiveScheme [IsDomain R] [UniqueFactorizationMonoid R] :
    IsIntegral W.ProjectiveScheme := by
  have : IsDomain W.HomogeneousCoordinateRing :=
    Projective.isDomain_quotient_span_polynomial W.toProjective
  exact Proj.isIntegral_of_isDomain _ W.exists_ne_zero_of_pos

/-- Over a field, the projective Weierstrass curve is an integral scheme. -/
instance isIntegral_projectiveScheme_of_field {F : Type u} [Field F] (W : WeierstrassCurve F) :
    IsIntegral W.ProjectiveScheme :=
  W.isIntegral_projectiveScheme

/-- Over a nontrivial ring, `Z ∉ (F)` in `R[X, Y, Z]`: the coefficient of `Z` in a multiple of
the cubic form `F` is `0`. -/
theorem X_two_not_mem_span [Nontrivial R] :
    (X 2 : MvPolynomial (Fin 3) R) ∉ Ideal.span {W.toProjective.polynomial} := by
  intro h
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp h
  have := congrArg (fun p : MvPolynomial (Fin 3) R => p.coeff (Finsupp.single 2 1)) hg
  simp only [coeff_X, coeff_mul] at this
  rw [Finset.sum_eq_zero] at this
  · exact zero_ne_one this
  · intro x hx
    have hd := congrArg Finsupp.degree (Finset.mem_antidiagonal.mp hx)
    rw [map_add, Finsupp.degree_single] at hd
    rw [(Projective.isHomogeneous_polynomial _).coeff_eq_zero (by omega), mul_zero]

/-- Over a domain, `(X, Z)` is a prime ideal of `R[X, Y, Z]`: the kernel of `X, Z ↦ 0`. -/
theorem isPrime_span_X_zero_X_two [IsDomain R] :
    (Ideal.span {X 0, X 2} : Ideal (MvPolynomial (Fin 3) R)).IsPrime := by
  classical
  have := MvPolynomial.span_X_image_eq_ker_aeval_ite_mem (R := R) ({0, 2} : Set (Fin 3))
  rw [Set.image_pair] at this
  rw [this]
  exact RingHom.ker_isPrime _

/-- Over a nontrivial ring, `Y ∉ (X, Z)` in `R[X, Y, Z]`. -/
theorem X_one_not_mem_span_X_zero_X_two [Nontrivial R] :
    (X 1 : MvPolynomial (Fin 3) R) ∉ Ideal.span {X 0, X 2} := by
  classical
  have := MvPolynomial.span_X_image_eq_ker_aeval_ite_mem (R := R) ({0, 2} : Set (Fin 3))
  rw [Set.image_pair] at this
  rw [this, RingHom.mem_ker]
  simp [X_ne_zero]

/-- The Weierstrass cubic form lies in `(X, Z)`: the point `(0 : 1 : 0)` is on the curve. -/
theorem polynomial_mem_span_X_zero_X_two :
    W.toProjective.polynomial ∈ (Ideal.span {X 0, X 2} : Ideal (MvPolynomial (Fin 3) R)) := by
  rw [Ideal.mem_span_pair]
  refine ⟨-X 0 ^ 2, X 1 ^ 2 + C W.a₁ * X 0 * X 1 + C W.a₃ * X 1 * X 2 - C W.a₂ * X 0 ^ 2 -
    C W.a₄ * X 0 * X 2 - C W.a₆ * X 2 ^ 2, ?_⟩
  simp only [Projective.polynomial]
  simp
  ring

/-- The ring map `R[Y, Z] → S_W` (variables `0, 1` of `R[Y, Z]` sent to the classes of `Y, Z`),
over which `S_W` is integral. -/
noncomputable def yzHom : MvPolynomial (Fin 2) R →+* W.HomogeneousCoordinateRing :=
  (Ideal.Quotient.mk _).comp (rename ![1, 2]).toRingHom

/-- The class of `X` is integral over `R[Y, Z]`: it is a root of the monic cubic
`T³ + a₂ Z T² + (a₄ Z² - a₁ Y Z) T + (a₆ Z³ - Y² Z - a₃ Y Z²)`, i.e. of `-F` read in `T = X`. -/
theorem isIntegral_X0 :
    let := W.yzHom.toAlgebra
    IsIntegral (MvPolynomial (Fin 2) R) (W.projectiveCoordinate 0) := by
  let := W.yzHom.toAlgebra
  refine ⟨Polynomial.X ^ 3 + Polynomial.C (C W.a₂ * X 1) * Polynomial.X ^ 2 +
    Polynomial.C (C W.a₄ * X 1 ^ 2 - C W.a₁ * X 0 * X 1) * Polynomial.X +
    Polynomial.C (C W.a₆ * X 1 ^ 3 - X 0 ^ 2 * X 1 - C W.a₃ * X 0 * X 1 ^ 2), ?_, ?_⟩
  · monicity!
  · have key : ∀ p, algebraMap (MvPolynomial (Fin 2) R) W.HomogeneousCoordinateRing p =
        Ideal.Quotient.mk _ (rename ![1, 2] p) := fun _ => rfl
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, key, projectiveCoordinate, ← map_pow, ← map_mul,
      ← map_add, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    exact ⟨-1, by simp [Projective.polynomial]; ring⟩

/-- `S_W` is integral over `R[Y, Z]` (via `WeierstrassCurve.yzHom`). -/
theorem isIntegral_mk :
    let := W.yzHom.toAlgebra
    Algebra.IsIntegral (MvPolynomial (Fin 2) R) W.HomogeneousCoordinateRing := by
  let := W.yzHom.toAlgebra
  have key : ∀ p, algebraMap (MvPolynomial (Fin 2) R) W.HomogeneousCoordinateRing p =
      Ideal.Quotient.mk _ (rename ![1, 2] p) := fun _ => rfl
  refine ⟨fun x => ?_⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C a =>
    have : Ideal.Quotient.mk (Ideal.span {W.toProjective.polynomial}) (C a) =
        algebraMap (MvPolynomial (Fin 2) R) W.HomogeneousCoordinateRing (C a) := by
      rw [key, rename_C]
    rw [this]
    exact isIntegral_algebraMap
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p i hp =>
    rw [map_mul]
    refine hp.mul ?_
    fin_cases i
    · exact W.isIntegral_X0
    · have : Ideal.Quotient.mk (Ideal.span {W.toProjective.polynomial}) (X 1) =
          algebraMap (MvPolynomial (Fin 2) R) W.HomogeneousCoordinateRing (X 0) := by
        rw [key, rename_X]; rfl
      simp only [Fin.mk_one, Fin.isValue]
      rw [this]
      exact isIntegral_algebraMap
    · have : Ideal.Quotient.mk (Ideal.span {W.toProjective.polynomial}) (X 2) =
          algebraMap (MvPolynomial (Fin 2) R) W.HomogeneousCoordinateRing (X 1) := by
        rw [key, rename_X]; rfl
      simp only [Fin.reduceFinMk, Fin.isValue]
      rw [this]
      exact isIntegral_algebraMap

/-- For a Weierstrass curve over a Noetherian ring `R`, `dim S_W ≤ dim R + 2`, since `S_W` is
integral over `R[Y, Z]`. -/
theorem ringKrullDim_le [IsNoetherianRing R] :
    ringKrullDim W.HomogeneousCoordinateRing ≤ ringKrullDim R + 2 := by
  let := W.yzHom.toAlgebra
  have := W.isIntegral_mk
  refine (ringKrullDim_le_of_integral (A := MvPolynomial (Fin 2) R)
    (B := W.HomogeneousCoordinateRing)).trans ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
  simp

/-- **The generic point of the image of the infinity section** of `Proj S_W`, over a domain: the
relevant homogeneous prime ideal `(X, Z)` of `S_W`. Over a field it is the point `(0 : 1 : 0)`;
over a domain that is not a field it is the generic point of the image of `zeroSection`, not the
whole section. -/
noncomputable def pointO [IsDomain R] : ProjectiveSpectrum W.projectiveGrading :=
  ⟨⟨Ideal.span {W.projectiveCoordinate 0, W.projectiveCoordinate 2},
    Ideal.homogeneous_span _ _ (by
      rintro _ (rfl | rfl)
      · exact ⟨1, W.projectiveCoordinate_mem 0⟩
      · exact ⟨1, W.projectiveCoordinate_mem 2⟩)⟩, by
    have hmap : Ideal.span {W.projectiveCoordinate 0, W.projectiveCoordinate 2} =
        (Ideal.span {X 0, X 2}).map
          (Ideal.Quotient.mk (Ideal.span {W.toProjective.polynomial})) := by
      rw [Ideal.map_span, Set.image_pair]; rfl
    change (Ideal.span {W.projectiveCoordinate 0, W.projectiveCoordinate 2}).IsPrime
    rw [hmap]
    have := isPrime_span_X_zero_X_two (R := R)
    refine Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective ?_
    rw [Ideal.mk_ker, Ideal.span_le, Set.singleton_subset_iff]
    exact W.polynomial_mem_span_X_zero_X_two, by
    intro hle
    have h1 : W.projectiveCoordinate 1 ∈ HomogeneousIdeal.irrelevant W.projectiveGrading := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne _ (W.projectiveCoordinate_mem 1) one_ne_zero]
    have h2 := hle h1
    change W.projectiveCoordinate 1 ∈
      Ideal.span {W.projectiveCoordinate 0, W.projectiveCoordinate 2} at h2
    have hmap : Ideal.span {W.projectiveCoordinate 0, W.projectiveCoordinate 2} =
        (Ideal.span {X 0, X 2}).map
          (Ideal.Quotient.mk (Ideal.span {W.toProjective.polynomial})) := by
      rw [Ideal.map_span, Set.image_pair]; rfl
    rw [hmap] at h2
    change Ideal.Quotient.mk _ (X 1) ∈ _ at h2
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, sup_eq_left.mpr (by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact W.polynomial_mem_span_X_zero_X_two)] at h2
    exact X_one_not_mem_span_X_zero_X_two h2⟩

/-- Over a factorial domain, the generic point of `Proj S_W` (the zero ideal) is strictly below the
point `(0 : 1 : 0)`, i.e. `(0 : 1 : 0)` is a proper specialization of the generic point. -/
theorem botPoint_lt_pointO [IsDomain R] [UniqueFactorizationMonoid R] :
    letI : IsDomain W.HomogeneousCoordinateRing :=
      Projective.isDomain_quotient_span_polynomial W.toProjective
    ProjectiveSpectrum.botPoint W.projectiveGrading W.exists_ne_zero_of_pos < W.pointO := by
  let : IsDomain W.HomogeneousCoordinateRing :=
    Projective.isDomain_quotient_span_polynomial W.toProjective
  refine lt_of_le_of_ne (show (⊥ : HomogeneousIdeal W.projectiveGrading) ≤ _ from bot_le)
    fun heq => ?_
  have hmem : W.projectiveCoordinate 2 ∈ (W.pointO).asHomogeneousIdeal :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  rw [← heq] at hmem
  change W.projectiveCoordinate 2 ∈ (⊥ : HomogeneousIdeal W.projectiveGrading).toIdeal at hmem
  rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at hmem
  exact W.X_two_not_mem_span (Ideal.Quotient.eq_zero_iff_mem.mp hmem)

/-- **The projective Weierstrass curve over a field is a curve.** For a Weierstrass curve `W` (of
any discriminant) over a field `F`, the topological Krull dimension of `Proj S_W` is `1`. Upper
bound: `S_W` is integral over `F[Y, Z]`, so `dim S_W ≤ 2`, and every chain of relevant homogeneous
primes extends by one in `S_W`; lower bound: the zero ideal is strictly contained in the relevant
homogeneous prime `(X, Z)` (the point `(0 : 1 : 0)`). (B. Conrad, "Minimal models for elliptic
curves", §2, p. 2, "the 1-dimensional special fiber"; J. S. Milne, *Elliptic Curves*, 2nd ed.,
Ch. II, §1, p. 46.) -/
theorem topologicalKrullDim_projectiveScheme {F : Type u} [Field F] (W : WeierstrassCurve F) :
    topologicalKrullDim W.ProjectiveScheme = 1 := by
  have : IsDomain W.HomogeneousCoordinateRing :=
    Projective.isDomain_quotient_span_polynomial W.toProjective
  have hlt : topologicalKrullDim W.ProjectiveScheme < (2 : ℕ) := by
    refine Proj.topologicalKrullDim_lt _ ?_
    refine W.ringKrullDim_le.trans ?_
    rw [ringKrullDim_eq_zero_of_field]
    rfl
  have hpos : 0 < topologicalKrullDim W.ProjectiveScheme := by
    rw [Proj.topologicalKrullDim_eq, Order.krullDim_pos_iff]
    exact ⟨_, _, W.botPoint_lt_pointO⟩
  generalize topologicalKrullDim W.ProjectiveScheme = d at hlt hpos
  induction d using WithBot.recBotCoe with
  | bot => exact absurd hpos (not_lt_of_ge bot_le)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd hlt (by simp)
    | coe k =>
      have h1' : (k : WithBot ℕ∞) < (2 : ℕ) := hlt
      have h2' : ((0 : ℕ) : WithBot ℕ∞) < k := hpos
      have h1 : k < 2 := Nat.cast_lt.mp h1'
      have h2 : 0 < k := Nat.cast_lt.mp h2'
      have : k = 1 := by omega
      subst this
      rfl

end WeierstrassCurve
