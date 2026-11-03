/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Statement
import Mathlib.Algebra.GroupWithZero.Action.Regular
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Regular.SMul
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Triangular regularity for `mkSystem`-shaped systems via `z`-linearity

Alternative regularity track for the cone over `Gᵢ = Fᵢ(x) − z·xᵢ` (the
`mkSystem` shape from `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
with
arbitrary `Fᵢ` in the `x` variables — in particular general quadratics, cross
terms allowed — over `[Field K]`; no `IsAlgClosed` needed). Every step is
elementary UFD/domain arithmetic in the
`z`-linear model `S[Z] ∋ C F − C a * X`; no unmixedness, catenary, or hit
arguments are used.

## What is proved

* (t1) `mkSystem_ne_zero` / `mkSystem_isSMulRegular`: each `Gᵢ ≠ 0` (the
  `−z·xᵢ` term carries the monomial `z¹xᵢ¹`, which cannot occur in the
  `z`-free lift of `Fᵢ`), hence regular on the domain `R`.
* (t2a) `triG_prime_of_not_dvd` + `triG_isSMulRegular_mod_of_not_dvd`: if
  `x₀ ∤ F₀` then `G₀` is prime (a `deg_z` argument: any factorization forces a
  constant factor dividing both `x₀` and `F₀`, hence a unit), so `R/(G₀)` is a
  domain; and `G₁ ∉ (G₀)` (any quotient would be constant by degree, forcing
  `x₀ ∣ x₁`), hence `G₁` is regular mod `(G₀)`.
* (t2b) `triG_isSMulRegular_mod_of_dvd`: if `x₀ ∣ F₀` (write `F₀ = x₀·L₀`) and
  the minor `M = x₀·F₁ − x₁·F₀` is nonzero, then `G₁` is regular mod `(G₀)` by
  monic-prime division through `(L₀ − z)`, back-substitution, cancellation of
  `(L₀ − z)` in the domain, and primality of `x₀` (using `x₀ ∤ G₁`, which holds
  for distinct variables).
* (t2c) `triG_common_factor_of_minor_zero`: if `x₀ ∣ F₀` and the minor
  vanishes, then `F₁ = x₁·L₀` (all forms share the cofactor). The
  locus-dimension consequence — all `Gⱼ` then share `(L₀ − z)`, so the locus
  contains a `ℙⁿ`-section, contradicting zero-dimensionality for `n ≥ 1` — is
  stated here as a precise remark; the full contradiction against
  `IsZeroDimensional` (Krull-dimension API) is a follow-up, not claimed.
* (t3) Step 3+ is assessed in the module remark below: the dichotomy does not
  iterate as stated (precise obstruction recorded). No claim about `G₂` is
  formalized here.
* Carry-back `lastVarEquiv`/`lastVarRingEquiv` (+ the arbitrary-index leg
  `shearLastEquiv`/`shearLastRingEquiv`, the generator images
  `lastVarEquiv_mkSystem`, and the transported (t2b)
  `isSMulRegular_mvPolynomial_mod_of_dvd` / `mkSystem_isSMulRegular_mod_of_dvd`):
  the last-variable isomorphism (`renameEquiv` sending `last ↦ none` composed
  with `optionEquivLeft`-style unfolding) carrying (t2b) back to `MvPolynomial`,
  in the exact shape FiberExhibit's bridge consumes. What stays with the
  consumer is only the t2b input data at the sheared fiber polynomial.

## Model correspondence

The abstract `z`-linear form `triG F a = C F − C a * X` in `S[Z]` models
`Gᵢ = Fᵢ(x) − z·xᵢ` under the last-variable identification
`R = MvPolynomial (Fin (n+2)) K ≃ S[Z]` with `S = MvPolynomial (Fin (n+1)) K`
sending `X last ↦ X`, `X (castSucc i) ↦ C (X i)`, and
`rename castSucc (F i) ↦ C (F i)`. The (t1) results are proved directly on
`mkSystem`; the (t2) dichotomy is proved in the `S[Z]` model where `deg_z`,
monic division, and Gauss-type arguments are available. The carry-back is
proved in the final section: `lastVarEquiv`/`lastVarRingEquiv` is exactly this
last-variable isomorphism, `lastVarEquiv_mkSystem` computes its values on the
`mkSystem` generators, `shearLastEquiv`/`shearLastRingEquiv` prepend the
`j ↦ last` permutation for an arbitrary `shear_idx`, and
`isSMulRegular_mvPolynomial_mod_of_dvd` transports (t2b) across any such
equivalence (with the `mkSystem` corollary). The only remainder for
FiberExhibit's instantiation is the t2b input data at the sheared fiber
polynomial (recorded there as the t2b instantiation remainder).

## (t3) verdict

Step 3 (`G₂` regular mod `(G₀, G₁)`) resists the same toolkit, and this is the
accepted result for (t3): after quotienting by the step-2 prime `(G₀)` in
case (a), the quotient `S[Z]/(G₀)` is a domain but no longer a polynomial ring
— `G₀ = C F₀ − C x₀ * X` is not monic, so there is no division algorithm, no
`deg_z`, and the image of `G₁` is not linear in any variable. The dichotomy
hypotheses (`x ∤ F`, minors) are all stated in the polynomial ring and do not
transport. In case (b) the auxiliary monic quotient `S[Z]/(X − C L₀) ≃ S` is
again a UFD, so a refined induction through the monic prime may be possible,
but the mixed-ideal bookkeeping (`(G₀, G₁)` vs `(X − C L₀, …)`) plus the minor
conditions do not close with the current lemmas. No spiral: (t3) stops here.

## References

Mathlib v4.34.0 exact names used (verified against the sources cited):
`MvPolynomial.ne_zero_iff`, `MvPolynomial.coeff_X_mul`,
`MvPolynomial.coeff_X_same`, `MvPolynomial.coeff_rename_eq_zero`,
`MvPolynomial.coeffAddMonoidHom` (`Mathlib/Algebra/MvPolynomial/Basic.lean`,
`Mathlib/Algebra/MvPolynomial/Rename.lean`);
`Finsupp.mapDomain_of_notMem_range` (`Mathlib/Data/Finsupp/Basic.lean`);
`Fin.castSucc_lt_last` (`Mathlib/Data/Fin/Basic.lean`);
`isSMulRegular_iff_right_eq_zero_of_smul`,
`IsSMulRegular.right_eq_zero_of_smul`
(`Mathlib/Algebra/GroupWithZero/Action/Regular.lean`);
`eq_zero_of_ne_zero_of_mul_left_eq_zero`
(`Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean`);
`Polynomial.lcoeff`, `Polynomial.lcoeff_apply`, `Polynomial.coeff_C_mul`,
`Polynomial.coeff_mul_C`, `Polynomial.coeff_C_mul_X`, `Polynomial.isUnit_C`
(`Mathlib/Algebra/Polynomial/Coeff.lean`);
`Polynomial.coeff_C`, `Polynomial.coeff_C_zero`, `Polynomial.C_eq_zero`
(`Mathlib/Algebra/Polynomial/Basic.lean`);
`Polynomial.natDegree_C`, `Polynomial.natDegree_X`,
`Polynomial.natDegree_C_mul_X_pow`, `Polynomial.natDegree_C_mul_X_pow_le`
(`Mathlib/Algebra/Polynomial/Degree/Defs.lean`);
`Polynomial.natDegree_mul` (`Mathlib/Algebra/Polynomial/Degree/Domain.lean`);
`Polynomial.natDegree_sub_eq_left_of_natDegree_lt`,
`Polynomial.natDegree_sub_eq_right_of_natDegree_lt`,
`Polynomial.natDegree_sub_le`, `Polynomial.eq_C_of_natDegree_eq_zero`
(`Mathlib/Algebra/Polynomial/Degree/Operations.lean`);
`Polynomial.prime_X_sub_C` (`Mathlib/Algebra/Polynomial/RingDivision.lean`);
`Polynomial.prime_C_iff` (`Mathlib/RingTheory/Polynomial/Basic.lean`);
`UniqueFactorizationMonoid.irreducible_iff_prime`
(`Mathlib/RingTheory/UniqueFactorizationDomain/Basic.lean`);
the `UniqueFactorizationMonoid (Polynomial D)` / `(MvPolynomial σ D)` instances
(`Mathlib/RingTheory/Polynomial/UniqueFactorization.lean`);
`Prime.irreducible`, `Prime.ne_zero`, `Prime.dvd_mul`
(`Mathlib/Algebra/Prime/Defs.lean`);
`Irreducible.isUnit_or_isUnit`
(`Mathlib/Algebra/Group/Irreducible/Defs.lean`);
`Polynomial.natDegree_eq_zero_of_isUnit`
(`Mathlib/Algebra/Polynomial/Degree/Units.lean`);
`Associated.dvd_iff_dvd_left`, `associated_mul_unit_left`
(`Mathlib/Algebra/GroupWithZero/Associated.lean`);
`Ideal.mem_span_singleton`, `Ideal.span_le`
(`Mathlib/RingTheory/Ideal/Span.lean`);
`Ideal.span_singleton_prime`, `Ideal.isPrime_span_singleton_of_prime`
(`Mathlib/RingTheory/Ideal/Maximal.lean`);
`Ideal.Quotient.eq_zero_iff_mem`, `Ideal.Quotient.mk_surjective`
(`Mathlib/RingTheory/Ideal/Quotient/Defs.lean`);
the `Ideal.Quotient.isDomain` instance for a prime ideal
(`Mathlib/RingTheory/Ideal/Quotient/Basic.lean`);
`finSuccEquivLast`, `finSuccEquivLast_castSucc`, `finSuccEquivLast_last`
(`Mathlib/Logic/Equiv/Fin/Basic.lean`);
`MvPolynomial.renameEquiv`, `renameEquiv_apply` (generated by `@[simps apply]`),
`MvPolynomial.rename_X`, `MvPolynomial.rename_C`
(`Mathlib/Algebra/MvPolynomial/Rename.lean`);
`MvPolynomial.optionEquivLeft`, `optionEquivLeft_X_some`,
`optionEquivLeft_X_none`, `optionEquivLeft_C`
(`Mathlib/Algebra/MvPolynomial/Equiv.lean`);
`MvPolynomial.induction_on` (`Mathlib/Algebra/MvPolynomial/Basic.lean`);
`Equiv.swap_apply_left`, `Equiv.swap_apply_right`
(`Mathlib/Logic/Equiv/Basic.lean`);
`AlgEquiv.trans_apply`, `AlgEquiv.toRingEquiv`
(`Mathlib/Algebra/Algebra/Equiv.lean`);
`Equiv.apply_symm_apply` (`toEquiv` form), `Equiv.injective`
(core/Batteries equiv API, same citations as FiberExhibit's bridge).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace Triangular

/-! ## (t1) Each `Gᵢ` is nonzero, hence regular — directly on `mkSystem`. -/

variable (n : ℕ) (K : Type*) [Field K]
  (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)

/-- (t1) Each `Gᵢ = Fᵢ(x) − z·xᵢ` is nonzero: the `−z·xᵢ` term carries the
monomial `z¹xᵢ¹` with coefficient `−1`, while the `z`-free lift of `Fᵢ` has
coefficient `0` there (`Fin.last` is outside the range of `Fin.castSucc`). -/
theorem mkSystem_ne_zero (i : Fin (n + 1)) :
    mkSystem n K F i ≠ 0 := by
  rw [MvPolynomial.ne_zero_iff]
  refine ⟨Finsupp.single (Fin.last (n + 1)) 1 +
    Finsupp.single (Fin.castSucc i) 1, ?_⟩
  have hxi : Fin.castSucc i ≠ Fin.last (n + 1) := by
    intro h
    have hlt := Fin.castSucc_lt_last i
    rw [h] at hlt
    exact lt_irrefl _ hlt
  have hlast : Fin.last (n + 1) ∉
      Set.range (Fin.castSucc : Fin (n + 1) → Fin (n + 2)) := by
    rintro ⟨j, hj⟩
    have hlt := Fin.castSucc_lt_last j
    rw [hj] at hlt
    exact lt_irrefl _ hlt
  have hren : (MvPolynomial.rename Fin.castSucc (F i)).coeff
        (Finsupp.single (Fin.last (n + 1)) 1 +
          Finsupp.single (Fin.castSucc i) 1) = 0 := by
    apply MvPolynomial.coeff_rename_eq_zero
    intro u hu
    exfalso
    have h1 : (u.mapDomain Fin.castSucc) (Fin.last (n + 1)) = 0 :=
      Finsupp.mapDomain_of_notMem_range _ _ hlast
    have h2 : (Finsupp.single (Fin.last (n + 1)) 1 +
          Finsupp.single (Fin.castSucc i) 1 : Fin (n + 2) →₀ ℕ)
        (Fin.last (n + 1)) = 1 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (Ne.symm hxi), add_zero]
    rw [hu, h2] at h1
    exact one_ne_zero h1
  have hprod : (MvPolynomial.X (Fin.last (n + 1)) *
        MvPolynomial.X (Fin.castSucc i) : MvPolynomial (Fin (n + 2)) K).coeff
        (Finsupp.single (Fin.last (n + 1)) 1 +
          Finsupp.single (Fin.castSucc i) 1) = 1 := by
    rw [MvPolynomial.coeff_X_mul]
    exact MvPolynomial.coeff_X_same _
  have hG : mkSystem n K F i = MvPolynomial.rename Fin.castSucc (F i) -
      MvPolynomial.X (Fin.last (n + 1)) * MvPolynomial.X (Fin.castSucc i) := rfl
  rw [hG, MvPolynomial.coeff_sub, hren, hprod]
  simp

/-- (t1, regularity form) Each `Gᵢ` is regular on the domain `R`: a nonzero
element of a domain is `IsSMulRegular`. -/
theorem mkSystem_isSMulRegular (i : Fin (n + 1)) :
    IsSMulRegular (MvPolynomial (Fin (n + 2)) K) (mkSystem n K F i) := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  intro m hm
  rw [smul_eq_mul] at hm
  exact eq_zero_of_ne_zero_of_mul_left_eq_zero (mkSystem_ne_zero n K F i) hm

/-! ## The abstract `z`-linear model `triG F a = C F − C a * X` in `S[Z]`.

All (t2) arguments are proved here, where `deg_z` is `Polynomial.natDegree`,
monic division is available, and Gauss-type coefficient comparisons apply.
-/

variable {S : Type*} [CommRing S] [IsDomain S] [UniqueFactorizationMonoid S]

/-- The `z`-linear form modelling `Gᵢ = Fᵢ(x) − z·xᵢ`: constant part `F`
(the quadric) and `z`-coefficient `−a` (the variable). -/
noncomputable def triG (Fc a : S) : Polynomial S :=
  Polynomial.C Fc - Polynomial.C a * Polynomial.X

omit [IsDomain S] [UniqueFactorizationMonoid S] in
/-- Coeffs commute with subtraction (unbundled univariate form). -/
private theorem poly_coeff_sub (p q : Polynomial S) (nn : ℕ) :
    (p - q).coeff nn = p.coeff nn - q.coeff nn := by
  simp

omit [IsDomain S] [UniqueFactorizationMonoid S] in
/-- The `z`-coefficient of `triG F a` is `−a`. -/
theorem triG_coeff_one (Fc a : S) : (triG Fc a).coeff 1 = -a := by
  change (Polynomial.C Fc - Polynomial.C a * Polynomial.X).coeff 1 = -a
  rw [poly_coeff_sub, Polynomial.coeff_C_mul_X]
  simp

omit [IsDomain S] [UniqueFactorizationMonoid S] in
/-- The constant coefficient of `triG F a` is `F`. -/
theorem triG_coeff_zero (Fc a : S) : (triG Fc a).coeff 0 = Fc := by
  change (Polynomial.C Fc - Polynomial.C a * Polynomial.X).coeff 0 = Fc
  rw [poly_coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_zero]
  simp

omit [IsDomain S] [UniqueFactorizationMonoid S] in
/-- A `z`-linear form with nonzero `z`-coefficient is nonzero. -/
theorem triG_ne_zero {Fc a : S} (ha : a ≠ 0) : triG Fc a ≠ 0 := by
  intro h
  have h1 := congrArg (Polynomial.coeff · 1) h
  rw [triG_coeff_one] at h1
  simp only [Polynomial.coeff_zero, neg_eq_zero] at h1
  exact ha h1

omit [IsDomain S] [UniqueFactorizationMonoid S] in
/-- A `z`-linear form with nonzero `z`-coefficient has `z`-degree exactly `1`. -/
theorem triG_natDegree {Fc a : S} (ha : a ≠ 0) : (triG Fc a).natDegree = 1 := by
  change (Polynomial.C Fc - Polynomial.C a * Polynomial.X).natDegree = 1
  have h1 : (Polynomial.C a * Polynomial.X).natDegree = 1 := by
    have h := Polynomial.natDegree_C_mul_X_pow 1 a ha
    rwa [pow_one] at h
  have h0 : (Polynomial.C Fc).natDegree <
      (Polynomial.C a * Polynomial.X).natDegree := by
    rw [Polynomial.natDegree_C, h1]
    exact zero_lt_one
  rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt h0, h1]

omit [IsDomain S] [UniqueFactorizationMonoid S] in
/-- Every `z`-linear form has `z`-degree at most `1` (no hypothesis needed). -/
theorem triG_natDegree_le (Fc a : S) : (triG Fc a).natDegree ≤ 1 := by
  change (Polynomial.C Fc - Polynomial.C a * Polynomial.X).natDegree ≤ 1
  have hCa : (Polynomial.C a * Polynomial.X).natDegree ≤ 1 := by
    have h := Polynomial.natDegree_C_mul_X_pow_le a 1
    rwa [pow_one] at h
  calc (Polynomial.C Fc - Polynomial.C a * Polynomial.X).natDegree
      ≤ max (Polynomial.C Fc).natDegree (Polynomial.C a * Polynomial.X).natDegree :=
        Polynomial.natDegree_sub_le _ _
    _ ≤ 1 := by
        rw [Polynomial.natDegree_C]
        exact max_le (Nat.zero_le _) hCa

/-! ## (t2a) Primality when `x₀ ∤ F₀`, and regularity mod `(G₀)`. -/

omit [UniqueFactorizationMonoid S] in
/-- (t2a, core) `deg_z` irreducibility: if `a₀` is prime and `a₀ ∤ F₀`, then
`triG F₀ a₀` is irreducible. Any factorization has a constant factor (degrees
add to `1`); comparing coefficients at `1` and `0` shows the constant divides
both `a₀` and `F₀`, hence is a unit (else it is associated to `a₀`, forcing
`a₀ ∣ F₀`). -/
theorem triG_irreducible_of_not_dvd {F0 a0 : S} (hprime : Prime a0)
    (hndvd : ¬a0 ∣ F0) : Irreducible (triG F0 a0) := by
  have ha0 : a0 ≠ 0 := hprime.ne_zero
  have hne : triG F0 a0 ≠ 0 := triG_ne_zero ha0
  have hdeg : (triG F0 a0).natDegree = 1 := triG_natDegree ha0
  have hunit : ¬IsUnit (triG F0 a0) := by
    intro hu
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [hdeg] at h0
    exact one_ne_zero h0
  refine ⟨hunit, ?_⟩
  intro A B hab
  have hA : A ≠ 0 := fun h => hne (by rw [hab, h, zero_mul])
  have hB : B ≠ 0 := fun h => hne (by rw [hab, h, mul_zero])
  have hAB : (A * B).natDegree = 1 := by
    rw [← hab]
    exact hdeg
  have hmul := Polynomial.natDegree_mul hA hB
  have hdegadd : A.natDegree + B.natDegree = 1 := by omega
  have h0 : A.natDegree = 0 ∨ B.natDegree = 0 := by omega
  have key : ∀ (c : S) (V : Polynomial S),
      triG F0 a0 = Polynomial.C c * V → IsUnit (Polynomial.C c) := by
    intro c V hV
    have hc1 : c * V.coeff 1 = -a0 := by
      have h := congrArg (Polynomial.coeff · 1) hV
      rw [triG_coeff_one, Polynomial.coeff_C_mul] at h
      exact h.symm
    have hc0 : c * V.coeff 0 = F0 := by
      have h := congrArg (Polynomial.coeff · 0) hV
      rw [triG_coeff_zero, Polynomial.coeff_C_mul] at h
      exact h.symm
    have hca : c ∣ a0 := by
      have hd : c ∣ -a0 := ⟨V.coeff 1, hc1.symm⟩
      rwa [dvd_neg] at hd
    have hcF : c ∣ F0 := ⟨V.coeff 0, hc0.symm⟩
    obtain ⟨d, hd⟩ := hca
    have hor := hprime.irreducible.isUnit_or_isUnit (a := c) (b := d) hd
    rcases hor with hc | hdu
    · exact Polynomial.isUnit_C.mpr hc
    · exfalso
      have hassoc : Associated c a0 := by
        rw [hd]
        exact (associated_mul_unit_left c d hdu).symm
      exact hndvd (hassoc.dvd_iff_dvd_left.mp hcF)
  rcases h0 with hA0 | hB0
  · left
    have hAeq := Polynomial.eq_C_of_natDegree_eq_zero hA0
    rw [hAeq] at hab
    rw [hAeq]
    exact key _ _ hab
  · right
    have hBeq := Polynomial.eq_C_of_natDegree_eq_zero hB0
    rw [mul_comm A B] at hab
    rw [hBeq] at hab
    rw [hBeq]
    exact key _ _ hab

/-- (t2a) If `a₀` is prime and `a₀ ∤ F₀`, then `G₀` is prime (irreducible in a
UFD is prime). -/
theorem triG_prime_of_not_dvd {F0 a0 : S} (hprime : Prime a0)
    (hndvd : ¬a0 ∣ F0) : Prime (triG F0 a0) :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (triG_irreducible_of_not_dvd hprime hndvd)

/-- Regularity on a prime quotient: if `P` is prime and `Q ∉ (P)`, then `Q` is
regular on `R/(P)` (the quotient is a domain, so this is nonvanishing). -/
theorem isSMulRegular_quotient_mk_of_prime {R : Type*} [CommRing R] [IsDomain R]
    (P Q : R) (hP : Prime P) (hQ : Q ∉ Ideal.span {P}) :
    IsSMulRegular (R ⧸ Ideal.span {P}) (Ideal.Quotient.mk (Ideal.span {P}) Q) := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  intro m hm
  obtain ⟨H, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [smul_eq_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hm
  have hmem : P ∣ Q * H := Ideal.mem_span_singleton.mp hm
  rcases hP.dvd_or_dvd hmem with h | h
  · exact absurd (Ideal.mem_span_singleton.mpr h) hQ
  · exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h)

omit [UniqueFactorizationMonoid S] in
/-- (t2a) `G₁ ∉ (G₀)`: by degree any quotient would be constant, and comparing
`z`-coefficients would force `a₀ ∣ a₁. -/
theorem triG_not_mem_span_of_not_dvd {F0 F1 a0 a1 : S}
    (ha0 : a0 ≠ 0) (ha1 : a1 ≠ 0) (hndvd : ¬a0 ∣ a1) :
    triG F1 a1 ∉ Ideal.span {triG F0 a0} := by
  intro hmem
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨Q, hQ⟩ := hmem
  have hG0 : (triG F0 a0).natDegree = 1 := triG_natDegree ha0
  have hG1le : (triG F1 a1).natDegree ≤ 1 := triG_natDegree_le _ _
  have hG0ne : triG F0 a0 ≠ 0 := triG_ne_zero ha0
  have hG1ne : triG F1 a1 ≠ 0 := triG_ne_zero ha1
  have hQne : Q ≠ 0 := fun h => hG1ne (by rw [hQ, h, mul_zero])
  have hdeg : (triG F1 a1).natDegree = 1 + Q.natDegree := by
    rw [hQ]
    have hmul := Polynomial.natDegree_mul hG0ne hQne
    rw [hG0] at hmul
    exact hmul
  have hQdeg : Q.natDegree = 0 := by omega
  have hQeq := Polynomial.eq_C_of_natDegree_eq_zero hQdeg
  have hc : (triG F1 a1).coeff 1 = (triG F0 a0 * Q).coeff 1 := by rw [hQ]
  rw [hQeq] at hc
  rw [triG_coeff_one, Polynomial.coeff_mul_C, triG_coeff_one] at hc
  have ha1eq : a1 = a0 * Q.coeff 0 := by linear_combination -hc
  exact hndvd ⟨Q.coeff 0, ha1eq⟩

/-- (t2a, assembled) If `a₀` is prime, `a₀ ∤ F₀`, `a₁ ≠ 0` and `a₀ ∤ a₁`, then
`G₁` is regular mod `(G₀)`: `R/(G₀)` is a domain and `G₁` does not vanish on
it. -/
theorem triG_isSMulRegular_mod_of_not_dvd {F0 F1 a0 a1 : S}
    (hprime : Prime a0) (hndvd0 : ¬a0 ∣ F0)
    (ha1 : a1 ≠ 0) (hndvd1 : ¬a0 ∣ a1) :
    IsSMulRegular (Polynomial S ⧸ Ideal.span {triG F0 a0})
      (Ideal.Quotient.mk (Ideal.span {triG F0 a0}) (triG F1 a1)) := by
  have ha0 : a0 ≠ 0 := hprime.ne_zero
  exact isSMulRegular_quotient_mk_of_prime _ _
    (triG_prime_of_not_dvd hprime hndvd0)
    (triG_not_mem_span_of_not_dvd ha0 ha1 hndvd1)

/-! ## (t2b) Regularity when `x₀ ∣ F₀` and the minor is nonzero.

Write `F₀ = a₀·L₀`. Then `G₀ = −C a₀ · (X − C L₀)` lies in the monic prime
ideal `(X − C L₀)`. The image of `G₁` there is the nonzero constant
`C (F₁ − a₁·L₀) = C (M/a₀)`, so `G₁` is regular mod `(X − C L₀)`. Lifting back:
any `H` with `H·G₁ ∈ (G₀)` lies in `(X − C L₀)`; cancelling `(X − C L₀)` in the
domain leaves `C a₀ ∣ Q·G₁`; since `C a₀` is prime and `C a₀ ∤ G₁` (for distinct
variables, via `a₀ ∤ a₁`), we get `C a₀ ∣ Q`, i.e. `H ∈ (G₀)`.
-/

omit [UniqueFactorizationMonoid S] in
/-- (t2b) If `F₀ = a₀·L₀` with `a₀` prime, the minor `M = a₀·F₁ − a₁·F₀` is
nonzero, and `a₀ ∤ a₁`, then `G₁` is regular mod `(G₀)`. -/
theorem triG_isSMulRegular_mod_of_dvd {F0 F1 a0 a1 L0 : S}
    (hF0 : F0 = a0 * L0) (hM : a0 * F1 - a1 * F0 ≠ 0)
    (hprime0 : Prime a0) (hndvd : ¬a0 ∣ a1) :
    IsSMulRegular (Polynomial S ⧸ Ideal.span {triG F0 a0})
      (Ideal.Quotient.mk (Ideal.span {triG F0 a0}) (triG F1 a1)) := by
  have ha0 : a0 ≠ 0 := hprime0.ne_zero
  set P : Polynomial S := Polynomial.X - Polynomial.C L0 with hP
  have hPprime : Prime P := Polynomial.prime_X_sub_C L0
  have hP0 : P ≠ 0 := hPprime.ne_zero
  have hCprime : Prime (Polynomial.C a0) := Polynomial.prime_C_iff.mpr hprime0
  have hG0eq : triG F0 a0 = -(Polynomial.C a0) * P := by
    rw [hP, hF0]
    change Polynomial.C (a0 * L0) - Polynomial.C a0 * Polynomial.X =
      -(Polynomial.C a0) * (Polynomial.X - Polynomial.C L0)
    rw [map_mul]
    ring
  have hG0mem : triG F0 a0 ∈ Ideal.span {P} := by
    rw [Ideal.mem_span_singleton]
    exact ⟨-(Polynomial.C a0), by linear_combination hG0eq⟩
  have hcrest : F1 - a1 * L0 ≠ 0 := by
    intro h
    apply hM
    have heq : a0 * F1 - a1 * F0 = a0 * (F1 - a1 * L0) := by
      rw [hF0]
      ring
    rw [heq, h, mul_zero]
  have hPl : P.natDegree = 1 := by
    rw [hP]
    have h1 : (Polynomial.C L0).natDegree <
        (Polynomial.X : Polynomial S).natDegree := by
      rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
      exact zero_lt_one
    have hmain := Polynomial.natDegree_sub_eq_left_of_natDegree_lt h1
    rwa [Polynomial.natDegree_X] at hmain
  have hCmod : Polynomial.C (F1 - a1 * L0) ∉ Ideal.span {P} := by
    intro hmem
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨Q, hQ⟩ := hmem
    by_cases hQ0 : Q = 0
    · rw [hQ0, mul_zero] at hQ
      exact hcrest (Polynomial.C_eq_zero.mp hQ)
    · have hR := Polynomial.natDegree_mul hP0 hQ0
      have hL : (Polynomial.C (F1 - a1 * L0)).natDegree = 0 :=
        Polynomial.natDegree_C _
      rw [hQ] at hL
      rw [hPl] at hR
      omega
  have hmkP : Ideal.Quotient.mk (Ideal.span {P}) P = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr dvd_rfl)
  have hXeq : Ideal.Quotient.mk (Ideal.span {P}) Polynomial.X =
      Ideal.Quotient.mk (Ideal.span {P}) (Polynomial.C L0) := by
    have h : Ideal.Quotient.mk (Ideal.span {P})
        (Polynomial.X - Polynomial.C L0) = 0 := by
      rw [← hP]
      exact hmkP
    rw [map_sub] at h
    exact sub_eq_zero.mp h
  have hC : Polynomial.C F1 - Polynomial.C a1 * Polynomial.C L0 =
      Polynomial.C (F1 - a1 * L0) := by
    rw [map_sub, map_mul]
  have hG1eq : Ideal.Quotient.mk (Ideal.span {P}) (triG F1 a1) =
      Ideal.Quotient.mk (Ideal.span {P}) (Polynomial.C (F1 - a1 * L0)) := by
    change Ideal.Quotient.mk (Ideal.span {P})
        (Polynomial.C F1 - Polynomial.C a1 * Polynomial.X) = _
    rw [map_sub, map_mul, hXeq, ← map_mul, ← map_sub, hC]
  have hG1ne : Ideal.Quotient.mk (Ideal.span {P}) (triG F1 a1) ≠ 0 := by
    rw [hG1eq, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hCmod
  have hregP : IsSMulRegular (Polynomial S ⧸ Ideal.span {P})
      (Ideal.Quotient.mk (Ideal.span {P}) (triG F1 a1)) :=
    isSMulRegular_quotient_mk_of_prime _ _ hPprime (by
      intro hmem
      exact hG1ne (Ideal.Quotient.eq_zero_iff_mem.mpr hmem))
  have key : ∀ H : Polynomial S, H * triG F1 a1 ∈ Ideal.span {triG F0 a0} →
      H ∈ Ideal.span {triG F0 a0} := by
    intro H hH
    have hle : Ideal.span {triG F0 a0} ≤ Ideal.span {P} :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hG0mem)
    have hH0 : Ideal.Quotient.mk (Ideal.span {P}) H = 0 := by
      have h0 : Ideal.Quotient.mk (Ideal.span {P}) (H * triG F1 a1) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (hle hH)
      rw [map_mul] at h0
      have h0' : Ideal.Quotient.mk (Ideal.span {P}) (triG F1 a1) •
          Ideal.Quotient.mk (Ideal.span {P}) H = 0 := by
        rw [smul_eq_mul, mul_comm]
        exact h0
      exact hregP.right_eq_zero_of_smul h0'
    have hHP : H ∈ Ideal.span {P} := Ideal.Quotient.eq_zero_iff_mem.mp hH0
    obtain ⟨Q, hQ⟩ := Ideal.mem_span_singleton.mp hHP
    obtain ⟨W, hW⟩ := Ideal.mem_span_singleton.mp hH
    -- hQ: H = P * Q, hW: H * G₁ = G₀ * W (dvd is `∃ c, b = a * c`)
    have hcancel : Q * triG F1 a1 = (-(Polynomial.C a0)) * W := by
      rw [hQ, hG0eq] at hW
      have h2 : P * (Q * triG F1 a1) =
          P * ((-(Polynomial.C a0)) * W) := by
        linear_combination hW
      exact mul_left_cancel₀ hP0 h2
    have hdvdQ : Polynomial.C a0 ∣ Q * triG F1 a1 := by
      refine ⟨-W, ?_⟩
      linear_combination hcancel
    have hndvdG1 : ¬Polynomial.C a0 ∣ triG F1 a1 := by
      intro hd
      obtain ⟨V, hV⟩ := hd
      have hc : (triG F1 a1).coeff 1 = (Polynomial.C a0 * V).coeff 1 := by
        rw [hV]
      rw [triG_coeff_one, Polynomial.coeff_C_mul] at hc
      have ha1eq : a1 = a0 * (-(V.coeff 1)) := by linear_combination -hc
      exact hndvd ⟨-(V.coeff 1), ha1eq⟩
    have hQdiv : Polynomial.C a0 ∣ Q := by
      have h := (hCprime.dvd_mul).mp hdvdQ
      rcases h with h | h
      · exact h
      · exact absurd h hndvdG1
    obtain ⟨Q', hQ'⟩ := hQdiv
    rw [Ideal.mem_span_singleton]
    refine ⟨-(Q'), ?_⟩
    rw [hQ, hQ', hG0eq]
    ring
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  intro m hm
  obtain ⟨H, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [smul_eq_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hm
  have hHm : H * triG F1 a1 ∈ Ideal.span {triG F0 a0} := by
    rwa [mul_comm]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (key H hHm)

/-! ## (t2c) Degeneracy note: vanishing minor forces a common cofactor. -/

omit [UniqueFactorizationMonoid S] in
/-- (t2c, algebraic core) If `F₀ = a₀·L₀` and the minor
`M₀₁ = a₀·F₁ − a₁·F₀` vanishes, then `F₁ = a₁·L₀`: all forms share the
cofactor `L₀`, so all `Gⱼ` share the factor `(L₀ − z)` and the locus contains a
`ℙⁿ`-section. The locus-dimension consequence (contradiction with
`IsZeroDimensional` for `n ≥ 1`) is a follow-up through the Krull-dimension
API, not claimed here. -/
theorem triG_common_factor_of_minor_zero {F0 F1 a0 a1 L0 : S}
    (ha0 : a0 ≠ 0) (hF0 : F0 = a0 * L0) (hM : a0 * F1 - a1 * F0 = 0) :
    F1 = a1 * L0 := by
  have h : a0 * F1 = a0 * (a1 * L0) := by
    rw [hF0] at hM
    linear_combination hM
  exact mul_left_cancel₀ ha0 h

/-! ## Carry-back: the last-variable isomorphism transporting (t2b) to `MvPolynomial`.

The (t2) dichotomy is proved in the `S[Z]` model. FiberExhibit's t2b
instantiation (its bridge `isSMulRegular_of_span_ringEquiv`) needs, beyond the
bridge itself: (i) the last-variable isomorphism — a variable permutation plus
the `MvPolynomial`-to-`Polynomial` identification — and (ii) the t2b input data
(`F₀ = a₀·L₀`, nonzero minor, `Prime a₀`, `¬ a₀ ∣ a₁`) at the sheared fiber
polynomial. This section proves (i) plus the assembled transport, in the exact
shape the bridge consumes: `lastVarEquiv`/`lastVarRingEquiv` (a `renameEquiv`
sending `last ↦ none`, via `finSuccEquivLast`, composed with `optionEquivLeft`),
its values on the `mkSystem` generators (`lastVarEquiv_mkSystem`: `Gᵢ ↦ triG`),
the arbitrary-index leg (`shearLastEquiv`: permute `j ↦ last`, then identify),
and the transported (t2b) (`isSMulRegular_mvPolynomial_mod_of_dvd`, plus the
`mkSystem` corollary). Item (ii) stays with the consumer (FiberExhibit's
t2b instantiation remainder).
-/

/-- Last-variable identification `MvPolynomial (Fin (n+2)) K ≃ₐ[K]
Polynomial (MvPolynomial (Fin (n+1)) K)`: `renameEquiv` sending `last ↦ none`
(`finSuccEquivLast`) composed with `optionEquivLeft`-style unfolding. -/
noncomputable def lastVarEquiv :
    MvPolynomial (Fin (n + 2)) K ≃ₐ[K] Polynomial (MvPolynomial (Fin (n + 1)) K) :=
  (MvPolynomial.renameEquiv K (finSuccEquivLast (n := n + 1))).trans
    (MvPolynomial.optionEquivLeft K (Fin (n + 1)))

/-- Ring-equivalence form of `lastVarEquiv`, in the exact shape consumed by
FiberExhibit's bridge (`e : R ≃+* S`). -/
noncomputable def lastVarRingEquiv :
    MvPolynomial (Fin (n + 2)) K ≃+* Polynomial (MvPolynomial (Fin (n + 1)) K) :=
  (lastVarEquiv n K).toRingEquiv

/-- The ring form acts as the algebra form (definitional glue for the bridge). -/
@[simp]
theorem lastVarRingEquiv_apply (x : MvPolynomial (Fin (n + 2)) K) :
    lastVarRingEquiv n K x = lastVarEquiv n K x := rfl

/-- The iso sends `X last ↦ Polynomial.X`. -/
theorem lastVarEquiv_X_last :
    lastVarEquiv n K (MvPolynomial.X (Fin.last (n + 1))) = Polynomial.X := by
  simp only [lastVarEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X, finSuccEquivLast_last,
    MvPolynomial.optionEquivLeft_X_none]

/-- The iso sends `X (castSucc i) ↦ Polynomial.C (X i)`. -/
theorem lastVarEquiv_X_castSucc (i : Fin (n + 1)) :
    lastVarEquiv n K (MvPolynomial.X (Fin.castSucc i)) =
      Polynomial.C (MvPolynomial.X i) := by
  simp only [lastVarEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X, finSuccEquivLast_castSucc,
    MvPolynomial.optionEquivLeft_X_some]

/-- The iso sends the `z`-free lift `rename castSucc f ↦ Polynomial.C f`. -/
theorem lastVarEquiv_rename_castSucc (f : MvPolynomial (Fin (n + 1)) K) :
    lastVarEquiv n K (MvPolynomial.rename Fin.castSucc f) = Polynomial.C f := by
  have hX : ∀ k : Fin (n + 1),
      lastVarEquiv n K (MvPolynomial.rename Fin.castSucc (MvPolynomial.X k)) =
        Polynomial.C (MvPolynomial.X k) := fun k => by
    rw [MvPolynomial.rename_X]
    exact lastVarEquiv_X_castSucc n K k
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.rename_C]
    simp [lastVarEquiv]
  | add p q hp hq =>
    rw [map_add (MvPolynomial.rename Fin.castSucc), map_add (lastVarEquiv n K), hp,
      hq, map_add]
  | mul_X p k ih =>
    rw [map_mul (MvPolynomial.rename Fin.castSucc), map_mul (lastVarEquiv n K), ih,
      hX k, map_mul]

/-- The iso carries `mkSystem` generators to `triG` forms:
`Gᵢ = Fᵢ(x) − z·xᵢ ↦ C (F i) − X * C (X i) = triG (F i) (X i)`. -/
theorem lastVarEquiv_mkSystem
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (i : Fin (n + 1)) :
    lastVarEquiv n K (mkSystem n K F i) = triG (F i) (MvPolynomial.X i) := by
  have h : mkSystem n K F i = MvPolynomial.rename Fin.castSucc (F i) -
      MvPolynomial.X (Fin.last (n + 1)) * MvPolynomial.X (Fin.castSucc i) := rfl
  have ht : triG (F i) (MvPolynomial.X i) = Polynomial.C (F i) -
      Polynomial.C (MvPolynomial.X i) * Polynomial.X := rfl
  rw [h, ht, map_sub, map_mul, lastVarEquiv_rename_castSucc,
    lastVarEquiv_X_last, lastVarEquiv_X_castSucc]
  ring

/-- Variable permutation moving an arbitrary distinguished index `j` to `last`:
the first leg of the sheared-fiber carry-back (the shear fixes `Xⱼ`, so the
fiber polynomial is monic in `Xⱼ`; permuting `j ↦ last` puts the last-variable
identification to work at an arbitrary `shear_idx`). -/
noncomputable def permSwapLast (j : Fin (n + 2)) : Fin (n + 2) ≃ Fin (n + 2) :=
  Equiv.swap j (Fin.last (n + 1))

/-- The sheared-fiber iso at distinguished index `j`: permute `j ↦ last`, then
the last-variable identification. Sends `X j ↦ Polynomial.X`. -/
noncomputable def shearLastEquiv (j : Fin (n + 2)) :
    MvPolynomial (Fin (n + 2)) K ≃ₐ[K] Polynomial (MvPolynomial (Fin (n + 1)) K) :=
  (MvPolynomial.renameEquiv K (permSwapLast n j)).trans (lastVarEquiv n K)

/-- Ring-equivalence form of `shearLastEquiv`, in the exact shape consumed by
FiberExhibit's bridge (`e : R ≃+* S`) at an arbitrary `shear_idx j`. -/
noncomputable def shearLastRingEquiv (j : Fin (n + 2)) :
    MvPolynomial (Fin (n + 2)) K ≃+* Polynomial (MvPolynomial (Fin (n + 1)) K) :=
  (shearLastEquiv n K j).toRingEquiv

/-- The ring form acts as the algebra form (definitional glue for the bridge). -/
@[simp]
theorem shearLastRingEquiv_apply (j : Fin (n + 2))
    (x : MvPolynomial (Fin (n + 2)) K) :
    shearLastRingEquiv n K j x = shearLastEquiv n K j x := rfl

/-- The sheared-fiber iso sends `X j ↦ Polynomial.X`. -/
theorem shearLastEquiv_X_self (j : Fin (n + 2)) :
    shearLastEquiv n K j (MvPolynomial.X j) = Polynomial.X := by
  simp only [shearLastEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X, permSwapLast, Equiv.swap_apply_left]
  exact lastVarEquiv_X_last n K

/-- (t2b, carried back) Transport of `triG_isSMulRegular_mod_of_dvd` across any
ring equivalence: given `e G₀ = triG F₀ a₀`, `e G₁ = triG F₁ a₁` and the t2b
input data on the `S` side, `G₁` is regular mod `(G₀)` on the `MvPolynomial`
side. This is the bridge conclusion with the t2b content built in — the
consumer instantiates `e` with `lastVarRingEquiv` (or `shearLastRingEquiv j`)
and discharges `h₀`/`h₁` with the generator images above; the remaining t2b
input data is the consumer's remainder. -/
theorem isSMulRegular_mvPolynomial_mod_of_dvd
    {G0 G1 : MvPolynomial (Fin (n + 2)) K}
    {F0 F1 a0 a1 L0 : MvPolynomial (Fin (n + 1)) K}
    (e : MvPolynomial (Fin (n + 2)) K ≃+*
      Polynomial (MvPolynomial (Fin (n + 1)) K))
    (h0 : e G0 = triG F0 a0) (h1 : e G1 = triG F1 a1)
    (hF0 : F0 = a0 * L0) (hM : a0 * F1 - a1 * F0 ≠ 0)
    (hprime0 : Prime a0) (hndvd : ¬a0 ∣ a1) :
    IsSMulRegular (MvPolynomial (Fin (n + 2)) K ⧸ Ideal.span {G0})
      (Ideal.Quotient.mk (Ideal.span {G0}) G1) := by
  have hreg := triG_isSMulRegular_mod_of_dvd hF0 hM hprime0 hndvd
  rw [isSMulRegular_iff_right_eq_zero_of_smul] at hreg ⊢
  intro m hm
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [smul_eq_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hm
  obtain ⟨w, hw⟩ := hm
  have hwx : e (G1 * x) = triG F1 a1 * e x := by rw [map_mul, h1]
  have hw0 : e (G0 * w) = triG F0 a0 * e w := by rw [map_mul, h0]
  have hmemS : triG F1 a1 * e x ∈ Ideal.span {triG F0 a0} := by
    rw [Ideal.mem_span_singleton]
    refine ⟨e w, ?_⟩
    rw [← hwx, ← hw0, hw]
  have hsmul : Ideal.Quotient.mk (Ideal.span {triG F0 a0}) (triG F1 a1) •
      Ideal.Quotient.mk (Ideal.span {triG F0 a0}) (e x) = 0 := by
    rw [smul_eq_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hmemS
  have hx0 := hreg _ hsmul
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx0
  obtain ⟨v, hv⟩ := hx0
  have hcancel : e (e.symm v) = v := e.toEquiv.apply_symm_apply v
  have key : e (G0 * e.symm v) = e x := by
    rw [map_mul, h0, hcancel, hv]
  have hx : G0 * e.symm v = x := e.toEquiv.injective key
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨e.symm v, hx.symm⟩

/-- (t2b, carried back, `mkSystem` form) If `F i0 = X i0 * L0` with the minor
`X i0 * F i1 − X i1 * F i0` nonzero, `X i0` prime, and `X i0 ∤ X i1`, then
`G i1` is regular mod `(G i0)` on the `MvPolynomial` side. -/
theorem mkSystem_isSMulRegular_mod_of_dvd
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (i0 i1 : Fin (n + 1)) (L0 : MvPolynomial (Fin (n + 1)) K)
    (hF0 : F i0 = MvPolynomial.X i0 * L0)
    (hM : MvPolynomial.X i0 * F i1 - MvPolynomial.X i1 * F i0 ≠ 0)
    (hprime0 : Prime (MvPolynomial.X i0 : MvPolynomial (Fin (n + 1)) K))
    (hndvd : ¬ (MvPolynomial.X i0 : MvPolynomial (Fin (n + 1)) K) ∣
      MvPolynomial.X i1) :
    IsSMulRegular (MvPolynomial (Fin (n + 2)) K ⧸ Ideal.span {mkSystem n K F i0})
      (Ideal.Quotient.mk (Ideal.span {mkSystem n K F i0})
        (mkSystem n K F i1)) := by
  have h0 : lastVarRingEquiv n K (mkSystem n K F i0) =
      triG (F i0) (MvPolynomial.X i0) := by
    rw [lastVarRingEquiv_apply]
    exact lastVarEquiv_mkSystem n K F i0
  have h1 : lastVarRingEquiv n K (mkSystem n K F i1) =
      triG (F i1) (MvPolynomial.X i1) := by
    rw [lastVarRingEquiv_apply]
    exact lastVarEquiv_mkSystem n K F i1
  exact isSMulRegular_mvPolynomial_mod_of_dvd n K (lastVarRingEquiv n K) h0 h1 hF0
    hM hprime0 hndvd

end Triangular
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
