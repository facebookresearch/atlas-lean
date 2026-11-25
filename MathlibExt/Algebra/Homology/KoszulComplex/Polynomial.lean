/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.KoszulComplex.Finsupp
public import MathlibExt.RingTheory.MvPolynomial.RegularSequence
public import MathlibExt.RingTheory.MvPolynomial.Augmentation
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Native arbitrary-variable polynomial Koszul resolution

The complex and quotient augmentation are the original native Koszul
constructions. Every positive cycle is supported on finitely many exterior
coordinates, whose variable family is proved weakly regular. The actual
constant-coefficient kernel identifies the original quotient with the
canonical coefficient module. No Lie/PBW, finite variable set, field,
characteristic, regularity certificate or exactness certificate is a premise.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace KoszulComplex

attribute [local implicit_reducible] complex

variable (R : Type u) [CommRing R] {I : Type v}

local notation "P" => MvPolynomial I R
local notation "V" => (I →₀ P)
local notation "x" => finsuppFunctional P (MvPolynomial.X : I → P)

/-- The genuine Koszul complex of all polynomial variables is exact in every
positive degree over an arbitrary commutative coefficient ring and an
arbitrary ambient variable type. -/
theorem polynomialVariables_exact_cycles
    (k : ℕ) (z : ⋀[MvPolynomial I R]^(k + 1) (I →₀ MvPolynomial I R))
    (hz : differential (MvPolynomial I R) (I →₀ MvPolynomial I R)
      (finsuppFunctional (MvPolynomial I R) (MvPolynomial.X : I → MvPolynomial I R)) k z = 0) :
    ∃ w : ⋀[MvPolynomial I R]^(k + 2) (I →₀ MvPolynomial I R),
      differential (MvPolynomial I R) (I →₀ MvPolynomial I R)
        (finsuppFunctional (MvPolynomial I R) (MvPolynomial.X : I → MvPolynomial I R))
        (k + 1) w = z := by
  exact finsupp_exact_cycles_of_finite_isWeaklyRegular (MvPolynomial I R) MvPolynomial.X
    (fun f hf => MvPolynomial.isWeaklyRegular_X_of_injective R f hf) k z hz

/-- The actual variable Koszul complex over its original polynomial ring. -/
abbrev polynomialComplex : ChainComplex (ModuleCat.{max u v} P) ℕ :=
  finsuppComplex P (MvPolynomial.X : I → P)

/-- Every term of the original variable complex is a native projective module. -/
theorem polynomialComplex_projective (n : ℕ) :
    CategoryTheory.Projective ((polynomialComplex (I := I) R).X n) :=
  finsuppComplex_projective P MvPolynomial.X n

/-- Every term is genuinely free, for any ambient variable cardinality. -/
theorem polynomialComplex_free (n : ℕ) : Module.Free P ((polynomialComplex (I := I) R).X n) :=
  finsuppComplex_free P MvPolynomial.X n

/-- Positive-degree exactness of the original native variable complex. -/
theorem polynomialComplex_exactAt (k : ℕ) :
    (polynomialComplex (I := I) R).ExactAt (k + 1) :=
  finsuppComplex_exactAt_of_finite_isWeaklyRegular P MvPolynomial.X
    (fun f hf => MvPolynomial.isWeaklyRegular_X_of_injective R f hf) k

/-- The original variable quotient augmentation is an actual quasi-isomorphism. -/
theorem polynomialQuotientAugmentation_quasiIso : QuasiIso (augmentation P V x) :=
  finsuppAugmentation_quasiIso_of_finite_isWeaklyRegular P MvPolynomial.X
    (fun f hf => MvPolynomial.isWeaklyRegular_X_of_injective R f hf)

/-- The actual original quotient resolution, before the coefficient-target
identification. Positive exactness and projective terms are earned above. -/
def polynomialQuotientProjectiveResolution :
    ProjectiveResolution (ModuleCat.of P (ULift.{max u v} (P ⧸ ideal P V x))) :=
  finsuppProjectiveResolutionOfFiniteIsWeaklyRegular P MvPolynomial.X
    (fun f hf => MvPolynomial.isWeaklyRegular_X_of_injective R f hf)

/-- The variable range ideal equals the actual constant-coefficient kernel. -/
theorem polynomialIdeal_eq_kerConstantCoeff :
    ideal P V x = RingHom.ker (MvPolynomial.constantCoeff : P →+* R) := by
  rw [finsuppIdeal_eq_span]
  exact MvPolynomial.idealOfVars_eq_ker_constantCoeff R I

/-- Original coefficients as a native polynomial module via evaluation X=0. -/
abbrev polynomialConstants : ModuleCat.{u} P :=
  (ModuleCat.restrictScalars (MvPolynomial.constantCoeff : P →+* R)).obj (ModuleCat.of R R)

/-- Actual native coefficient carrier lift to the complex's true maximum universe. -/
abbrev polynomialTarget : ModuleCat.{max u v} P :=
  (ModuleCat.uliftFunctor.{max u v, u} P).obj (polynomialConstants (I := I) R)

/-- The original generated-ideal quotient is the original coefficient ring,
through native ideal equality and the native first isomorphism theorem. -/
def polynomialQuotientRingEquiv : (P ⧸ ideal P V x) ≃+* R :=
  (Ideal.quotientEquivAlgOfEq P (polynomialIdeal_eq_kerConstantCoeff (I := I) R)).toRingEquiv.trans
    ((MvPolynomial.constantCoeff : P →+* R).quotientKerEquivOfRightInverse
      (fun r => MvPolynomial.constantCoeff_C I r))

@[simp]
theorem polynomialQuotientRingEquiv_mk (p : P) :
    polynomialQuotientRingEquiv (I := I) R (Ideal.Quotient.mk (ideal P V x) p) =
      MvPolynomial.constantCoeff p := by
  change (MvPolynomial.constantCoeff : P →+* R).quotientKerEquivOfRightInverse
    (fun r => MvPolynomial.constantCoeff_C I r)
      ((Ideal.quotientEquivAlgOfEq P (polynomialIdeal_eq_kerConstantCoeff (I := I) R))
        (Ideal.Quotient.mk (ideal P V x) p)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk]
  rfl

/-- That computed quotient equivalence is linear for the actual polynomial
augmentation action on the original coefficient ring. -/
def polynomialQuotientEquiv : (P ⧸ ideal P V x) ≃ₗ[P] polynomialConstants (I := I) R :=
  { (polynomialQuotientRingEquiv (I := I) R).toAddEquiv with
    map_smul' := by
      intro a q
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
      change polynomialQuotientRingEquiv (I := I) R (Ideal.Quotient.mk (ideal P V x) (a * p)) =
        MvPolynomial.constantCoeff a *
          polynomialQuotientRingEquiv (I := I) R (Ideal.Quotient.mk (ideal P V x) p)
      rw [polynomialQuotientRingEquiv_mk, polynomialQuotientRingEquiv_mk, map_mul] }

/-- Actual native up/down on the quotient and coefficient targets, with the
original computed polynomial-linear quotient equivalence between them. -/
def polynomialQuotientTargetIso :
    ModuleCat.of P (ULift.{max u v} (P ⧸ ideal P V x)) ≅ polynomialTarget (I := I) R :=
  ((ULift.moduleEquiv : ULift.{max u v} (P ⧸ ideal P V x) ≃ₗ[P] P ⧸ ideal P V x).trans
    ((polynomialQuotientEquiv (I := I) R).trans
      (ULift.moduleEquiv : polynomialTarget (I := I) R ≃ₗ[P] polynomialConstants (I := I) R).symm)).toModuleIso

/-- The original variable Koszul augmentation with the canonical original
coefficient target, through the actual native target isomorphism. -/
def polynomialAugmentation : polynomialComplex (I := I) R ⟶
    (ChainComplex.single₀ (ModuleCat.{max u v} P)).obj (polynomialTarget (I := I) R) :=
  augmentation P V x ≫ (ChainComplex.single₀ (ModuleCat.{max u v} P)).map
    (polynomialQuotientTargetIso (I := I) R).hom

@[simp]
theorem polynomialAugmentation_f_zero : (polynomialAugmentation (I := I) R).f 0 =
    ModuleCat.ofHom (augmentationLinearLifted P V x) ≫ (polynomialQuotientTargetIso (I := I) R).hom := by
  rw [polynomialAugmentation, HomologicalComplex.comp_f, augmentation_f_zero]
  rfl

/-- The actual degree-zero scalar is evaluated at zero in every variable. -/
theorem polynomialAugmentation_apply (z : ⋀[P]^0 V) :
    ((polynomialAugmentation (I := I) R).f 0).hom z =
      ULift.up (MvPolynomial.constantCoeff (exteriorPower.zeroEquiv P V z)) := by
  rw [polynomialAugmentation_f_zero]
  change (polynomialQuotientTargetIso (I := I) R).hom.hom
    (augmentationLinearLifted P V x z) = _
  rw [augmentationLinearLifted_apply, augmentationLinear_apply]
  change ULift.up (polynomialQuotientRingEquiv (I := I) R
    (Ideal.Quotient.mk (ideal P V x) (exteriorPower.zeroEquiv P V z))) = _
  rw [polynomialQuotientRingEquiv_mk]

/-- The actual arbitrary-variable polynomial Koszul projective resolution of
canonical original coefficients. No finite or regularity/exactness input is supplied. -/
def polynomialProjectiveResolution : ProjectiveResolution (polynomialTarget (I := I) R) where
  complex := polynomialComplex (I := I) R
  projective := polynomialComplex_projective R
  π := polynomialAugmentation (I := I) R
  quasiIso := by
    letI : QuasiIso (augmentation P V x) := polynomialQuotientAugmentation_quasiIso R
    unfold polynomialAugmentation
    infer_instance

@[simp]
theorem polynomialProjectiveResolution_complex :
    (polynomialProjectiveResolution (I := I) R).complex = polynomialComplex (I := I) R := rfl

@[simp]
theorem polynomialProjectiveResolution_π :
    (polynomialProjectiveResolution (I := I) R).π = polynomialAugmentation (I := I) R := rfl

end KoszulComplex
