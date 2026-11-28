/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.KoszulComplex.Finsupp
public import MathlibExt.RingTheory.MvPolynomial.RegularSequence
public import MathlibExt.RingTheory.MvPolynomial.Augmentation
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# The polynomial-variable Koszul resolution over an arbitrary coefficient ring

Let R be a commutative ring, I an arbitrary variable type and
P = R[X_i | i ∈ I]. Put V = I →₀ P, with basis e_i, and let
x : V → P send e_i to X_i. The variable Koszul complex has
K_n = ⋀_P^n V and differential
∂(e_(i₀) ∧ ⋯ ∧ e_(iₙ)) =
∑_(j=0)^n (−1)^j X_(iⱼ) e_(i₀) ∧ ⋯ ∧ ê_(iⱼ) ∧ ⋯ ∧ e_(iₙ).

Every positive-degree cycle is a boundary, and every term is free and
projective as a P-module. These results hold for arbitrary I: each
exterior element involves only finitely many variables.

The variable ideal J = (X_i | i ∈ I) is the kernel of constant-coefficient
evaluation ε : P → R, so P/J ≅ R. Give R its P-module structure through
ε. The degree-zero augmentation K_0 ≅ P → R evaluates every variable
at zero; it is a quasi-isomorphism to R concentrated in degree zero.
It gives a projective resolution of the lifted coefficient module
ULift^H R in ModuleCat^H(P), where H = max(u,v) for the independent
worlds of R and I.
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

/-- For a commutative ring R and arbitrary variable type I, put
P = MvPolynomial I R and V = I →₀ P, with functional x(e_i) = X_i.
If z ∈ ⋀_P^(k+1) V satisfies ∂_k(z) = 0, then there is
w ∈ ⋀_P^(k+2) V with ∂_(k+1)(w) = z, for every k ≥ 0.
The variable family I need not be finite. -/
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

/-- For a commutative ring R and arbitrary I, the polynomial
Koszul complex over P = MvPolynomial I R has degree-n term
⋀_P^n(I →₀ P) and differential determined by x(e_i) = X_i.
It is an ℕ-indexed chain complex in ModuleCat^max(u,v)(P). -/
abbrev polynomialComplex : ChainComplex (ModuleCat.{max u v} P) ℕ :=
  finsuppComplex P (MvPolynomial.X : I → P)

/-- For a commutative ring R, arbitrary I and n ≥ 0, the
degree-n term ⋀_P^n(I →₀ P) of the variable Koszul complex is
a projective object of ModuleCat^max(u,v)(P), where
P = MvPolynomial I R. -/
theorem polynomialComplex_projective (n : ℕ) :
    CategoryTheory.Projective ((polynomialComplex (I := I) R).X n) :=
  finsuppComplex_projective P MvPolynomial.X n

/-- For a commutative ring R, arbitrary I and n ≥ 0, the
P-module in degree n of the variable Koszul complex is free,
with P = MvPolynomial I R. The exterior power of the free
variable module I →₀ P is taken in all degrees. -/
theorem polynomialComplex_free (n : ℕ) : Module.Free P ((polynomialComplex (I := I) R).X n) :=
  finsuppComplex_free P MvPolynomial.X n

/-- For a commutative ring R, arbitrary I and k ≥ 0, the
Koszul complex of the variables X_i in P = MvPolynomial I R
is exact at degree k+1. Thus its positive-degree homology vanishes. -/
theorem polynomialComplex_exactAt (k : ℕ) :
    (polynomialComplex (I := I) R).ExactAt (k + 1) :=
  finsuppComplex_exactAt_of_finite_isWeaklyRegular P MvPolynomial.X
    (fun f hf => MvPolynomial.isWeaklyRegular_X_of_injective R f hf) k

/-- For a commutative ring R and arbitrary I, let
P = MvPolynomial I R, V = I →₀ P and x(e_i) = X_i.
The Koszul augmentation to ULift^max(u,v)(P/(X_i)) concentrated
in degree zero is a quasi-isomorphism of P-module complexes. -/
theorem polynomialQuotientAugmentation_quasiIso : QuasiIso (augmentation P V x) :=
  finsuppAugmentation_quasiIso_of_finite_isWeaklyRegular P MvPolynomial.X
    (fun f hf => MvPolynomial.isWeaklyRegular_X_of_injective R f hf)

/-- For a commutative ring R and arbitrary I, the variable Koszul
complex, with its quotient augmentation, is a projective resolution
of ULift^max(u,v)(P/(X_i)) as a P-module, where
P = MvPolynomial I R. Its terms are the exterior powers of I →₀ P. -/
def polynomialQuotientProjectiveResolution :
    ProjectiveResolution (ModuleCat.of P (ULift.{max u v} (P ⧸ ideal P V x))) :=
  finsuppProjectiveResolutionOfFiniteIsWeaklyRegular P MvPolynomial.X
    (fun f hf => MvPolynomial.isWeaklyRegular_X_of_injective R f hf)

/-- For a commutative ring R and arbitrary I, the image ideal of
x : (I →₀ P) →ₗ[P] P, x(e_i) = X_i, equals ker(ε), where
P = MvPolynomial I R and ε(p) is the constant coefficient of p.
Equivalently, (X_i | i ∈ I) = ker(ε). -/
theorem polynomialIdeal_eq_kerConstantCoeff :
    ideal P V x = RingHom.ker (MvPolynomial.constantCoeff : P →+* R) := by
  rw [finsuppIdeal_eq_span]
  exact MvPolynomial.idealOfVars_eq_ker_constantCoeff R I

/-- For a commutative ring R and arbitrary I, regard R as a
module over P = MvPolynomial I R by p • r = ε(p)r, where ε is
constant-coefficient evaluation. This coefficient module has its
carrier in the world u of R. -/
abbrev polynomialConstants : ModuleCat.{u} P :=
  (ModuleCat.restrictScalars (MvPolynomial.constantCoeff : P →+* R)).obj (ModuleCat.of R R)

/-- For a commutative ring R in world u and arbitrary variable
type I in world v, the coefficient target is ULift^max(u,v) R,
with P = MvPolynomial I R acting through constant-coefficient
evaluation. It is an object of ModuleCat^max(u,v)(P). -/
abbrev polynomialTarget : ModuleCat.{max u v} P :=
  (ModuleCat.uliftFunctor.{max u v, u} P).obj (polynomialConstants (I := I) R)

/-- For a commutative ring R and arbitrary I, constant-coefficient
evaluation induces the ring equivalence P/(X_i | i ∈ I) ≃ R,
where P = MvPolynomial I R. It sends the quotient class of p to
ε(p) and has inverse r ↦ [C(r)]. -/
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

/-- For a commutative ring R and arbitrary I, the quotient
equivalence P/(X_i) ≃ R is P-linear when R is given the action
p • r = ε(p)r. The forward value is [p] ↦ ε(p), with
P = MvPolynomial I R and ε constant-coefficient evaluation. -/
def polynomialQuotientEquiv : (P ⧸ ideal P V x) ≃ₗ[P] polynomialConstants (I := I) R :=
  { (polynomialQuotientRingEquiv (I := I) R).toAddEquiv with
    map_smul' := by
      intro a q
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
      change polynomialQuotientRingEquiv (I := I) R (Ideal.Quotient.mk (ideal P V x) (a * p)) =
        MvPolynomial.constantCoeff a *
          polynomialQuotientRingEquiv (I := I) R (Ideal.Quotient.mk (ideal P V x) p)
      rw [polynomialQuotientRingEquiv_mk, polynomialQuotientRingEquiv_mk, map_mul] }

/-- For a commutative ring R in world u and arbitrary I in
world v, the polynomial-linear quotient equivalence induces
ULift^max(u,v)(P/(X_i)) ≅ ULift^max(u,v) R in ModuleCat(P).
The coefficient action on R is constant-coefficient evaluation. -/
def polynomialQuotientTargetIso :
    ModuleCat.of P (ULift.{max u v} (P ⧸ ideal P V x)) ≅ polynomialTarget (I := I) R :=
  ((ULift.moduleEquiv : ULift.{max u v} (P ⧸ ideal P V x) ≃ₗ[P] P ⧸ ideal P V x).trans
    ((polynomialQuotientEquiv (I := I) R).trans
      (ULift.moduleEquiv : polynomialTarget (I := I) R ≃ₗ[P] polynomialConstants (I := I)
        R).symm)).toModuleIso

/-- For a commutative ring R and arbitrary I, the variable
Koszul augmentation is the chain map to the complex concentrated
at degree zero in ULift^max(u,v) R, with P acting through ε.
Its degree-zero value is constant-coefficient evaluation after
the identification ⋀_P^0(I →₀ P) ≅ P. -/
def polynomialAugmentation : polynomialComplex (I := I) R ⟶
    (ChainComplex.single₀ (ModuleCat.{max u v} P)).obj (polynomialTarget (I := I) R) :=
  augmentation P V x ≫ (ChainComplex.single₀ (ModuleCat.{max u v} P)).map
    (polynomialQuotientTargetIso (I := I) R).hom

@[simp]
theorem polynomialAugmentation_f_zero : (polynomialAugmentation (I := I) R).f 0 =
    ModuleCat.ofHom (augmentationLinearLifted P V x) ≫ (polynomialQuotientTargetIso (I := I) R).hom
      := by
  rw [polynomialAugmentation, HomologicalComplex.comp_f, augmentation_f_zero]
  rfl

/-- For a commutative ring R and arbitrary I, let
P = MvPolynomial I R and V = I →₀ P. On z ∈ ⋀_P^0 V, the
variable Koszul augmentation has value up(ε(s)), where
s is the scalar corresponding to z under ⋀_P^0 V ≅ P and ε
evaluates every variable at zero. -/
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

/-- For a commutative ring R and arbitrary I, the variable
Koszul complex with its constant-coefficient augmentation is
a projective resolution of ULift^max(u,v) R as a
P = MvPolynomial I R module. Its nth term is ⋀_P^n(I →₀ P),
and the P-action on the target is through ε. -/
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
