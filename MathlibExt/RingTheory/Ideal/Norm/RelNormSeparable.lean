/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

attribute [local instance] FractionRing.liftAlgebra

/-!
# Relative norm of a prime ideal in the separable case

For `R ⊆ S` Dedekind domains with `S` finite and torsion-free over `R`, and a
maximal ideal `P` of `S` lying over a maximal ideal `p` of `R`, this file proves
`Ideal.relNorm R P = p ^ P.inertiaDeg R` under the single assumption that the
fraction-field extension is separable.

This is Theorem 6.10 of ATLAS `NumberTheoryI` (Section 6.2), stated there in the
`AKLB` setting (`B` the integral closure of `A` in a finite separable extension).
The version proved here avoids an explicit ambient-field/integral-closure
presentation: `S` is not required to be exhibited as the integral closure of
`R` in a field. Mathlib already has the Galois version
`Ideal.relNorm_eq_pow_of_isPrime_isGalois` and, under a perfect base fraction-field
hypothesis, `Ideal.relNorm_eq_pow_of_isMaximal`. The separable version is obtained
by replaying the normal-closure argument of `Ideal.relNorm_eq_pow_of_isMaximal`
with the splitting field of a primitive element in place of the normal closure:
a primitive element exists by separability, its splitting field is Galois over
the base fraction field, and the integral closure `T` of `S` in that splitting
field has a Galois fraction field over both `FractionRing R` and
`FractionRing S`, so the Galois case applies at `T` and the result descends via
`Ideal.relNorm_relNorm` and `Ideal.inertiaDeg_tower`.
-/

@[expose] public section

namespace Ideal

set_option linter.overlappingInstances false in
set_option maxHeartbeats 400000 in
/-- Theorem 6.10 of ATLAS `NumberTheoryI`, in the separable (rather than Galois
or perfect-field) form: the relative norm of a maximal ideal lying over a maximal
ideal is the base prime raised to the inertia degree. -/
theorem relNorm_eq_pow_inertiaDeg_of_isSeparable
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [IsIntegrallyClosed R] [IsIntegrallyClosed S] [Algebra R S]
    [Module.Finite R S] [Module.IsTorsionFree R S]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    relNorm R P = p ^ P.inertiaDeg R := by
  classical
  have : P.IsPrime := inferInstance
  have : p.IsPrime := inferInstance
  by_cases hp : p = ⊥
  · subst hp
    have hP : P = ⊥ := eq_bot_of_liesOver_bot R P
    have hne : (⊥ : Ideal S).inertiaDeg R ≠ 0 := by
      rw [← hP]; exact (inertiaDeg_pos P R).ne'
    rw [hP, relNorm_bot]
    exact (bot_pow hne).symm
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element (FractionRing R) (FractionRing S)
  have hfsep : (minpoly (FractionRing R) θ).Separable :=
    Algebra.IsSeparable.isSeparable (FractionRing R) θ
  have hGal : IsGalois (FractionRing R) (minpoly (FractionRing R) θ).SplittingField :=
    IsGalois.of_separable_splitting_field hfsep
  have hInt : IsIntegral (FractionRing R) θ := Algebra.IsIntegral.isIntegral θ
  have e1 := IntermediateField.adjoinRootEquivAdjoin (FractionRing R) hInt
  have e2 := (IntermediateField.equivOfEq hθ).trans IntermediateField.topEquiv
  have e := e1.trans e2
  obtain ⟨y, hy⟩ : ∃ y : (minpoly (FractionRing R) θ).SplittingField,
      Polynomial.aeval y (minpoly (FractionRing R) θ) = 0 := by
    have hsplits : ((minpoly (FractionRing R) θ).map
        (algebraMap (FractionRing R) (minpoly (FractionRing R) θ).SplittingField)).Splits :=
      Polynomial.IsSplittingField.splits _ _
    have hne : minpoly (FractionRing R) θ ≠ 0 := minpoly.ne_zero hInt
    have hdeg : ((minpoly (FractionRing R) θ).map
        (algebraMap (FractionRing R) (minpoly (FractionRing R) θ).SplittingField)).degree ≠ 0 := by
      rw [Polynomial.degree_map_eq_of_injective
        (FaithfulSMul.algebraMap_injective _ _),
        Polynomial.degree_eq_natDegree hne]
      exact_mod_cast (minpoly.natDegree_pos hInt).ne'
    refine ⟨Polynomial.rootOfSplits hsplits hdeg, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    exact Polynomial.eval_rootOfSplits hsplits hdeg
  let lift : AdjoinRoot (minpoly (FractionRing R) θ) →ₐ[FractionRing R]
      (minpoly (FractionRing R) θ).SplittingField :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) y hy
  let φ : FractionRing S →ₐ[FractionRing R] (minpoly (FractionRing R) θ).SplittingField :=
    lift.comp e.symm.toAlgHom
  let : Algebra (FractionRing S) (minpoly (FractionRing R) θ).SplittingField := φ.toAlgebra
  have : IsScalarTower (FractionRing R) (FractionRing S)
      (minpoly (FractionRing R) θ).SplittingField :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun k => (φ.commutes k).symm)
  have : FiniteDimensional (FractionRing S) (minpoly (FractionRing R) θ).SplittingField :=
    Module.Finite.right (FractionRing R) (FractionRing S)
      (minpoly (FractionRing R) θ).SplittingField
  have : IsGalois (FractionRing S) (minpoly (FractionRing R) θ).SplittingField :=
    IsGalois.tower_top_of_isGalois (FractionRing R) (FractionRing S)
      (minpoly (FractionRing R) θ).SplittingField
  let : Algebra S (minpoly (FractionRing R) θ).SplittingField :=
    ((algebraMap (FractionRing S) (minpoly (FractionRing R) θ).SplittingField).comp
      (algebraMap S (FractionRing S))).toAlgebra
  have : IsScalarTower S (FractionRing S) (minpoly (FractionRing R) θ).SplittingField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R S (minpoly (FractionRing R) θ).SplittingField := by
    refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r => ?_)
    simp only [RingHom.comp_apply]
    show algebraMap R (minpoly (FractionRing R) θ).SplittingField r =
      algebraMap (FractionRing S) (minpoly (FractionRing R) θ).SplittingField
        (algebraMap S (FractionRing S) (algebraMap R S r))
    simp only [← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing S) r,
      ← IsScalarTower.algebraMap_apply (FractionRing R) (FractionRing S)
        (minpoly (FractionRing R) θ).SplittingField (algebraMap R (FractionRing R) r),
      ← IsScalarTower.algebraMap_apply R (FractionRing R)
        (minpoly (FractionRing R) θ).SplittingField r]
  let T := integralClosure S (minpoly (FractionRing R) θ).SplittingField
  let : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  have : FaithfulSMul S T := by
    rw [faithfulSMul_iff_algebraMap_injective]
    have hSE : Function.Injective (algebraMap S (minpoly (FractionRing R) θ).SplittingField) := by
      show Function.Injective (⇑(algebraMap (FractionRing S)
        (minpoly (FractionRing R) θ).SplittingField) ∘ ⇑(algebraMap S (FractionRing S)))
      exact (FaithfulSMul.algebraMap_injective (FractionRing S) _).comp
        (IsFractionRing.injective S (FractionRing S))
    rw [IsScalarTower.algebraMap_eq S T (minpoly (FractionRing R) θ).SplittingField] at hSE
    have hSE' : Function.Injective ((algebraMap T
        (minpoly (FractionRing R) θ).SplittingField : T →+* _) ∘
        (algebraMap S T : S →+* T)) := by
      rw [← RingHom.coe_comp]
      exact hSE
    exact Function.Injective.of_comp hSE'
  have : FaithfulSMul R T := by
    rw [faithfulSMul_iff_algebraMap_injective]
    show Function.Injective (⇑(algebraMap S T) ∘ ⇑(algebraMap R S))
    exact (FaithfulSMul.algebraMap_injective S T).comp (FaithfulSMul.algebraMap_injective R S)
  let : Algebra (FractionRing R) (FractionRing T) := FractionRing.liftAlgebra R _
  let : Algebra (FractionRing S) (FractionRing T) := FractionRing.liftAlgebra S _
  have : IsDedekindDomain T :=
    IsIntegralClosure.isDedekindDomain S (FractionRing S)
      (minpoly (FractionRing R) θ).SplittingField T
  have : Module.Finite S T :=
    IsIntegralClosure.finite S (FractionRing S)
      (minpoly (FractionRing R) θ).SplittingField T
  have : Module.Finite R T := Module.Finite.trans S T
  have : IsFractionRing T (minpoly (FractionRing R) θ).SplittingField :=
    IsIntegralClosure.isFractionRing_of_finite_extension S (FractionRing S)
      (minpoly (FractionRing R) θ).SplittingField T
  have : IsScalarTower R T (minpoly (FractionRing R) θ).SplittingField :=
    IsScalarTower.to₁₃₄ R S T (minpoly (FractionRing R) θ).SplittingField
  obtain ⟨Q, hQmax, hQP⟩ : ∃ Q : Ideal T, Q.IsMaximal ∧ Q.LiesOver P :=
    exists_maximal_ideal_liesOver_of_isIntegral P
  have : Q.IsPrime := inferInstance
  have hQp : Q.LiesOver p := LiesOver.trans Q P p
  -- Galois transports to the fraction field of `T`.
  have hGalRT : IsGalois (FractionRing R) (FractionRing T) := by
    have hrefl : (RingHomClass.toRingHom (RingEquiv.refl (FractionRing R))) =
        RingHom.id (FractionRing R) := RingHom.ext fun _ => rfl
    refine IsGalois.of_equiv_equiv (F := FractionRing R)
      (E := (minpoly (FractionRing R) θ).SplittingField)
      (M := FractionRing R) (N := FractionRing T)
      (f := RingEquiv.refl _) (g := (FractionRing.algEquiv T _).symm.toRingEquiv) ?_
    rw [hrefl, RingHom.comp_id]
    apply IsFractionRing.ringHom_ext (A := R)
    intro r
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply R (FractionRing R)
        (minpoly (FractionRing R) θ).SplittingField r,
      IsScalarTower.algebraMap_apply R T
        (minpoly (FractionRing R) θ).SplittingField r]
    conv_rhs => rw [AlgEquiv.toRingEquiv_toRingHom, ← AlgEquiv.toAlgHom_toRingHom,
      AlgHom.coe_toRingHom, AlgEquiv.toAlgHom_apply,
      (FractionRing.algEquiv T _).symm.commutes]
    have h1 : algebraMap T (FractionRing T) (algebraMap R T r) = algebraMap R (FractionRing T) r :=
      (IsScalarTower.algebraMap_apply R T (FractionRing T) r).symm
    have h2 : algebraMap (FractionRing R) (FractionRing T) (algebraMap R (FractionRing R) r) =
        algebraMap R (FractionRing T) r := by
      rw [FractionRing.algebraMap_liftAlgebra]
      exact IsFractionRing.lift_algebraMap _ r
    rw [h1, h2]
  have hGalST : IsGalois (FractionRing S) (FractionRing T) := by
    have hrefl : (RingHomClass.toRingHom (RingEquiv.refl (FractionRing S))) =
        RingHom.id (FractionRing S) := RingHom.ext fun _ => rfl
    refine IsGalois.of_equiv_equiv (F := FractionRing S)
      (E := (minpoly (FractionRing R) θ).SplittingField)
      (M := FractionRing S) (N := FractionRing T)
      (f := RingEquiv.refl _) (g := (FractionRing.algEquiv T _).symm.toRingEquiv) ?_
    rw [hrefl, RingHom.comp_id]
    apply IsFractionRing.ringHom_ext (A := S)
    intro s
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply S (FractionRing S)
        (minpoly (FractionRing R) θ).SplittingField s,
      IsScalarTower.algebraMap_apply S T
        (minpoly (FractionRing R) θ).SplittingField s]
    conv_rhs => rw [AlgEquiv.toRingEquiv_toRingHom, ← AlgEquiv.toAlgHom_toRingHom,
      AlgHom.coe_toRingHom, AlgEquiv.toAlgHom_apply,
      (FractionRing.algEquiv T _).symm.commutes]
    have h1 : algebraMap T (FractionRing T) (algebraMap S T s) = algebraMap S (FractionRing T) s :=
      (IsScalarTower.algebraMap_apply S T (FractionRing T) s).symm
    have h2 : algebraMap (FractionRing S) (FractionRing T) (algebraMap S (FractionRing S) s) =
        algebraMap S (FractionRing T) s := by
      rw [FractionRing.algebraMap_liftAlgebra]
      exact IsFractionRing.lift_algebraMap _ s
    rw [h1, h2]
  have : IsGalois (FractionRing R) (FractionRing T) := hGalRT
  have : IsGalois (FractionRing S) (FractionRing T) := hGalST
  have h := relNorm_eq_pow_of_isPrime_isGalois Q p
  rwa [← relNorm_relNorm R S, relNorm_eq_pow_of_isPrime_isGalois Q P, map_pow,
    inertiaDeg_tower (R := R) P Q, pow_mul,
    pow_left_inj (inertiaDeg_pos Q S).ne'] at h

end Ideal
