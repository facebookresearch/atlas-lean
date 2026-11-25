/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.RingTheory.Ideal.WeakRegularCotangent
public import MathlibExt.Algebra.Homology.KoszulComplexCoefficientSnoc
public import MathlibExt.Algebra.Homology.ZeroDifferentialHomology
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Weakly regular Koszul complexes and conormal exterior powers

A finite ordered weakly regular family resolves the quotient by its generated
ideal. Let a coefficient module have an `R`-action factoring through this
quotient. Each family member then annihilates the module, so its Koszul
tensor complex has zero differential.

Tensor cancellation and exterior base change identify its terms with
coefficient exterior powers of the conormal module `I/I²`. The generator
map is an equivalence by degree-one Koszul exactness. This gives the homology
comparison and computes the left-derived tensor functor. In the module
category at the ring's universe it also computes Mathlib's Tor.

The coefficient carrier may have an independent universe and need not be
finite or flat. The ring may be non-Noetherian, the quotient may be zero,
and the family may be empty.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace KoszulComplex

variable (R : Type u) [CommRing R] {r : ℕ} (c : Fin r → R)

local notation "V" => Fin r → R
local notation "KI" => ideal R V (familyFunctional R c)
local notation "Q" => R ⧸ KI

/-- Native finite-family exterior base change followed by the earned actual conormal generator map. -/
def weakRegularConormalExteriorBaseChangeEquiv
    (hc : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn c)) (q : ℕ) :
    Q ⊗[R] (⋀[R]^q V) ≃ₗ[Q] ⋀[Q]^q (Ideal.Cotangent KI) :=
  ((familyBaseChangeComponentEquiv R Q (I := Fin r) q).trans
    (ULift.moduleEquiv : ULift.{u, u} (⋀[Q]^q (Fin r → Q)) ≃ₗ[Q] ⋀[Q]^q (Fin r → Q))).trans
      (exteriorPower.mapEquiv Q (Fin r → Q) q
        (Ideal.weakRegularFamilyCotangentEquiv R c hc))

/-- Every original vector maps to the actual conormal class of its functional value. -/
theorem weakRegularConormalExteriorBaseChangeEquiv_ιMulti
    (hc : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn c)) (q : ℕ)
    (a : Fin q → V) :
    weakRegularConormalExteriorBaseChangeEquiv R c hc q
      ((1 : Q) ⊗ₜ[R] exteriorPower.ιMulti R q a) =
      exteriorPower.ιMulti Q q
        (fun j => Ideal.toCotangent KI (Ideal.weakRegularFamilyIdealMap R c (a j))) := by
  rw [weakRegularConormalExteriorBaseChangeEquiv, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, familyBaseChangeComponentEquiv_apply_tmul_ιMulti]
  simp only [one_smul]
  change exteriorPower.mapEquiv Q (Fin r → Q) q
    (Ideal.weakRegularFamilyCotangentEquiv R c hc)
      (exteriorPower.ιMulti Q q (fun j i => Ideal.Quotient.mk KI (a j i))) = _
  rw [exteriorPower.mapEquiv_apply_ιMulti]
  congr 1
  funext j
  exact Ideal.weakRegularFamilyCotangentMap_quotientCoordinates R c (a j)

section Coefficients

variable (M : ModuleCat.{v} R)
  [Module (R ⧸ ideal R (Fin r → R) (familyFunctional R c)) M]
  [IsScalarTower R (R ⧸ ideal R (Fin r → R) (familyFunctional R c)) M]

local instance quotientCoefficient_smulComm : SMulCommClass R Q M where
  smul_comm a b m := by
    rw [← IsScalarTower.algebraMap_smul Q a (b • m),
      ← IsScalarTower.algebraMap_smul Q a m, smul_smul, smul_smul, mul_comm]

/-- The original quotient-compatible coefficient action annihilates every actual Koszul coefficient. -/
theorem weakRegularQuotientCoefficients_annihilate :
    ∀ i : Fin r, c i ∈ Module.annihilator R M := by
  intro i
  apply Module.mem_annihilator.mpr
  intro m
  have hz : Ideal.Quotient.mk KI (c i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.weakRegularFamilyGenerator R c i).property
  rw [← IsScalarTower.algebraMap_smul Q (c i) m]
  change Ideal.Quotient.mk KI (c i) • m = 0
  rw [hz, zero_smul]

/-- Every differential of the existing original coefficient tensor complex vanishes. -/
theorem weakRegularConormalCoefficient_d_eq_zero (i j : ℕ) :
    (familyTensorCoefficientComplex R c M).d i j = 0 :=
  familyTensorCoefficient_d_eq_zero_of_coefficients_annihilate R c M
    (weakRegularQuotientCoefficients_annihilate R c M) i j

/-- The actual degree map keeps M and uses only native coefficient base-change cancellation. -/
def weakRegularConormalCoefficientDegreeEquiv
    (hc : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn c)) (q : ℕ) :
    (familyTensorCoefficientComplex R c M).X q ≃ₗ[R]
      M ⊗[Q] (⋀[Q]^q (Ideal.Cotangent KI)) :=
  (((TensorProduct.AlgebraTensorModule.cancelBaseChange R Q Q M (⋀[R]^q V)).symm).trans
    (TensorProduct.congr (LinearEquiv.refl Q M)
      (weakRegularConormalExteriorBaseChangeEquiv R c hc q))).restrictScalars R

/-- An original pure coefficient wedge retains its coefficient and its literal conormal values. -/
theorem weakRegularConormalCoefficientDegreeEquiv_ιMulti
    (hc : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn c)) (q : ℕ)
    (m : M) (a : Fin q → V) :
    weakRegularConormalCoefficientDegreeEquiv R c M hc q
      (m ⊗ₜ[R] exteriorPower.ιMulti R q a) =
      m ⊗ₜ[Q] exteriorPower.ιMulti Q q
        (fun j => Ideal.toCotangent KI (Ideal.weakRegularFamilyIdealMap R c (a j))) := by
  change m ⊗ₜ[Q] weakRegularConormalExteriorBaseChangeEquiv R c hc q
    ((1 : Q) ⊗ₜ[R] exteriorPower.ιMulti R q a) = _
  rw [weakRegularConormalExteriorBaseChangeEquiv_ιMulti]

/-- The existing native zero-differential homology coordinates followed by
the actual conormal degree map give the coefficient form comparison. -/
def weakRegularConormalTensorHomologyIso
    (hc : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn c)) (q : ℕ) :
    (familyTensorCoefficientComplex R c M).homology q ≅
      ModuleCat.of R (M ⊗[Q] (⋀[Q]^q (Ideal.Cotangent KI))) :=
  familyTensorCoefficientHomologyIsoTermOfCoefficientsAnnihilate R c M
    (weakRegularQuotientCoefficients_annihilate R c M) q ≪≫
      (weakRegularConormalCoefficientDegreeEquiv R c M hc q).toModuleIso

/-- The original zero-differential class map is sent to the actual conormal coordinate map. -/
theorem weakRegularConormalTensorHomologyIso_classMap
    (hc : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn c)) (q : ℕ) :
    HomologicalComplex.zeroDifferentialClassMap (familyTensorCoefficientComplex R c M) q
        (weakRegularConormalCoefficient_d_eq_zero R c M) ≫
      (weakRegularConormalTensorHomologyIso R c M hc q).hom =
        (weakRegularConormalCoefficientDegreeEquiv R c M hc q).toModuleIso.hom := by
  change (HomologicalComplex.zeroDifferentialClassMap (familyTensorCoefficientComplex R c M) q
      (weakRegularConormalCoefficient_d_eq_zero R c M) ≫
    (HomologicalComplex.zeroDifferentialHomologyIso (familyTensorCoefficientComplex R c M) q
      (weakRegularConormalCoefficient_d_eq_zero R c M)).hom) ≫
        (weakRegularConormalCoefficientDegreeEquiv R c M hc q).toModuleIso.hom = _
  rw [HomologicalComplex.zeroDifferentialClassMap_homologyIso, Category.id_comp]

/-- The actual native class of every original pure wedge has the displayed coefficient conormal form. -/
theorem weakRegularConormalTensorHomologyIso_class_ιMulti
    (hc : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn c)) (q : ℕ)
    (m : M) (a : Fin q → V) :
    (weakRegularConormalTensorHomologyIso R c M hc q).hom.hom
      ((HomologicalComplex.zeroDifferentialClassMap (familyTensorCoefficientComplex R c M) q
        (weakRegularConormalCoefficient_d_eq_zero R c M)).hom
          (m ⊗ₜ[R] exteriorPower.ιMulti R q a)) =
      m ⊗ₜ[Q] exteriorPower.ιMulti Q q
        (fun j => Ideal.toCotangent KI (Ideal.weakRegularFamilyIdealMap R c (a j))) := by
  let x : (familyTensorCoefficientComplex R c M).X q :=
    m ⊗ₜ[R] exteriorPower.ιMulti R q a
  have h := congrArg
    (fun f : (familyTensorCoefficientComplex R c M).X q ⟶
        ModuleCat.of R (M ⊗[Q] (⋀[Q]^q (Ideal.Cotangent KI))) => f.hom x)
    (weakRegularConormalTensorHomologyIso_classMap R c M hc q)
  exact h.trans (weakRegularConormalCoefficientDegreeEquiv_ιMulti R c M hc q m a)

/-- The actual projective resolution computes the original coefficient
left-derived tensor functor in independent coefficient and ring universes. -/
def weakRegularConormalDerivedTensorIso
    (hc : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn c)) (q : ℕ) :
    ((coefficientTensorFunctor R M).leftDerived q).obj (ModuleCat.of R Q) ≅
      ModuleCat.of R (M ⊗[Q] (⋀[Q]^q (Ideal.Cotangent KI))) :=
  (finiteFamilyProjectiveResolutionQuotient R c hc).isoLeftDerivedObj
    (coefficientTensorFunctor R M) q ≪≫ weakRegularConormalTensorHomologyIso R c M hc q

end Coefficients

section NativeTor

variable (M : ModuleCat.{u} R)
  [Module (R ⧸ ideal R (Fin r → R) (familyFunctional R c)) M]
  [IsScalarTower R (R ⧸ ideal R (Fin r → R) (familyFunctional R c)) M]

/-- In the original equal-universe module category this is Mathlib's actual
Tor of the generated-ideal quotient, computed by the same weak-regular resolution. -/
def weakRegularConormalTorIso
    (hc : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn c)) (q : ℕ) :
    (((Tor (ModuleCat.{u} R) q).obj M).obj (ModuleCat.of R Q)) ≅
      ModuleCat.of R (M ⊗[Q] (⋀[Q]^q (Ideal.Cotangent KI))) :=
  (regularFiniteFamilyTensorHomologyIsoTorQuotient R c hc M q).symm ≪≫
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) q).mapIso
      (eqToIso (familyTensorCoefficientComplex_sameUniverse R c M))).symm ≪≫
        weakRegularConormalTensorHomologyIso R c M hc q

end NativeTor

end KoszulComplex
