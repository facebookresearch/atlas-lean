/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.RightTensor
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.Isomorphism

/-!
# Coefficient naturality of the right-tensor CE comparison

Let N and N' be right modules over U_R(L) and g : N → N' a right-module morphism. For each
left U-module X, the balanced tensor map sends [n,x] to [g(n),x]. These maps form a natural
transformation of the fixed-right tensor functors and give a map of their tensor-applied
enveloping CE complexes.

Cancellation coordinates [n,w⊗a] ↦ w⊗(n·a) commute with g. They identify these complexes with
CE coefficients carrying the left Lie action ⁅x,n⁆ = −n·ι(x). The induced transformation on
left-derived tensor functors is the coefficient map on Tor.

When L is free over R, the CE homology/Tor isomorphisms commute with these coefficient maps in
every degree. The right modules share their given module-category universe; the Lie and scalar
carriers may lie in different universes.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory MulOpposite
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg


variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

variable {N N' : ModuleCat.{w} (UniversalEnvelopingAlgebra R L)ᵐᵒᵖ} (g : N ⟶ N')

local instance tensorN_additive :
    (ModuleCat.BalancedTensor.functor R U N :
      ModuleCat.{max u v} U ⥤ ModuleCat.{max u v w} R).Additive :=
  ModuleCat.BalancedTensor.additive R U N
local instance tensorN'_additive :
    (ModuleCat.BalancedTensor.functor R U N' :
      ModuleCat.{max u v} U ⥤ ModuleCat.{max u v w} R).Additive :=
  ModuleCat.BalancedTensor.additive R U N'

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Let N, N' :
ModuleCat.{w} Uᵐᵒᵖ be right U-modules and g : N ⟶ N' a Uᵐᵒᵖ-linear morphism. For X :
ModuleCat.{max u v} U, rightTensorCoefficientComponent gives the R-linear map B(R,U,N,X) →
B(R,U,N',X) with [n,x] ↦ [g(n),x]. The R-actions are restricted from the U and Uᵐᵒᵖ actions. -/
def rightTensorCoefficientComponent (X : ModuleCat.{max u v} U) :
    (ModuleCat.BalancedTensor.functor R U N).obj X ⟶
      (ModuleCat.BalancedTensor.functor R U N').obj X := by
  letI : Module R X := Module.compHom X (algebraMap R U)
  let f : N →ₗ[R] N' := ((ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).map g).hom
  exact ModuleCat.ofHom (TensorProduct.Balanced.map f (LinearMap.id : X →ₗ[R] X)
    (fun u m => g.hom.map_smul (op u) m) (fun _ _ => rfl))

theorem rightTensorCoefficientComponent_mk (X : ModuleCat.{max u v} U) (m : N) (x : X) :
    letI : Module R X := Module.compHom X (algebraMap R U)
    (rightTensorCoefficientComponent R L g X).hom
      (TensorProduct.Balanced.mk R U N X m x) =
        TensorProduct.Balanced.mk R U N' X (g.hom m) x := by
  letI : Module R X := Module.compHom X (algebraMap R U)
  let f : N →ₗ[R] N' := ((ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).map g).hom
  exact TensorProduct.Balanced.map_mk f (LinearMap.id : X →ₗ[R] X)
    (fun u m => g.hom.map_smul (op u) m) (fun _ _ => rfl) m x

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Let N, N' :
ModuleCat.{w} Uᵐᵒᵖ be right U-modules and g : N ⟶ N' a Uᵐᵒᵖ-linear morphism. The maps X ↦
rightTensorCoefficientComponent g X form a natural transformation
ModuleCat.BalancedTensor.functor R U N ⟶ ModuleCat.BalancedTensor.functor R U N'. Naturality
in a left U-module map acts on the X tensor factor. -/
def rightTensorCoefficientTransformation :
    ModuleCat.BalancedTensor.functor R U N ⟶ ModuleCat.BalancedTensor.functor R U N' where
  app := rightTensorCoefficientComponent R L g
  naturality {X Y} f := by
    letI : Module R X := Module.compHom X (algebraMap R U)
    letI : Module R Y := Module.compHom Y (algebraMap R U)
    apply ModuleCat.hom_ext
    apply TensorProduct.Balanced.hom_ext
    intro m x
    change (rightTensorCoefficientComponent R L g Y).hom
      ((ModuleCat.BalancedTensor.map R U N f).hom (TensorProduct.Balanced.mk R U N X m x)) =
        (ModuleCat.BalancedTensor.map R U N' f).hom
          ((rightTensorCoefficientComponent R L g X).hom (TensorProduct.Balanced.mk R U N X m x))
    rw [ModuleCat.BalancedTensor.map_mk, rightTensorCoefficientComponent_mk,
      rightTensorCoefficientComponent_mk, ModuleCat.BalancedTensor.map_mk]

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Let N, N' :
ModuleCat.{w} Uᵐᵒᵖ be right U-modules and g : N ⟶ N' a Uᵐᵒᵖ-linear morphism. Evaluating the
tensor natural transformation on envelopingComplex and mapping it over down ℕ gives
rightTensorCoefficientComplexMap : rightTensorEnvelopingComplex R L N ⟶
rightTensorEnvelopingComplex R L N'. In every degree it applies g to the balanced coefficient. -/
def rightTensorCoefficientComplexMap :
    rightTensorEnvelopingComplex R L N ⟶ rightTensorEnvelopingComplex R L N' :=
  (NatTrans.mapHomologicalComplex (rightTensorCoefficientTransformation R L g)
    (ComplexShape.down ℕ)).app (envelopingComplex R L)

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Let N, N' :
ModuleCat.{w} Uᵐᵒᵖ be right U-modules and g : N ⟶ N' a Uᵐᵒᵖ-linear morphism. Let e_N and e_N'
be the isomorphisms from the balanced tensor complexes to CE with rightCoefficients, whose Lie
action is ⁅x,n⁆ = −op(ι(x)) • n. Then rightTensorCoefficientComplexMap g ≫ e_N'.hom = e_N.hom
≫ coefficientComplexMap(rightCoefficientsMap g). The coordinate map sends [n,w⊗a] to w⊗(op a •
n). -/
theorem rightTensorCoefficientIso_naturality :
    rightTensorCoefficientComplexMap R L g ≫ (rightTensorCoefficientIso R L N').hom =
      (rightTensorCoefficientIso R L N).hom ≫
        coefficientComplexMap R L (rightCoefficients R L N) (rightCoefficientsMap R L g) := by
  apply HomologicalComplex.hom_ext
  intro n
  letI : Module R ((envelopingComplex R L).X n) :=
    Module.compHom ((envelopingComplex R L).X n) (algebraMap R U)
  apply ModuleCat.hom_ext
  apply TensorProduct.Balanced.hom_ext
  intro m z
  let A : envelopingGroundObject R L n →ₗ[R] (rightEnvelopingCoefficientComplex R L N').X n :=
    ((rightTensorCoefficientComplexMap R L g ≫ (rightTensorCoefficientIso R L N').hom).f n).hom.comp
      (TensorProduct.Balanced.mk R U N (envelopingGroundObject R L n) m)
  let B : envelopingGroundObject R L n →ₗ[R] (rightEnvelopingCoefficientComplex R L N').X n :=
    (((rightTensorCoefficientIso R L N).hom ≫
      coefficientComplexMap R L (rightCoefficients R L N) (rightCoefficientsMap R L g)).f n).hom.comp
        (TensorProduct.Balanced.mk R U N (envelopingGroundObject R L n) m)
  change A z = B z
  induction z using TensorProduct.induction_on with
  | zero => exact A.map_zero.trans B.map_zero.symm
  | add z z' hz hz' =>
      exact (A.map_add _ _).trans ((congrArg₂ (fun x y => x + y) hz hz').trans
        (B.map_add _ _).symm)
  | tmul w a =>
      let z : (envelopingComplex R L).X n := w ⊗ₜ[R] a
      have hComponent := rightTensorCoefficientComponent_mk R L g ((envelopingComplex R L).X n) m z
      have hLeft := (congrArg (rightTensorCoordinates R L N' n) hComponent).trans
        (rightTensorCoordinates_mk_tmul R L N' n (g.hom m) w a)
      have hRight := (congrArg
        (((coefficientComplexMap R L (rightCoefficients R L N) (rightCoefficientsMap R L g)).f n).hom)
          (rightTensorCoordinates_mk_tmul R L N n m w a)).trans
            (coefficientComplexMap_f_tmul R L (rightCoefficients R L N) (rightCoefficientsMap R L g) n w (op a • m))
      have hAction := g.hom.map_smul (op a) m
      exact hLeft.trans ((congrArg (fun y : rightCoefficients R L N' => w ⊗ₜ[R] y)
        hAction.symm).trans hRight.symm)

/-- Let R be commutative, L an R-Lie algebra and U its enveloping algebra. Let N, N' :
ModuleCat.{w} Uᵐᵒᵖ and g : N ⟶ N' be a right-module morphism. Let T₀ = envelopingTrivialObject
R L be the lifted scalar module with U-action through augmentation. For n : ℕ,
rightEnvelopingTorCoefficientMap is the component at T₀ of NatTrans.leftDerived
(rightTensorCoefficientTransformation g) n. It maps Tor_n^U(N,T₀) to Tor_n^U(N',T₀), with Tor
defined by the fixed-right balanced tensor left-derived functor. -/
def rightEnvelopingTorCoefficientMap (n : ℕ) :
    rightEnvelopingTor R L N n ⟶ rightEnvelopingTor R L N' n :=
  (NatTrans.leftDerived (rightTensorCoefficientTransformation R L g) n).app
    (envelopingTrivialObject R L)

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Let N, N' :
ModuleCat.{w} Uᵐᵒᵖ be right U-modules and g : N ⟶ N' a Uᵐᵒᵖ-linear morphism. Assume
Module.Free R L. For n : ℕ, the CE coefficient homology map H_n(g) followed by the comparison
e_N' to Tor equals e_N followed by rightEnvelopingTorCoefficientMap g n. The right Lie
coefficients use ⁅x,n⁆ = −op(ι(x)) • n, and the Tor map is derived from the balanced tensor
transformation. -/
theorem rightCoefficientHomologyIsoTor_naturality [Module.Free R L] (n : ℕ) :
    HomologicalComplex.homologyMap
      (coefficientComplexMap R L (rightCoefficients R L N) (rightCoefficientsMap R L g)) n ≫
        (rightCoefficientHomologyIsoTor R L N' n).hom =
      (rightCoefficientHomologyIsoTor R L N n).hom ≫ rightEnvelopingTorCoefficientMap R L g n := by
  let e := rightTensorCoefficientIso R L N
  let e' := rightTensorCoefficientIso R L N'
  let a := rightTensorCoefficientComplexMap R L g
  let b := coefficientComplexMap R L (rightCoefficients R L N) (rightCoefficientsMap R L g)
  let P := envelopingProjectiveResolution R L
  have h : b ≫ e'.inv = e.inv ≫ a := by
    apply (cancel_epi e.hom).1
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← rightTensorCoefficientIso_naturality,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hH : HomologicalComplex.homologyMap b n ≫ HomologicalComplex.homologyMap e'.inv n =
      HomologicalComplex.homologyMap e.inv n ≫ HomologicalComplex.homologyMap a n := by
    simpa only [HomologicalComplex.homologyMap_comp] using
      congrArg (fun f => HomologicalComplex.homologyMap f n) h
  rw [rightEnvelopingTorCoefficientMap, ProjectiveResolution.leftDerived_app_eq
    (rightTensorCoefficientTransformation R L g) P n]
  change HomologicalComplex.homologyMap b n ≫
      (HomologicalComplex.homologyMap e'.inv n ≫
        (P.isoLeftDerivedObj (ModuleCat.BalancedTensor.functor R U N') n).inv) =
    (HomologicalComplex.homologyMap e.inv n ≫
      (P.isoLeftDerivedObj (ModuleCat.BalancedTensor.functor R U N) n).inv) ≫
      ((P.isoLeftDerivedObj (ModuleCat.BalancedTensor.functor R U N) n).hom ≫
        HomologicalComplex.homologyMap a n ≫
          (P.isoLeftDerivedObj (ModuleCat.BalancedTensor.functor R U N') n).inv)
  have cancel {A B C D E : ModuleCat.{max u v w} R} (a : A ⟶ B)
      (e : C ≅ B) (b : B ⟶ D) (c : D ⟶ E) :
      (a ≫ e.inv) ≫ (e.hom ≫ b ≫ c) = a ≫ b ≫ c := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ (P.isoLeftDerivedObj
      (ModuleCat.BalancedTensor.functor R U N') n).inv) hH).trans
      (((Category.assoc _ _ _).trans
        (cancel (HomologicalComplex.homologyMap e.inv n)
          (P.isoLeftDerivedObj (ModuleCat.BalancedTensor.functor R U N) n)
          (HomologicalComplex.homologyMap a n)
          (P.isoLeftDerivedObj (ModuleCat.BalancedTensor.functor R U N') n).inv)).symm))

end ChevalleyEilenberg
