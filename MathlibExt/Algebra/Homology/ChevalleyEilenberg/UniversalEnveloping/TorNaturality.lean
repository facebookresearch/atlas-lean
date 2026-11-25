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

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.Variance
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.RightTensor
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.ScalarChange
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.Square
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
# Lie-map naturality of coefficient homology and Tor

A Lie homomorphism and a compatible semilinear map of right enveloping modules induce a
canonical Tor map from the balanced-tensor square and exact scalar restriction.

When both underlying Lie modules are free over the commutative ground ring, their coefficient
Chevalley–Eilenberg resolutions compute this map, giving naturality of the homology-to-Tor
comparison in every degree.
-/

@[expose] public section

noncomputable section

universe u v v' w z z'

open CategoryTheory CategoryTheory.Limits MulOpposite
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

attribute [local implicit_reducible] coefficientComplex HomologicalComplex.homologyFunctor
attribute [local instance] LieRing.ofAssociativeRing rightRegularLieRingModule rightRegularLieModule

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]
  {L' : Type v'} [LieRing L'] [LieAlgebra R L']
  (f : L →ₗ⁅R⁆ L')

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "U'" => UniversalEnvelopingAlgebra R L'

variable (N : ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)ᵐᵒᵖ)
  (N' : ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L')ᵐᵒᵖ)
    (g : N →ₛₗ[((UniversalEnvelopingAlgebra.map R f).toRingHom).op] N')


local instance tensorAt_additive {A : Type v} [Ring A] [Algebra R A]
    (M : ModuleCat.{z} Aᵐᵒᵖ) :
    (ModuleCat.BalancedTensor.functor.{u, v, z, z'} R A M).Additive :=
  ModuleCat.BalancedTensor.additive R A M
local instance restrictionAt_preservesHomology {A : Type v} [Ring A]
    {B : Type v'} [Ring B] (φ : A →+* B) :
    (ModuleCat.restrictScalars.{z} φ).PreservesHomology := Functor.preservesHomologyOfExact _
local instance identityAt_preservesHomology :
    (𝟭 (ModuleCat.{z} R)).PreservesHomology := Functor.preservesHomologyOfExact _

/-- Ground restriction through the scalar-linear enveloping algebra map has the target module's
ground action. -/
def restrictedEnvelopingGroundEquiv (X : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L'))) :
    (ModuleCat.restrictScalars (algebraMap R U)).obj
      ((ModuleCat.restrictScalars.{max u v v' w} ((UniversalEnvelopingAlgebra.map R f).toRingHom)).obj X) ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R U')).obj X :=
  { AddEquiv.refl _ with
    map_smul' := by
      intro r x
      change @SMul.smul U' X X.isModule.toDistribMulAction.toMulAction.toSMul
          (UniversalEnvelopingAlgebra.map R f (algebraMap R U r)) (show X from x) =
        @SMul.smul U' X X.isModule.toDistribMulAction.toMulAction.toSMul
          (algebraMap R U' r) (show X from x)
      exact congrArg (fun a : U' => @SMul.smul U' X
        X.isModule.toDistribMulAction.toMulAction.toSMul a (show X from x))
          ((UniversalEnvelopingAlgebra.map R f).commutes r) }

/-- The underived scalar-change tensor component, using the semilinear map of the balanced
quotient. -/
def rightTensorLieComponent (X : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L'))) :
  (ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
  ModuleCat.{max u v v' w} R).obj
  ((ModuleCat.restrictScalars.{max u v v' w} ((UniversalEnvelopingAlgebra.map R f).toRingHom)).obj X) ⟶
  (ModuleCat.BalancedTensor.functor R U' N' : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L')) ⥤
  ModuleCat.{max u v v' w} R).obj X := by
  letI : Module R
    ((ModuleCat.restrictScalars.{max u v v' w} ((UniversalEnvelopingAlgebra.map R f).toRingHom)).obj X) :=
    Module.compHom
    ((ModuleCat.restrictScalars.{max u v v' w} ((UniversalEnvelopingAlgebra.map R f).toRingHom)).obj X)
    (algebraMap R U)
  letI : Module R X := Module.compHom X (algebraMap R U')
  exact ModuleCat.ofHom (TensorProduct.Balanced.mapSemilinear ((UniversalEnvelopingAlgebra.map R f).toRingHom)
    (rightCoefficientGroundMap R L f g) (restrictedEnvelopingGroundEquiv R L f X).toLinearMap
    (fun u m => g.map_smulₛₗ (op u) m) (fun _ _ => rfl))

theorem rightTensorLieComponent_mk (X : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L'))) (m : N) (x : X) :
    letI : Module R
      ((ModuleCat.restrictScalars.{max u v v' w} ((UniversalEnvelopingAlgebra.map R f).toRingHom)).obj X) :=
      Module.compHom
      ((ModuleCat.restrictScalars.{max u v v' w} ((UniversalEnvelopingAlgebra.map R f).toRingHom)).obj X)
      (algebraMap R U)
    letI : Module R X := Module.compHom X (algebraMap R U')
    (rightTensorLieComponent R L f N N' g X).hom
      (TensorProduct.Balanced.mk R U N
        ((ModuleCat.restrictScalars.{max u v v' w} ((UniversalEnvelopingAlgebra.map R f).toRingHom)).obj X) m x) =
        TensorProduct.Balanced.mk R U' N' X (g m) x := by
  letI : Module R
    ((ModuleCat.restrictScalars.{max u v v' w} ((UniversalEnvelopingAlgebra.map R f).toRingHom)).obj X) :=
    Module.compHom
    ((ModuleCat.restrictScalars.{max u v v' w} ((UniversalEnvelopingAlgebra.map R f).toRingHom)).obj X)
    (algebraMap R U)
  letI : Module R X := Module.compHom X (algebraMap R U')
  exact TensorProduct.Balanced.mapSemilinear_mk ((UniversalEnvelopingAlgebra.map R f).toRingHom)
    (rightCoefficientGroundMap R L f g) (restrictedEnvelopingGroundEquiv R L f X).toLinearMap
    (fun u m => g.map_smulₛₗ (op u) m) (fun _ _ => rfl) m x

/-- The tensor square for joint Lie and right coefficient maps. -/
def rightTensorLieTransformation :
  (ModuleCat.restrictScalars.{max u v v' w} ((UniversalEnvelopingAlgebra.map R f).toRingHom)) ⋙
  (ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
  ModuleCat.{max u v v' w} R) ⟶
  (ModuleCat.BalancedTensor.functor R U' N' : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L')) ⥤
  ModuleCat.{max u v v' w} R) ⋙ 𝟭 (ModuleCat.{max u v v' w} R) where
  app := rightTensorLieComponent R L f N N' g
  naturality {X Y} h := by
    letI : Module R
      ((ModuleCat.restrictScalars.{max u v v' w} ((UniversalEnvelopingAlgebra.map R f).toRingHom)).obj X) :=
      Module.compHom
      ((ModuleCat.restrictScalars.{max u v v' w} ((UniversalEnvelopingAlgebra.map R f).toRingHom)).obj X)
      (algebraMap R U)
    letI : Module R
      ((ModuleCat.restrictScalars.{max u v v' w} ((UniversalEnvelopingAlgebra.map R f).toRingHom)).obj Y) :=
      Module.compHom
      ((ModuleCat.restrictScalars.{max u v v' w} ((UniversalEnvelopingAlgebra.map R f).toRingHom)).obj Y)
      (algebraMap R U)
    letI : Module R X := Module.compHom X (algebraMap R U')
    letI : Module R Y := Module.compHom Y (algebraMap R U')
    apply ModuleCat.hom_ext
    apply TensorProduct.Balanced.hom_ext
    intro m x
    change (rightTensorLieComponent R L f N N' g Y).hom
      ((ModuleCat.BalancedTensor.map R U N
        ((ModuleCat.restrictScalars.{max u v v' w} ((UniversalEnvelopingAlgebra.map R f).toRingHom)).map h)).hom
        (TensorProduct.Balanced.mk R U N
          ((ModuleCat.restrictScalars.{max u v v' w} ((UniversalEnvelopingAlgebra.map R f).toRingHom)).obj X) m x))
          =
      (ModuleCat.BalancedTensor.map R U' N' h).hom
        ((rightTensorLieComponent R L f N N' g X).hom
          (TensorProduct.Balanced.mk R U N
            ((ModuleCat.restrictScalars.{max u v v' w} ((UniversalEnvelopingAlgebra.map R f).toRingHom)).obj X) m
            x))
    let J := ModuleCat.restrictScalars.{max u v v' w} (UniversalEnvelopingAlgebra.map R f).toRingHom
    let x₀ : X := x
    have hSource := ModuleCat.BalancedTensor.map_mk R U N (J.map h) m x
    have hTarget := ModuleCat.BalancedTensor.map_mk R U' N' h (g m) x₀
    have hComponentY := rightTensorLieComponent_mk R L f N N' g Y m (h.hom x₀)
    have hComponentX := rightTensorLieComponent_mk R L f N N' g X m x₀
    exact ((congrArg (rightTensorLieComponent R L f N N' g Y).hom hSource).trans
      hComponentY).trans
        (((congrArg (ModuleCat.BalancedTensor.map R U' N' h).hom hComponentX).trans
          hTarget).symm)


/-- The canonical left-variable Tor map is derivation of the tensor square, independently of CE
homology. Exact restriction is sufficient. -/
def rightEnvelopingTorLieMapAt (n : ℕ) :
    ((ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
      ModuleCat.{max u v v' w} R).leftDerived n).obj (liftedEnvelopingTrivial.{u, v, max u v v' w} R L) ⟶
      ((ModuleCat.BalancedTensor.functor R U' N' : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L')) ⥤
        ModuleCat.{max u v v' w} R).leftDerived n).obj (liftedEnvelopingTrivial.{u, v', max u v v' w} R L') := by
  letI :
    (ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
    ModuleCat.{max u v v' w} R).Additive :=
    ModuleCat.BalancedTensor.additive.{u, max u v, max u v v' w, max u v v' w} R U N
  letI :
    (ModuleCat.BalancedTensor.functor R U' N' : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L')) ⥤
    ModuleCat.{max u v v' w} R).Additive :=
    ModuleCat.BalancedTensor.additive.{u, max u v', max u v v' w, max u v v' w} R U' N'
  letI : (ModuleCat.restrictScalars.{max u v v' w} (UniversalEnvelopingAlgebra.map R f).toRingHom).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  letI : (𝟭 (ModuleCat.{max u v v' w} R)).PreservesHomology := Functor.preservesHomologyOfExact _
  exact
    ((ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
      ModuleCat.{max u v v' w} R).leftDerived n).map (liftedEnvelopingTrivialLieMap.{u, v, v', w} R L f) ≫
    (Functor.leftDerivedSquareHom
      (ModuleCat.restrictScalars.{max u v v' w} ((UniversalEnvelopingAlgebra.map R f).toRingHom))
      (𝟭 (ModuleCat.{max u v v' w} R))
      (ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
      ModuleCat.{max u v v' w} R)
      (ModuleCat.BalancedTensor.functor R U' N' : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L')) ⥤
      ModuleCat.{max u v v' w} R)
      (rightTensorLieTransformation R L f N N' g) n).app
        (liftedEnvelopingTrivial.{u, v', max u v v' w} R L')

section ResolutionComputation

variable [Module.Free R L] [Module.Free R L']


/-- The exact CE resolution after common-universe lift and application of the fixed-right tensor
functor. -/
def rightTensorEnvelopingComplexAt : ChainComplex (ModuleCat.{max u v v' w} R) ℕ := by
  letI :
    (ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
    ModuleCat.{max u v v' w} R).Additive :=
    ModuleCat.BalancedTensor.additive.{u, max u v, max u v v' w, max u v v' w} R U N
  exact
    ((ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
      ModuleCat.{max u v v' w} R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).complex

/-- Up/down coordinates in the exact canonical ground scalar structure. -/
def liftedEnvelopingGroundEquiv (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap R U)).obj
      ((liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).complex.X n) ≃ₗ[R]
      envelopingGroundObject R L n := by
  letI : Module R ((envelopingComplex R L).X n) :=
    Module.compHom ((envelopingComplex R L).X n) (algebraMap R U)
  letI : IsScalarTower R U ((envelopingComplex R L).X n) :=
    IsScalarTower.of_compHom R U ((envelopingComplex R L).X n)
  exact (ULift.moduleEquiv : ULift.{max u v v' w} ((envelopingComplex R L).X n) ≃ₗ[U]
    (envelopingComplex R L).X n).restrictScalars R

/-- The tensor cancellation coordinates after lift. -/
def rightTensorCoordinatesAt (n : ℕ) :
    (rightTensorEnvelopingComplexAt.{u, v, v', w} R L N).X n ≃ₗ[R] (rightEnvelopingCoefficientComplex R L N).X n :=
  (TensorProduct.Balanced.congr (LinearEquiv.refl R N) (liftedEnvelopingGroundEquiv.{u, v, v', w} R L n)
    (fun _ _ => rfl) (fun u z =>
      (ULift.moduleEquiv : ULift.{max u v v' w} ((envelopingComplex R L).X n) ≃ₗ[U]
        (envelopingComplex R L).X n).map_smul u z)).trans (rightTensorCoordinates R L N n)

theorem rightTensorCoordinatesAt_mk_up (n : ℕ) (m : N) (z : (envelopingComplex R L).X n) :
    rightTensorCoordinatesAt.{u, v, v', w} R L N n
      (TensorProduct.Balanced.mk R U N
        ((ModuleCat.restrictScalars (algebraMap R U)).obj
          ((liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).complex.X n)) m (ULift.up z)) =
      rightTensorCoordinates R L N n
        (TensorProduct.Balanced.mk R U N (envelopingGroundObject R L n) m z) := by
  simp only [rightTensorCoordinatesAt, LinearEquiv.trans_apply, TensorProduct.Balanced.congr_mk,
    LinearEquiv.refl_apply]
  rfl

theorem rightTensorCoordinatesAt_mk_tmul (n : ℕ) (m : N) (x : ⋀[R]^n L)
    (u : regularCoefficients R L) :
    rightTensorCoordinatesAt.{u, v, v', w} R L N n
      (TensorProduct.Balanced.mk R U N
        ((ModuleCat.restrictScalars (algebraMap R U)).obj
          ((liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).complex.X n)) m
          (ULift.up (x ⊗ₜ[R] u))) = x ⊗ₜ[R] (op u • m) := by
  rw [rightTensorCoordinatesAt_mk_up, rightTensorCoordinates_mk_tmul]

theorem rightTensorCoordinatesAt_d (n : ℕ) :
    (rightTensorCoordinatesAt.{u, v, v', w} R L N n).toLinearMap.comp
      ((rightTensorEnvelopingComplexAt.{u, v, v', w} R L N).d (n + 1) n).hom =
      (coefficientDifferential R L (rightCoefficients R L N) n).comp
        (rightTensorCoordinatesAt.{u, v, v', w} R L N (n + 1)).toLinearMap := by
  apply TensorProduct.Balanced.hom_ext
  intro m z
  cases z with
  | up z =>
      change rightTensorCoordinatesAt.{u, v, v', w} R L N n
        (TensorProduct.Balanced.mk R U N
          ((ModuleCat.restrictScalars (algebraMap R U)).obj
            ((liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).complex.X n)) m
            (ULift.up (((envelopingComplex R L).d (n + 1) n).hom z))) =
        coefficientDifferential R L (rightCoefficients R L N) n
          (rightTensorCoordinatesAt.{u, v, v', w} R L N (n + 1)
            (TensorProduct.Balanced.mk R U N
              ((ModuleCat.restrictScalars (algebraMap R U)).obj
                ((liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).complex.X (n + 1))) m
                (ULift.up z)))
      let z₀ : (envelopingComplex R L).X (n + 1) := z
      have hLeft := rightTensorCoordinatesAt_mk_up.{u, v, v', w} R L N n m
        (((envelopingComplex R L).d (n + 1) n).hom z₀)
      have hRight := rightTensorCoordinatesAt_mk_up.{u, v, v', w} R L N (n + 1) m z₀
      have hCore := LinearMap.congr_fun (rightTensorCoordinates_d R L N n)
        (TensorProduct.Balanced.mk R U N (envelopingGroundObject R L (n + 1)) m z₀)
      have hD := rightTensorEnvelopingComplex_d_mk R L N n m z₀
      have hValue := (congrArg (rightTensorCoordinates R L N n) hD).symm.trans hCore
      have hGround := envelopingGroundDifferential_apply R L n z₀
      exact hLeft.trans
        (((congrArg (fun z : envelopingGroundObject R L n =>
          rightTensorCoordinates R L N n (TensorProduct.Balanced.mk R U N
            (envelopingGroundObject R L n) m z)) hGround).symm.trans hValue).trans
          (congrArg (coefficientDifferential R L (rightCoefficients R L N) n) hRight.symm))


/-- The exact CE coefficient complex is the lifted resolution tensor, through the cancellation
coordinates. -/
def rightTensorCoefficientIsoAt :
    rightTensorEnvelopingComplexAt.{u, v, v', w} R L N ≅ rightEnvelopingCoefficientComplex R L N :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (rightTensorCoordinatesAt.{u, v, v', w} R L N n).toModuleIso) (by
      intro i j hij
      change j + 1 = i at hij
      subst i
      apply ModuleCat.hom_ext
      rw [coefficientComplex_d_succ]
      exact (rightTensorCoordinatesAt_d.{u, v, v', w} R L N j).symm)

/-- The coefficient CE homology computes Tor in the common module-category universe. -/
def rightCoefficientHomologyIsoTorAt (n : ℕ) :
    (rightEnvelopingCoefficientComplex R L N).homology n ≅
      ((ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
        ModuleCat.{max u v v' w} R).leftDerived n).obj (liftedEnvelopingTrivial.{u, v, max u v v' w} R L) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v v' w} R) (ComplexShape.down ℕ) n).mapIso
    (rightTensorCoefficientIsoAt.{u, v, v', w} R L N).symm ≪≫
      ((liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).isoLeftDerivedObj
      (ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
      ModuleCat.{max u v v' w} R) n).symm

/-- The chain map inserted into the independent canonical derived square. -/
def rightTensorLieResolutionMapAt :
    rightTensorEnvelopingComplexAt.{u, v, v', w} R L N ⟶ rightTensorEnvelopingComplexAt.{u, v', v, w} R L' N' :=
  ((ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
    ModuleCat.{max u v v' w} R).mapHomologicalComplex (ComplexShape.down ℕ)).map
    (liftedEnvelopingLieComplexMap.{u, v, v', w} R L f) ≫
    (Functor.mapSquareHomologicalComplex
      (ModuleCat.restrictScalars.{max u v v' w} ((UniversalEnvelopingAlgebra.map R f).toRingHom))
      (𝟭 (ModuleCat.{max u v v' w} R))
      (ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
      ModuleCat.{max u v v' w} R)
      (ModuleCat.BalancedTensor.functor R U' N' : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L')) ⥤
      ModuleCat.{max u v v' w} R)
      (rightTensorLieTransformation R L f N N' g)).app
        (liftedEnvelopingProjectiveResolution.{u, v', max u v v' w} R L').complex

/-- Cancellation commutes with the joint CE Lie/coefficient map. The semilinear enveloping algebra
action law is used on its pure representatives. -/
theorem rightTensorCoefficientIsoAt_lie_naturality :
    rightTensorLieResolutionMapAt R L f N N' g ≫ (rightTensorCoefficientIsoAt.{u, v', v, w} R L' N').hom =
      (rightTensorCoefficientIsoAt.{u, v, v', w} R L N).hom ≫ rightEnvelopingCoefficientLieComplexMap R L f g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply TensorProduct.Balanced.hom_ext
  intro m z
  let X := (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).complex.X n
  let X' := (liftedEnvelopingProjectiveResolution.{u, v', max u v v' w} R L').complex.X n
  letI : Module R X := Module.compHom X (algebraMap R U)
  letI : Module R X' := Module.compHom X' (algebraMap R U')
  let A := ((rightTensorLieResolutionMapAt R L f N N' g ≫
    (rightTensorCoefficientIsoAt.{u, v', v, w} R L' N').hom).f n).hom.comp
      (TensorProduct.Balanced.mk R U N X m)
  let B := (((rightTensorCoefficientIsoAt.{u, v, v', w} R L N).hom ≫
    rightEnvelopingCoefficientLieComplexMap R L f g).f n).hom.comp
      (TensorProduct.Balanced.mk R U N X m)
  change A z = B z
  cases z with
  | up z =>
      induction z using TensorProduct.induction_on with
      | zero =>
          change A 0 = B 0
          exact A.map_zero.trans B.map_zero.symm
      | add z z' hz hz' =>
          change A (ULift.up z + ULift.up z') = B (ULift.up z + ULift.up z')
          exact (A.map_add _ _).trans ((congrArg₂ (fun x y => x + y) hz hz').trans
            (B.map_add _ _).symm)
      | tmul x u =>
          let y : (envelopingComplex R L').X n :=
            exteriorPower.map n f.toLinearMap x ⊗ₜ[R] UniversalEnvelopingAlgebra.map R f u
          have hWord := envelopingLieTermMap_tmul R L f n x u
          have hComponent := rightTensorLieComponent_mk R L f N N' g X' m (ULift.up y)
          have hLeft := (congrArg (rightTensorCoordinatesAt.{u, v', v, w} R L' N' n)
            hComponent).trans (rightTensorCoordinatesAt_mk_tmul.{u, v', v, w} R L' N' n
              (g m) (exteriorPower.map n f.toLinearMap x) (UniversalEnvelopingAlgebra.map R f u))
          have hRight := (congrArg ((rightEnvelopingCoefficientLieComplexMap R L f g).f n).hom
            (rightTensorCoordinatesAt_mk_tmul.{u, v, v', w} R L N n m x u)).trans
              (rightEnvelopingCoefficientLieComplexMap_f_tmul R L f g n x (op u • m))
          have hAction : op (UniversalEnvelopingAlgebra.map R f u) • g m = g (op u • m) :=
            (g.map_smulₛₗ (op u) m).symm
          change rightTensorCoordinatesAt.{u, v', v, w} R L' N' n
            ((rightTensorLieComponent R L f N N' g X').hom
              (TensorProduct.Balanced.mk R U N
                ((ModuleCat.restrictScalars (UniversalEnvelopingAlgebra.map R f).toRingHom).obj X') m
                  (ULift.up (envelopingLieTermMap R L f n (x ⊗ₜ[R] u))))) = _
          exact (congrArg (fun t : (envelopingComplex R L').X n =>
            rightTensorCoordinatesAt.{u, v', v, w} R L' N' n
              ((rightTensorLieComponent R L f N N' g X').hom
                (TensorProduct.Balanced.mk R U N
                  ((ModuleCat.restrictScalars (UniversalEnvelopingAlgebra.map R f).toRingHom).obj X') m
                    (ULift.up t)))) hWord).trans
                      (hLeft.trans ((congrArg (fun t : rightCoefficients R L' N' =>
                        exteriorPower.map n f.toLinearMap x ⊗ₜ[R] t) hAction).trans hRight.symm))

/-- Full Lie/coefficient naturality of the CE/Tor computation. The Tor map is the independently
defined scalar-change derived square. -/
theorem rightCoefficientHomologyIsoTorAt_lie_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (rightEnvelopingCoefficientLieComplexMap R L f g) n ≫
      (rightCoefficientHomologyIsoTorAt.{u, v', v, w} R L' N' n).hom =
        (rightCoefficientHomologyIsoTorAt.{u, v, v', w} R L N n).hom ≫ rightEnvelopingTorLieMapAt R L f N N' g n := by
  let e := rightTensorCoefficientIsoAt.{u, v, v', w} R L N
  let e' := rightTensorCoefficientIsoAt.{u, v', v, w} R L' N'
  let a := rightTensorLieResolutionMapAt R L f N N' g
  let b := rightEnvelopingCoefficientLieComplexMap R L f g
  have h : b ≫ e'.inv = e.inv ≫ a := by
    apply (cancel_epi e.hom).1
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← rightTensorCoefficientIsoAt_lie_naturality,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hH : HomologicalComplex.homologyMap b n ≫ HomologicalComplex.homologyMap e'.inv n =
      HomologicalComplex.homologyMap e.inv n ≫ HomologicalComplex.homologyMap a n := by
    simpa only [HomologicalComplex.homologyMap_comp] using
      congrArg (fun f => HomologicalComplex.homologyMap f n) h
  rw [rightEnvelopingTorLieMapAt, Functor.leftDerivedSquareHom_eq_with_source_lift
    (ModuleCat.restrictScalars.{max u v v' w} ((UniversalEnvelopingAlgebra.map R f).toRingHom))
      (𝟭 (ModuleCat.{max u v v' w} R))
      (ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
      ModuleCat.{max u v v' w} R)
      (ModuleCat.BalancedTensor.functor R U' N' : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L')) ⥤
      ModuleCat.{max u v v' w} R) (rightTensorLieTransformation R L f N N' g) n
      (liftedEnvelopingTrivialLieMap.{u, v, v', w} R L f)
        (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L)
        (liftedEnvelopingProjectiveResolution.{u, v', max u v v' w} R L')
        (liftedEnvelopingLieComplexMap.{u, v, v', w} R L f)
      (liftedEnvelopingLieComplexMap_augmentation.{u, v, v', w} R L f),
    HomologicalComplex.mapHomologyFunctorIso_id_hom]
  change HomologicalComplex.homologyMap b n ≫
      (HomologicalComplex.homologyMap e'.inv n ≫
        ((liftedEnvelopingProjectiveResolution.{u, v', max u v v' w} R L').isoLeftDerivedObj
        (ModuleCat.BalancedTensor.functor R U' N' : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L')) ⥤
        ModuleCat.{max u v v' w} R) n).inv) =
    (HomologicalComplex.homologyMap e.inv n ≫
      ((liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).isoLeftDerivedObj
      (ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
      ModuleCat.{max u v v' w} R) n).inv) ≫
      (((liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).isoLeftDerivedObj
        (ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
        ModuleCat.{max u v v' w} R) n).hom ≫ HomologicalComplex.homologyMap a n ≫
        ((liftedEnvelopingProjectiveResolution.{u, v', max u v v' w} R L').isoLeftDerivedObj
          (ModuleCat.BalancedTensor.functor R U' N' : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L')) ⥤
          ModuleCat.{max u v v' w} R) n).inv)
  let eP := (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).isoLeftDerivedObj
    (ModuleCat.BalancedTensor.functor R U N) n
  let eQ := (liftedEnvelopingProjectiveResolution.{u, v', max u v v' w} R L').isoLeftDerivedObj
    (ModuleCat.BalancedTensor.functor R U' N') n
  have cancel {W X Y Z V : ModuleCat.{max u v v' w} R}
      (a : W ⟶ X) (e : Y ≅ X) (b : X ⟶ Z) (c : Z ⟶ V) :
      (a ≫ e.inv) ≫ (e.hom ≫ b ≫ c) = a ≫ b ≫ c := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ eQ.inv) hH).trans
      (((Category.assoc _ _ _).trans
        (cancel (HomologicalComplex.homologyMap e.inv n) eP
          (HomologicalComplex.homologyMap a n) eQ.inv)).symm))

end ResolutionComputation

end ChevalleyEilenberg
