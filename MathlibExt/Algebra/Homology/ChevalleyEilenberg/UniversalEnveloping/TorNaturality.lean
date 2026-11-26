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
# Naturality of coefficient homology and enveloping Tor

Let R be a commutative ring, f : L →ₗ⁅R⁆ L′ a Lie map, U = U_R(L), U′ = U_R(L′), and σ =
U_R(f). For right modules N over U and N′ over U′, a σ-semilinear map g satisfies g(m·u) =
g(m)·σ(u). It induces N ⊗_U σ*X → N′ ⊗_{U′} X by [m,x] ↦ [g(m),x]. Deriving this natural
transformation and using the augmentation-module map defines the Tor map in every degree.

The Lie carriers may have universes v and v′; both coefficient modules and the tensor
categories use H = max(u,v,v′,w). If both L and L′ are free over R, tensor cancellation
identifies the lifted enveloping resolution complexes with the coefficient Chevalley–Eilenberg
complexes, and the homology-to-Tor comparison is natural for f and g.
-/

@[expose] public section

noncomputable section

universe u v v' w z z'

open CategoryTheory CategoryTheory.Limits MulOpposite
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

attribute [local implicit_reducible] coefficientComplex
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

/-- Let R be a commutative ring, f : L →ₗ⁅R⁆ L′ a Lie map, U = U_R(L), U′ = U_R(L′), and σ =
U_R(f). For X ∈ ModuleCat_H(U′), H = max(u,v,v′,w), restricting X first along σ and then along
R → U gives an R-module R-linearly equivalent to the restriction along R → U′. This
equivalence is the identity on the additive carrier. Its scalar compatibility is
σ(algebraMap_R,U(r)) = algebraMap_R,U′(r). -/
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

/-- Let R be a commutative ring, f : L →ₗ⁅R⁆ L′ a Lie map, and σ : U_R(L) → U_R(L′) its enveloping
algebra map. Put H = max(u,v,v′,w), and let N and N′ be right enveloping modules in
ModuleCat_H. A σ-semilinear map g : N → N′, satisfying g(m·u) = g(m)·σ(u), gives an R-module
morphism N ⊗_{U_R(L)} σ*X → N′ ⊗_{U_R(L′)} X for each X ∈ ModuleCat_H(U_R(L′)). It sends [m,x]
to [g(m),x]; the second factor uses the identity comparison of the two ground R-actions. -/
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

/-- Let R be a commutative ring, f : L →ₗ⁅R⁆ L′ a Lie map, σ = U_R(f), and g : N → N′ a
σ-semilinear map of right enveloping modules in the common category universe H =
max(u,v,v′,w). Set F(X) = N ⊗_{U_R(L)} X and G(Y) = N′ ⊗_{U_R(L′)} Y. The maps α_X : F(σ*X) →
G(X), [m,x] ↦ [g(m),x], form a natural transformation σ* ⋙ F → G ⋙ Id. For a U_R(L′)-linear
map a : X → Y, F(σ*a) ≫ α_Y = α_X ≫ G(a). -/
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


/-- Let R be a commutative ring, f : L →ₗ⁅R⁆ L′ a Lie map, and g : N → N′ a U_R(f)-semilinear map
of right enveloping modules in universe H = max(u,v,v′,w). Write F(X) = N ⊗_{U_R(L)} X, G(Y) =
N′ ⊗_{U_R(L′)} Y, and T_H(L), T_H(L′) for the lifted augmentation modules. For n ∈ ℕ, define
(L_nF)(T_H(L)) → (L_nG)(T_H(L′)) by first applying L_nF to T_H(L) → U_R(f)*T_H(L′), then
applying the derived natural transformation of [m,x] ↦ [g(m),x]. Scalar restriction is exact;
no freeness of either Lie algebra is required to define this map. -/
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


/-- Let R be a commutative ring, L a free R-Lie module, U = U_R(L), and N a right U-module in
universe H = max(u,v,v′,w). If Q_H is the lifted enveloping projective resolution of the
augmentation module, define the chain complex F(Q_H) in ModuleCat_H(R), where F(X) = N ⊗_U X.
In degree n its term is N ⊗_U Q_H,n and its differential is F applied to the resolution
differential. The tensor functor is additive; no exactness of this tensor complex is asserted. -/
def rightTensorEnvelopingComplexAt : ChainComplex (ModuleCat.{max u v v' w} R) ℕ := by
  letI :
    (ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
    ModuleCat.{max u v v' w} R).Additive :=
    ModuleCat.BalancedTensor.additive.{u, max u v, max u v v' w, max u v v' w} R U N
  exact
    ((ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
      ModuleCat.{max u v v' w} R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).complex

/-- Let R be a commutative ring, L a free R-Lie module, and U = U_R(L). Put H = max(u,v,v′,w), and
let Q_H be the lifted enveloping projective resolution. For n ∈ ℕ, restricting Q_H,n along R →
U gives an R-module R-linearly equivalent to the ground term Λⁿ_R L ⊗_R U of the enveloping
complex. The forward map removes the whole-term universe lift and the inverse adds it, with
the R-action obtained by restriction from the U-action. -/
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

/-- Let R be a commutative ring, L a free R-Lie module, U = U_R(L), and N a right U-module in
universe H = max(u,v,v′,w). For n ∈ ℕ, the balanced tensor of N with the lifted resolution
term Q_H,n is R-linearly equivalent to Λⁿ_R L ⊗_R N, equipped with the left Lie action [x,m] =
−m·ι(x). The coordinate map sends [m,up(a ⊗ b)] to a ⊗ (m·b). Its inverse sends a ⊗ m to
[m,up(a ⊗ 1)]. -/
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


/-- Let R be a commutative ring, L a free R-Lie module, U = U_R(L), and N a right U-module in
universe H = max(u,v,v′,w). Tensor cancellation gives a chain isomorphism N ⊗_U Q_H ≅
C_*(L;N), where Q_H is the lifted enveloping projective resolution and the exterior-first
coefficient complex uses [x,m] = −m·ι(x). Its degree-n component is [m,up(a ⊗ b)] ↦ a ⊗ (m·b),
with inverse a ⊗ m ↦ [m,up(a ⊗ 1)]. These components commute with the differentials C_{n+1} →
C_n. -/
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

/-- Let R be a commutative ring, L a free R-Lie module, U = U_R(L), and N a right U-module in
universe H = max(u,v,v′,w). For every n ∈ ℕ, H_n(C_*(L;N)) ≅ (L_nF)(T_H), where C_*(L;N) uses
the left action [x,m] = −m·ι(x), F(X) = N ⊗_U X, and T_H is the lifted augmentation module.
The forward map applies homology to the inverse tensor-cancellation chain isomorphism C_*(L;N)
≅ F(Q_H), then uses the inverse resolution-to-left-derived comparison. The right coefficient N
need not be flat. -/
def rightCoefficientHomologyIsoTorAt (n : ℕ) :
    (rightEnvelopingCoefficientComplex R L N).homology n ≅
      ((ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
        ModuleCat.{max u v v' w} R).leftDerived n).obj (liftedEnvelopingTrivial.{u, v, max u v v' w} R L) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v v' w} R) (ComplexShape.down ℕ) n).mapIso
    (rightTensorCoefficientIsoAt.{u, v, v', w} R L N).symm ≪≫
      ((liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).isoLeftDerivedObj
      (ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
      ModuleCat.{max u v v' w} R) n).symm

/-- Let R be a commutative ring, f : L →ₗ⁅R⁆ L′ a Lie map between free R-modules, and g : N → N′ a
U_R(f)-semilinear map of right enveloping modules in universe H = max(u,v,v′,w). Let Q_H and
Q′_H be their lifted enveloping resolutions and F(X) = N ⊗_{U_R(L)} X, G(Y) = N′ ⊗_{U_R(L′)}
Y. The chain map F(Q_H) → G(Q′_H) first applies F to the lifted enveloping Lie map Q_H →
U_R(f)*Q′_H, then applies the tensor transformation [m,x] ↦ [g(m),x] degreewise. -/
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

/-- Let R be a commutative ring, f : L →ₗ⁅R⁆ L′ a Lie map between free R-modules, and g : N → N′ a
U_R(f)-semilinear map of right enveloping modules in common universe H = max(u,v,v′,w). Let d
be the induced map between their tensor resolution complexes, e and e′ the tensor-cancellation
isomorphisms to their coefficient complexes, and c the coefficient chain map with components
Λⁿ(f) ⊗ g. Then d ≫ e′.hom = e.hom ≫ c. The balancing compatibility is g(m·u) =
g(m)·U_R(f)(u). -/
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

/-- Let R be a commutative ring, f : L →ₗ⁅R⁆ L′ a Lie map between free R-modules, and g : N → N′ a
U_R(f)-semilinear map of right enveloping modules in universe H = max(u,v,v′,w). Let c :
C_*(L;N) → C_*(L′;N′) have degree-n component Λⁿ(f) ⊗ g, let Φ_n and Φ′_n be the coefficient
homology-to-Tor isomorphisms, and let t_n be the Tor map defined by the derived
balanced-tensor square and augmentation-module map. For every n ∈ ℕ, H_n(c) ≫ Φ′_n.hom =
Φ_n.hom ≫ t_n. The Lie algebras may have distinct carrier universes v and v′. -/
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
