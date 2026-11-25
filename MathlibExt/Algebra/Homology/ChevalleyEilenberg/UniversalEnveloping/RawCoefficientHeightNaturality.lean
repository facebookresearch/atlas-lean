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

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.RawCoefficientHomologyZero
public import MathlibExt.Algebra.Category.ModuleCat.UliftRestriction

/-!
# Height naturality of Lie-coefficient Tor maps

Compatible Lie and coefficient maps induce natural balanced-tensor maps and derived Tor maps
between their enveloping representations. These maps commute with the coefficient, input, and
output universe-lift comparisons.

The underlying tensor diagrams commute on pure representatives. Exact scalar restriction and
projective-preserving input lifts give the derived height identities.
-/

@[expose] public section

noncomputable section

universe u v v' w w' z t a b c d

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

attribute [local implicit_reducible] HomologicalComplex.homologyFunctor rawLieCoefficientLiftAt

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]
  {L' : Type v'} [LieRing L'] [LieAlgebra R L'] (f : L →ₗ⁅R⁆ L')
  (M : LieModuleCat.{w} R L) (M' : LieModuleCat.{w'} R L')
  (h : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f M')

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "U'" => UniversalEnvelopingAlgebra R L'

local instance rawCube_input_preservesHomology {A : Type a} [Ring A] :
    (ModuleCat.uliftFunctor.{c, b} A).PreservesHomology := Functor.preservesHomologyOfExact _
local instance rawCube_restriction_preservesHomology {A : Type a} [Ring A] {B : Type b} [Ring B]
    (φ : A →+* B) : (ModuleCat.restrictScalars.{c} φ).PreservesHomology := Functor.preservesHomologyOfExact _
local instance rawCube_identity_preservesHomology :
    (𝟭 (ModuleCat.{c} R)).PreservesHomology := Functor.preservesHomologyOfExact _
local instance rawCube_tensor_additive {A : Type a} [Ring A] [Algebra R A]
    (N : ModuleCat.{b} Aᵐᵒᵖ) : (ModuleCat.BalancedTensor.functor.{u, a, b, c} R A N).Additive :=
  ModuleCat.BalancedTensor.additive R A N

/-- The Lie/coefficient tensor square commutes with the sufficient-height maps on the balanced
quotient. -/
theorem rawTensorLieHeight_cube :
    Functor.composeLeftDerivedSquare (rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L)
      (ModuleCat.restrictScalars.{max u v v' w w' z} ((UniversalEnvelopingAlgebra.map R f).toRingHom))
      ((ModuleCat.restrictScalars.{max u v v' w w' z} ((UniversalEnvelopingAlgebra.map R f).toRingHom)) ⋙
      (rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L)) (Iso.refl _)
      (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R) (𝟭 (ModuleCat.{max u v v' w w' z} R))
      ((𝟭 (ModuleCat.{max u v v' w w' z} R)) ⋙ (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R))
      (Iso.refl _)
        (ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
        ModuleCat.{max u v v' w w' z t} R)
        (ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
        ModuleCat.{max u v v' w w' z} R)
        (ModuleCat.BalancedTensor.functor R U'
        (LieModuleCat.RightUniversalEnveloping.representObj R L'
        (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M')) : ModuleCat.{max u v v' w w' z} U' ⥤
        ModuleCat.{max u v v' w w' z} R) (rawTensorHeightNatIso.{u, v, v', w, w', z, t} R L M).hom
        (rightTensorLieTransformation.{u, v, v', max w w' z} R L f
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
        (LieModuleCat.RightUniversalEnveloping.representObj R L'
        (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M'))
        (LieModuleCat.RightUniversalEnveloping.representLieMapSemilinear.{u, v, max u v v' w w' z, v', max u v v' w
        w' z} R L f (rawLieCoefficientMapAt.{u, v, v', w, w', z} R L f M M' h))) =
    Functor.composeLeftDerivedSquare
      (ModuleCat.restrictScalars.{max u v v' w w' z t} ((UniversalEnvelopingAlgebra.map R f).toRingHom))
      (rawTensorHeightSourceLift.{u, v', v, w', w, z, t} R L')
      ((ModuleCat.restrictScalars.{max u v v' w w' z} ((UniversalEnvelopingAlgebra.map R f).toRingHom)) ⋙
      (rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L))
      (ModuleCat.uliftRestrictionIso.{t, max u v v' w w' z, max u v, max u v'}
      ((UniversalEnvelopingAlgebra.map R f).toRingHom)).symm (𝟭 (ModuleCat.{max u v v' w w' z t} R))
      (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R)
      ((𝟭 (ModuleCat.{max u v v' w w' z} R)) ⋙ (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R))
      (Functor.leftUnitor (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R) ≪≫
        (Functor.rightUnitor (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R)).symm).symm
        (ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
        ModuleCat.{max u v v' w w' z t} R)
        (ModuleCat.BalancedTensor.functor R U'
        (LieModuleCat.RightUniversalEnveloping.representObj R L'
        (rawLieCoefficientLiftAt.{u, v', v, w', w, max z t} R L' M')) : ModuleCat.{max u v v' w w' z t} U' ⥤
        ModuleCat.{max u v v' w w' z t} R)
        (ModuleCat.BalancedTensor.functor R U'
        (LieModuleCat.RightUniversalEnveloping.representObj R L'
        (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M')) : ModuleCat.{max u v v' w w' z} U' ⥤
        ModuleCat.{max u v v' w w' z} R)
        (rightTensorLieTransformation.{u, v, v', max w w' z t} R L f
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M))
        (LieModuleCat.RightUniversalEnveloping.representObj R L'
        (rawLieCoefficientLiftAt.{u, v', v, w', w, max z t} R L' M'))
        (LieModuleCat.RightUniversalEnveloping.representLieMapSemilinear.{u, v, max u v v' w w' z t, v', max u v v'
        w w' z t} R L f (rawLieCoefficientMapAt.{u, v, v', w, w', max z t} R L f M M' h)))
        (rawTensorHeightNatIso.{u, v', v, w', w, z, t} R L' M').hom := by
  apply NatTrans.ext
  funext X
  rw [Functor.composeLeftDerivedSquare_app, Functor.composeLeftDerivedSquare_app]
  simp only [Iso.refl_hom, Iso.refl_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.id_app, Functor.map_id, Category.id_comp, Category.comp_id]
  apply ModuleCat.hom_ext
  apply TensorProduct.Balanced.hom_ext
  intro m x
  cases m
  cases x
  rfl

/-- The generic canonical exact-square cube computes the left-variable Tor height square, with
arbitrary input morphism and independent raw coefficients. -/
theorem rawTensorLieHeight_derived_with_input
    {X : ModuleCat.{max u v v' w w' z} U} {Y : ModuleCat.{max u v v' w w' z} U'}
    (a : X ⟶ (ModuleCat.restrictScalars.{max u v v' w w' z} ((UniversalEnvelopingAlgebra.map R f).toRingHom)).obj Y)
      (n : ℕ) :
    ((ModuleCat.BalancedTensor.functor R U
      (LieModuleCat.RightUniversalEnveloping.representObj R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
      ModuleCat.{max u v v' w w' z t} R).leftDerived n).map
      ((rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L).map a ≫
      (ModuleCat.uliftRestrictionIso.{t, max u v v' w w' z, max u v, max u v'}
      ((UniversalEnvelopingAlgebra.map R f).toRingHom)).hom.app Y) ≫
      (Functor.leftDerivedSquareHom
        (ModuleCat.restrictScalars.{max u v v' w w' z t} ((UniversalEnvelopingAlgebra.map R f).toRingHom))
        (𝟭 (ModuleCat.{max u v v' w w' z t} R))
        (ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
        ModuleCat.{max u v v' w w' z t} R)
        (ModuleCat.BalancedTensor.functor R U'
        (LieModuleCat.RightUniversalEnveloping.representObj R L'
        (rawLieCoefficientLiftAt.{u, v', v, w', w, max z t} R L' M')) : ModuleCat.{max u v v' w w' z t} U' ⥤
        ModuleCat.{max u v v' w w' z t} R)
        (rightTensorLieTransformation.{u, v, v', max w w' z t} R L f
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M))
        (LieModuleCat.RightUniversalEnveloping.representObj R L'
        (rawLieCoefficientLiftAt.{u, v', v, w', w, max z t} R L' M'))
        (LieModuleCat.RightUniversalEnveloping.representLieMapSemilinear.{u, v, max u v v' w w' z t, v', max u v v'
        w w' z t} R L f (rawLieCoefficientMapAt.{u, v, v', w, w', max z t} R L f M M' h))) n).app
        ((rawTensorHeightSourceLift.{u, v', v, w', w, z, t} R L').obj Y) ≫
        (rawCoefficientTorHeightFunctorIso.{u, v', v, w', w, z, t} R L' M' n).inv.app Y =
    (rawCoefficientTorHeightFunctorIso.{u, v, v', w, w', z, t} R L M n).inv.app X ≫
      (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map
        (((ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
        ModuleCat.{max u v v' w w' z} R).leftDerived n).map a ≫
        (Functor.leftDerivedSquareHom
          (ModuleCat.restrictScalars.{max u v v' w w' z} ((UniversalEnvelopingAlgebra.map R f).toRingHom))
          (𝟭 (ModuleCat.{max u v v' w w' z} R))
          (ModuleCat.BalancedTensor.functor R U
          (LieModuleCat.RightUniversalEnveloping.representObj R L
          (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
          ModuleCat.{max u v v' w w' z} R)
          (ModuleCat.BalancedTensor.functor R U'
          (LieModuleCat.RightUniversalEnveloping.representObj R L'
          (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M')) : ModuleCat.{max u v v' w w' z} U' ⥤
          ModuleCat.{max u v v' w w' z} R)
          (rightTensorLieTransformation.{u, v, v', max w w' z} R L f
          (LieModuleCat.RightUniversalEnveloping.representObj R L
          (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
          (LieModuleCat.RightUniversalEnveloping.representObj R L'
          (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M'))
          (LieModuleCat.RightUniversalEnveloping.representLieMapSemilinear.{u, v, max u v v' w w' z, v', max u v v'
          w w' z} R L f (rawLieCoefficientMapAt.{u, v, v', w, w', z} R L f M M' h))) n).app Y) := by
  have hCube := Functor.leftDerivedSquareHom_cube_inverse
    (rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L) (rawTensorHeightSourceLift.{u, v', v, w', w, z, t} R L')
      (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R) (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R)
      (ModuleCat.restrictScalars.{max u v v' w w' z} ((UniversalEnvelopingAlgebra.map R f).toRingHom))
      (ModuleCat.restrictScalars.{max u v v' w w' z t} ((UniversalEnvelopingAlgebra.map R f).toRingHom))
      (𝟭 (ModuleCat.{max u v v' w w' z} R)) (𝟭 (ModuleCat.{max u v v' w w' z t} R))
      (ModuleCat.uliftRestrictionIso.{t, max u v v' w w' z, max u v, max u v'}
      ((UniversalEnvelopingAlgebra.map R f).toRingHom))
      (Functor.leftUnitor (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R) ≪≫
      (Functor.rightUnitor (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R)).symm)
      (ModuleCat.BalancedTensor.functor R U
      (LieModuleCat.RightUniversalEnveloping.representObj R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
      : ModuleCat.{max u v v' w w' z} U ⥤ ModuleCat.{max u v v' w w' z} R)
      (ModuleCat.BalancedTensor.functor R U
      (LieModuleCat.RightUniversalEnveloping.representObj R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
      ModuleCat.{max u v v' w w' z t} R)
      (ModuleCat.BalancedTensor.functor R U'
      (LieModuleCat.RightUniversalEnveloping.representObj R L'
      (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M')) : ModuleCat.{max u v v' w w' z} U' ⥤
      ModuleCat.{max u v v' w w' z} R)
      (ModuleCat.BalancedTensor.functor R U'
      (LieModuleCat.RightUniversalEnveloping.representObj R L'
      (rawLieCoefficientLiftAt.{u, v', v, w', w, max z t} R L' M')) : ModuleCat.{max u v v' w w' z t} U' ⥤
      ModuleCat.{max u v v' w w' z t} R) (rawTensorHeightNatIso.{u, v, v', w, w', z, t} R L M)
      (rawTensorHeightNatIso.{u, v', v, w', w, z, t} R L' M')
      (rightTensorLieTransformation.{u, v, v', max w w' z} R L f
      (LieModuleCat.RightUniversalEnveloping.representObj R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
      (LieModuleCat.RightUniversalEnveloping.representObj R L'
      (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M'))
      (LieModuleCat.RightUniversalEnveloping.representLieMapSemilinear.{u, v, max u v v' w w' z, v', max u v v' w w'
      z} R L f (rawLieCoefficientMapAt.{u, v, v', w, w', z} R L f M M' h)))
      (rightTensorLieTransformation.{u, v, v', max w w' z t} R L f
      (LieModuleCat.RightUniversalEnveloping.representObj R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M))
      (LieModuleCat.RightUniversalEnveloping.representObj R L'
      (rawLieCoefficientLiftAt.{u, v', v, w', w, max z t} R L' M'))
      (LieModuleCat.RightUniversalEnveloping.representLieMapSemilinear.{u, v, max u v v' w w' z t, v', max u v v' w
      w' z t} R L f (rawLieCoefficientMapAt.{u, v, v', w, w', max z t} R L f M M' h)))
    (rawTensorLieHeight_cube R L f M M' h) n Y
  rw [← rawCoefficientTorHeightFunctorIso_inv_square,
    ← rawCoefficientTorHeightFunctorIso_inv_square] at hCube
  have hId :
    (Functor.leftUnitor (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R) ≪≫
    (Functor.rightUnitor (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R)).symm).inv.app
    (((ModuleCat.BalancedTensor.functor R U'
    (LieModuleCat.RightUniversalEnveloping.representObj R L' (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M'))
    : ModuleCat.{max u v v' w w' z} U' ⥤ ModuleCat.{max u v v' w w' z} R).leftDerived n).obj Y) =
    𝟙 ((rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).obj
    (((ModuleCat.BalancedTensor.functor R U'
    (LieModuleCat.RightUniversalEnveloping.representObj R L' (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M'))
    : ModuleCat.{max u v v' w w' z} U' ⥤ ModuleCat.{max u v v' w w' z} R).leftDerived n).obj Y)) := by
    apply ModuleCat.hom_ext
    ext x
    rfl
  simp only [Functor.id_map, hId, Category.comp_id, Category.assoc] at hCube
  let F₀ : ModuleCat.{max u v v' w w' z} U ⥤ ModuleCat.{max u v v' w w' z} R :=
    ModuleCat.BalancedTensor.functor R U (LieModuleCat.RightUniversalEnveloping.representObj R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
  let F₁ : ModuleCat.{max u v v' w w' z t} U ⥤ ModuleCat.{max u v v' w w' z t} R :=
    ModuleCat.BalancedTensor.functor R U (LieModuleCat.RightUniversalEnveloping.representObj R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M))
  let I := rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L
  let K := rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R
  let eF := rawCoefficientTorHeightFunctorIso.{u, v, v', w, w', z, t} R L M n
  let eU := ModuleCat.uliftRestrictionIso.{t, max u v v' w w' z, max u v, max u v'}
    (UniversalEnvelopingAlgebra.map R f).toRingHom
  let G₀ : ModuleCat.{max u v v' w w' z} U' ⥤ ModuleCat.{max u v v' w w' z} R :=
    ModuleCat.BalancedTensor.functor R U' (LieModuleCat.RightUniversalEnveloping.representObj R L'
      (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M'))
  let G₁ : ModuleCat.{max u v v' w w' z t} U' ⥤ ModuleCat.{max u v v' w w' z t} R :=
    ModuleCat.BalancedTensor.functor R U' (LieModuleCat.RightUniversalEnveloping.representObj R L'
      (rawLieCoefficientLiftAt.{u, v', v, w', w, max z t} R L' M'))
  let A₀ := ModuleCat.restrictScalars.{max u v v' w w' z} (UniversalEnvelopingAlgebra.map R f).toRingHom
  let A₁ := ModuleCat.restrictScalars.{max u v v' w w' z t} (UniversalEnvelopingAlgebra.map R f).toRingHom
  let J := rawTensorHeightSourceLift.{u, v', v, w', w, z, t} R L'
  let eG := rawCoefficientTorHeightFunctorIso.{u, v', v, w', w, z, t} R L' M' n
  let α₀ := rightTensorLieTransformation.{u, v, v', max w w' z} R L f
    (LieModuleCat.RightUniversalEnveloping.representObj R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
    (LieModuleCat.RightUniversalEnveloping.representObj R L' (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M'))
    (LieModuleCat.RightUniversalEnveloping.representLieMapSemilinear R L f
      (rawLieCoefficientMapAt.{u, v, v', w, w', z} R L f M M' h))
  let α₁ := rightTensorLieTransformation.{u, v, v', max w w' z t} R L f
    (LieModuleCat.RightUniversalEnveloping.representObj R L (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M))
    (LieModuleCat.RightUniversalEnveloping.representObj R L'
      (rawLieCoefficientLiftAt.{u, v', v, w', w, max z t} R L' M'))
    (LieModuleCat.RightUniversalEnveloping.representLieMapSemilinear R L f
      (rawLieCoefficientMapAt.{u, v, v', w, w', max z t} R L f M M' h))
  let s₀ := (Functor.leftDerivedSquareHom A₀ (𝟭 (ModuleCat.{max u v v' w w' z} R)) F₀ G₀ α₀ n).app Y
  let s₁ := (Functor.leftDerivedSquareHom A₁ (𝟭 (ModuleCat.{max u v v' w w' z t} R)) F₁ G₁ α₁ n).app (J.obj Y)
  let tail := s₁ ≫ eG.inv.app Y
  have hNat := eF.inv.naturality a
  have hFront := (F₁.leftDerived n).map_comp (I.map a) (eU.hom.app Y)
  have h' := congrArg (fun b => (F₁.leftDerived n).map (I.map a) ≫ b) hCube
  have hStart : (F₁.leftDerived n).map (I.map a ≫ eU.hom.app Y) ≫ tail =
      (F₁.leftDerived n).map (I.map a) ≫ ((F₁.leftDerived n).map (eU.hom.app Y) ≫ tail) :=
    (congrArg (fun q => q ≫ tail) hFront).trans (Category.assoc _ _ _)
  have hEnd : (F₁.leftDerived n).map (I.map a) ≫ (eF.inv.app (A₀.obj Y) ≫ K.map s₀) =
      eF.inv.app X ≫ K.map ((F₀.leftDerived n).map a ≫ s₀) := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ K.map s₀) hNat).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun q => eF.inv.app X ≫ q) (K.map_comp ((F₀.leftDerived n).map a) s₀).symm)))
  exact hStart.trans (h'.trans hEnd)

/-- Trivial-module Lie maps commute with the input height flattening, by their unchanged scalar
representatives. -/
theorem rawEnvelopingTrivialLieMap_height :
    (rawEnvelopingTrivialHeightIso.{u, v, v', w, w', z, t} R L).inv ≫
      (rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L).map
        (liftedEnvelopingTrivialLieMap.{u, v, v', max w w' z} R L f) ≫
        (ModuleCat.uliftRestrictionIso.{t, max u v v' w w' z, max u v, max u v'}
          ((UniversalEnvelopingAlgebra.map R f).toRingHom)).hom.app
          (liftedEnvelopingTrivial.{u, v', max u v v' w w' z} R L') =
    liftedEnvelopingTrivialLieMap.{u, v, v', max w w' z t} R L f ≫
      (ModuleCat.restrictScalars.{max u v v' w w' z t} ((UniversalEnvelopingAlgebra.map R f).toRingHom)).map
        (rawEnvelopingTrivialHeightIso.{u, v', v, w', w, z, t} R L').inv := by
  apply ModuleCat.hom_ext
  ext x
  cases x
  rfl

/-- The joint Lie-and-coefficient Tor map commutes with universe-lift transport of both
coefficient modules. -/
theorem rawLieCoefficientTorMapAt_height (n : ℕ) :
    rawLieCoefficientTorMapAt.{u, v, v', w, w', max z t} R L f M M' h n ≫
      (rawLieCoefficientTorHeightIsoAt.{u, v', v, w', w, z, t} R L' M' n).inv =
    (rawLieCoefficientTorHeightIsoAt.{u, v, v', w, w', z, t} R L M n).inv ≫
      (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map
        (rawLieCoefficientTorMapAt.{u, v, v', w, w', z} R L f M M' h n) := by
  let X := liftedEnvelopingTrivial.{u, v, max u v v' w w' z} R L
  let Y := liftedEnvelopingTrivial.{u, v', max u v v' w w' z} R L'
  let eX := rawEnvelopingTrivialHeightIso.{u, v, v', w, w', z, t} R L
  let eY := rawEnvelopingTrivialHeightIso.{u, v', v, w', w, z, t} R L'
  let a₀ := liftedEnvelopingTrivialLieMap.{u, v, v', max w w' z} R L f
  let a₁ := liftedEnvelopingTrivialLieMap.{u, v, v', max w w' z t} R L f
  let S₁ := Functor.leftDerivedSquareHom
    (ModuleCat.restrictScalars.{max u v v' w w' z t} ((UniversalEnvelopingAlgebra.map R f).toRingHom))
    (𝟭 (ModuleCat.{max u v v' w w' z t} R))
    (ModuleCat.BalancedTensor.functor R U
    (LieModuleCat.RightUniversalEnveloping.representObj R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
    ModuleCat.{max u v v' w w' z t} R)
    (ModuleCat.BalancedTensor.functor R U'
    (LieModuleCat.RightUniversalEnveloping.representObj R L'
    (rawLieCoefficientLiftAt.{u, v', v, w', w, max z t} R L' M')) : ModuleCat.{max u v v' w w' z t} U' ⥤
    ModuleCat.{max u v v' w w' z t} R)
    (rightTensorLieTransformation.{u, v, v', max w w' z t} R L f
    (LieModuleCat.RightUniversalEnveloping.representObj R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M))
    (LieModuleCat.RightUniversalEnveloping.representObj R L'
    (rawLieCoefficientLiftAt.{u, v', v, w', w, max z t} R L' M'))
    (LieModuleCat.RightUniversalEnveloping.representLieMapSemilinear.{u, v, max u v v' w w' z t, v', max u v v' w w'
    z t} R L f (rawLieCoefficientMapAt.{u, v, v', w, w', max z t} R L f M M' h))) n
  have hNat : S₁.app (liftedEnvelopingTrivial.{u, v', max u v v' w w' z t} R L') ≫
      ((ModuleCat.BalancedTensor.functor R U'
        (LieModuleCat.RightUniversalEnveloping.representObj R L'
        (rawLieCoefficientLiftAt.{u, v', v, w', w, max z t} R L' M')) : ModuleCat.{max u v v' w w' z t} U' ⥤
        ModuleCat.{max u v v' w w' z t} R).leftDerived n).map eY.inv =
    ((ModuleCat.BalancedTensor.functor R U
      (LieModuleCat.RightUniversalEnveloping.representObj R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
      ModuleCat.{max u v v' w w' z t} R).leftDerived n).map
      ((ModuleCat.restrictScalars.{max u v v' w w' z t} ((UniversalEnvelopingAlgebra.map R f).toRingHom)).map
      eY.inv) ≫ S₁.app ((rawTensorHeightSourceLift.{u, v', v, w', w, z, t} R L').obj Y) :=
    (S₁.naturality eY.inv).symm
  have hInput : eX.inv ≫ (rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L).map a₀ ≫
    (ModuleCat.uliftRestrictionIso.{t, max u v v' w w' z, max u v, max u v'}
    ((UniversalEnvelopingAlgebra.map R f).toRingHom)).hom.app Y = a₁ ≫
    (ModuleCat.restrictScalars.{max u v v' w w' z t} ((UniversalEnvelopingAlgebra.map R f).toRingHom)).map eY.inv :=
    rawEnvelopingTrivialLieMap_height R L f
  have hLarge := rawTensorLieHeight_derived_with_input R L f M M' h a₀ n
  have hPrefixed := congrArg
    (fun b =>
    ((ModuleCat.BalancedTensor.functor R U
    (LieModuleCat.RightUniversalEnveloping.representObj R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
    ModuleCat.{max u v v' w w' z t} R).leftDerived n).map eX.inv ≫ b) hLarge
  rw [rawLieCoefficientTorHeightIsoAt_inv, rawLieCoefficientTorHeightIsoAt_inv]
  unfold rawLieCoefficientTorMapAt nativeLieCoefficientTorMap rightEnvelopingTorLieMapAt
  rw [← rawCoefficientTorHeightFunctorIso_inv_square, ← rawCoefficientTorHeightFunctorIso_inv_square]
  change
    ((ModuleCat.BalancedTensor.functor R U
    (LieModuleCat.RightUniversalEnveloping.representObj R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
    ModuleCat.{max u v v' w w' z t} R).leftDerived n).map a₁ ≫ S₁.app _ ≫
      ((ModuleCat.BalancedTensor.functor R U'
        (LieModuleCat.RightUniversalEnveloping.representObj R L'
        (rawLieCoefficientLiftAt.{u, v', v, w', w, max z t} R L' M')) : ModuleCat.{max u v v' w w' z t} U' ⥤
        ModuleCat.{max u v v' w w' z t} R).leftDerived n).map eY.inv ≫
        (rawCoefficientTorHeightFunctorIso.{u, v', v, w', w, z, t} R L' M' n).inv.app Y =
    ((ModuleCat.BalancedTensor.functor R U
      (LieModuleCat.RightUniversalEnveloping.representObj R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
      ModuleCat.{max u v v' w w' z t} R).leftDerived n).map eX.inv ≫
      (rawCoefficientTorHeightFunctorIso.{u, v, v', w, w', z, t} R L M n).inv.app X ≫
        (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map
          (((ModuleCat.BalancedTensor.functor R U
          (LieModuleCat.RightUniversalEnveloping.representObj R L
          (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
          ModuleCat.{max u v v' w w' z} R).leftDerived n).map a₀ ≫
          (Functor.leftDerivedSquareHom
            (ModuleCat.restrictScalars.{max u v v' w w' z} ((UniversalEnvelopingAlgebra.map R f).toRingHom))
            (𝟭 (ModuleCat.{max u v v' w w' z} R))
            (ModuleCat.BalancedTensor.functor R U
            (LieModuleCat.RightUniversalEnveloping.representObj R L
            (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
            ModuleCat.{max u v v' w w' z} R)
            (ModuleCat.BalancedTensor.functor R U'
            (LieModuleCat.RightUniversalEnveloping.representObj R L'
            (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M')) : ModuleCat.{max u v v' w w' z} U' ⥤
            ModuleCat.{max u v v' w w' z} R)
            (rightTensorLieTransformation.{u, v, v', max w w' z} R L f
            (LieModuleCat.RightUniversalEnveloping.representObj R L
            (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
            (LieModuleCat.RightUniversalEnveloping.representObj R L'
            (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M'))
            (LieModuleCat.RightUniversalEnveloping.representLieMapSemilinear.{u, v, max u v v' w w' z, v', max u v
            v' w w' z} R L f (rawLieCoefficientMapAt.{u, v, v', w, w', z} R L f M M' h))) n).app Y)
  rw [← Category.assoc (S₁.app _), hNat]
  simp only [Category.assoc]
  rw [← Category.assoc
    (((ModuleCat.BalancedTensor.functor R U
    (LieModuleCat.RightUniversalEnveloping.representObj R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
    ModuleCat.{max u v v' w w' z t} R).leftDerived n).map a₁), ← Functor.map_comp, ← hInput]
  simpa only [Functor.map_comp, Category.assoc] using hPrefixed

end ChevalleyEilenberg
