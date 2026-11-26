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
# Naturality of Lie-coefficient Tor under universe lifting

Let R be a commutative ring, f : L →ₗ⁅R⁆ L′ a Lie map, and h : M → f* M′ an equivariant
coefficient map. The Lie algebras and coefficient modules may occupy independent universes.
Put H = max(u,v,v′,w,w′,z) and H′ = max(H,t).

The balanced-tensor maps induced by f and h commute with the coefficient, input, and output
comparisons between H and H′. Their left-derived maps satisfy the same identity in every
degree, for arbitrary input morphisms. Evaluating at the augmentation modules gives height
naturality of the Lie-coefficient Tor maps. No freeness of either Lie algebra is required for
these Tor identities.
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

/-- Let R be a commutative ring, f : L →ₗ⁅R⁆ L′ a Lie map, and h : M → f* M′ an equivariant map of
coefficient modules in independent universes. Put H = max(u,v,v′,w,w′,z) and H′ = max(H,t),
and write U = U_R(L), U′ = U_R(L′), σ = U_R(f). Let F_H(X) = N_H ⊗_U X and G_H(Y) = N′_H
⊗_{U′} Y, where N_H and N′_H are the right enveloping representations of the lifted
coefficients. Let α_H : F_H(σ*Y) → G_H(Y) be induced by h, ν_M : F_H′(I_U X) ≅ V(F_H X) the
tensor height comparison, and r_Y : I_U(σ*Y) ≅ σ*(I_U′Y) the lift–restriction comparison. Then
ν_M.hom at σ*Y followed by V(α_H,Y) equals F_H′(r_Y.hom) followed by α_H′ at I_U′Y and
ν_M′.hom at Y. Equivalently, the two composed natural transformations in the displayed
scalar-restriction and tensor-lift square agree. -/
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

/-- Let R be a commutative ring, f : L →ₗ⁅R⁆ L′ a Lie map, and h : M → f* M′ an equivariant
coefficient map. Put H = max(u,v,v′,w,w′,z), H′ = max(H,t), U = U_R(L), U′ = U_R(L′), and σ =
U_R(f). For X ∈ ModuleCat_H(U), Y ∈ ModuleCat_H(U′), and a : X → σ*Y, define k_H,n(a) =
(L_nF_H)(a) followed by the degree-n derived coefficient transformation, where F_H(X) = N_H
⊗_U X and N_H represents the lifted coefficient M. Let D_M,n : V∘L_nF_H ≅ L_nF_H′∘I_U be the
derived height comparison, and r_Y : I_U(σ*Y) ≅ σ*(I_U′Y). Then, for every n ∈ ℕ,
k_H′,n(I_U(a) ≫ r_Y.hom) ≫ D_M′,n.inv at Y = D_M,n.inv at X ≫ V(k_H,n(a)). The coefficient
modules and Lie algebras have independent carrier universes; no freeness hypothesis is
imposed. -/
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

/-- Let R be a commutative ring and f : L →ₗ⁅R⁆ L′ a Lie map between independently sized R-Lie
algebras. Put H = max(u,v,v′,w,w′,z), H′ = max(H,t), and σ = U_R(f). Let T_H(L) and T_H(L′) be
the lifted augmentation modules, c_H : T_H(L) → σ*T_H(L′) their canonical scalar-preserving
map, and τ_L : I_U(T_H(L)) ≅ T_H′(L) the repeated-input-lift flattening. With r the
lift–restriction comparison, τ_L.inv ≫ I_U(c_H) ≫ r.hom = c_H′ ≫ σ*(τ_L′.inv). Thus both maps
preserve the scalar representative in R. -/
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

/-- Let R be a commutative ring, f : L →ₗ⁅R⁆ L′ a Lie map, and h : M → f* M′ an equivariant
coefficient map, with the Lie and coefficient carriers in independent universes. Put H =
max(u,v,v′,w,w′,z), H′ = max(H,t), and let V be the R-module lift H → H′. For n ∈ ℕ, write
K_H,n for the Tor map induced by U_R(f), the represented coefficient map, and the
augmentation-module map. Let J_M,n : V(Tor_H,n(M)) ≅ Tor_H′,n(M) and J_M′,n be the Tor height
isomorphisms. Then K_H′,n ≫ J_M′,n.inv = J_M,n.inv ≫ V(K_H,n). The map on Tor is defined
through the derived balanced-tensor square; neither Lie algebra is assumed free. -/
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
