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

public import MathlibExt.Algebra.Category.LieModuleCat.RightUniversalEnveloping
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.TorZeroAt
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientFunctor

/-!
# Lie coefficients and enveloping Tor

A left Lie module extends to a right universal-enveloping module with negative right-generator
action. Restricting this action back to left Lie coefficients recovers the original module,
and the corresponding coefficient complexes are isomorphic.

When the underlying Lie module is free over the commutative ground ring, coefficient homology
computes enveloping Tor with the trivial module. Compatible Lie and coefficient maps yield
natural comparisons, including the degree-zero coinvariant and scalar-unit class.
-/

@[expose] public section

noncomputable section

universe u v v' w z z'

open CategoryTheory MulOpposite
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

attribute [local implicit_reducible] coefficientComplex HomologicalComplex.homologyFunctor

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

local instance nativeCoefficientTensor_additive {A : Type v} [Ring A] [Algebra R A]
    (M : ModuleCat.{z} Aᵐᵒᵖ) : (ModuleCat.BalancedTensor.functor.{u, v, z, z'} R A M).Additive :=
  ModuleCat.BalancedTensor.additive R A M

/-- Lie coefficients are recovered from their right enveloping algebra representation by the
identity carrier and its ground/action laws. -/
def nativeRightCoefficientsIso (M : LieModuleCat.{max u v v' w} R L) :
    M ≅ rightCoefficients R L (LieModuleCat.RightUniversalEnveloping.representObj R L M) where
  hom :=
    { toLinearMap :=
        { toFun := fun m => m
          map_add' := fun _ _ => rfl
          map_smul' := fun r m =>
            (LieModuleCat.RightUniversalEnveloping.representObj_ground_smul R L M r m).symm }
      map_lie' := by
        intro x m
        change @Bracket.bracket L M M.lieRingModule.toBracket x (show M from m) =
          -(op (UniversalEnvelopingAlgebra.ι R x) •
          (show LieModuleCat.RightUniversalEnveloping.representObj R L M from m))
        have h := LieModuleCat.RightUniversalEnveloping.representObj_op_ι R L M x (show M from m)
        exact ((congrArg Neg.neg h).trans (neg_neg _)).symm }
  inv :=
    { toLinearMap :=
        { toFun := fun m => m
          map_add' := fun _ _ => rfl
          map_smul' := fun r m =>
            LieModuleCat.RightUniversalEnveloping.representObj_ground_smul R L M r m }
      map_lie' := by
        intro x m
        change -(op (UniversalEnvelopingAlgebra.ι R x) •
          (show LieModuleCat.RightUniversalEnveloping.representObj R L M from m)) = @Bracket.bracket L M
            M.lieRingModule.toBracket x (show M from m)
        have h := LieModuleCat.RightUniversalEnveloping.representObj_op_ι R L M x (show M from m)
        exact (congrArg Neg.neg h).trans (neg_neg _) }
  hom_inv_id := by apply LieModuleHom.ext; intro m; rfl
  inv_hom_id := by apply LieModuleHom.ext; intro m; rfl

/-- The CE coefficient functor transports the identity-carrier coefficient isomorphism. -/
def nativeRightCoefficientComplexIso (M : LieModuleCat.{max u v v' w} R L) :
    coefficientComplex R L M ≅ rightEnvelopingCoefficientComplex R L
      (LieModuleCat.RightUniversalEnveloping.representObj R L M) :=
  (coefficientComplexFunctor R L).mapIso (nativeRightCoefficientsIso.{u, v, v', w} R L M)

theorem nativeRightCoefficientComplexIso_f_tmul (M : LieModuleCat.{max u v v' w} R L)
    (n : ℕ) (x : ⋀[R]^n L) (m : M) :
    ((nativeRightCoefficientComplexIso.{u, v, v', w} R L M).hom.f n).hom (x ⊗ₜ[R] m) =
      x ⊗ₜ[R] (show rightCoefficients R L
        (LieModuleCat.RightUniversalEnveloping.representObj R L M) from m) :=
  by
    have h := coefficientComplexFunctor_map_f_tmul R L
      (nativeRightCoefficientsIso.{u, v, v', w} R L M).hom n x m
    exact h.trans (congrArg (fun y : rightCoefficients R L
      (LieModuleCat.RightUniversalEnveloping.representObj R L M) => x ⊗ₜ[R] y) (show
        (nativeRightCoefficientsIso.{u, v, v', w} R L M).hom m = m from rfl))

/-- The Lie coefficient H₀ map to its trivial-module tensor, using the coefficient coinvariants
and scalar unit. -/
def nativeCoefficientHomologyZeroTensorIso (M : LieModuleCat.{max u v v' w} R L) :
    (coefficientComplex R L M).homology 0 ≅
      (ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L M)).obj (envelopingTrivialObject R L) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v v' w} R) (ComplexShape.down ℕ) 0).mapIso
    (nativeRightCoefficientComplexIso.{u, v, v', w} R L M) ≪≫
      rightCoefficientHomologyZeroTensorIso R L
        (LieModuleCat.RightUniversalEnveloping.representObj R L M)

/-- The canonical empty-word/coinvariant H₀ class keeps its coefficient and scalar unit in the
balanced tensor. -/
theorem nativeCoefficientHomologyZeroTensorIso_class (M : LieModuleCat.{max u v v' w} R L)
    (m : M) :
    (nativeCoefficientHomologyZeroTensorIso.{u, v, v', w} R L M).hom
      ((coefficientComplex R L M).isoHomologyι₀.inv
        ((coefficientComplex R L M).pOpcycles 0
          (exteriorPower.ιMulti R 0 Fin.elim0 ⊗ₜ[R] m))) =
      TensorProduct.Balanced.mk R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L M)
        ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))
          m (ULift.up (1 : R)) := by
  let a := (nativeRightCoefficientsIso.{u, v, v', w} R L M).hom
  have h := coefficientHomologyMap_zero_class R L M a m
  have hValue : a m = (show rightCoefficients R L
      (LieModuleCat.RightUniversalEnveloping.representObj R L M) from m) := rfl
  have hClass := (rightCoefficientHomologyZeroTensorIso_class R L
    (LieModuleCat.RightUniversalEnveloping.representObj R L M) m)
  have hMap := congrArg (rightCoefficientHomologyZeroTensorIso R L
    (LieModuleCat.RightUniversalEnveloping.representObj R L M)).hom h
  exact hMap.trans hClass

section JointMaps

variable {L' : Type v'} [LieRing L'] [LieAlgebra R L'] (f : L →ₗ⁅R⁆ L')
  (M : LieModuleCat.{max u v v' w} R L) (M' : LieModuleCat.{max u v v' w} R L')
  (h : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f M')

local notation "N" => LieModuleCat.RightUniversalEnveloping.representObj R L M
local notation "N'" => LieModuleCat.RightUniversalEnveloping.representObj R L' M'
local notation "g" => LieModuleCat.RightUniversalEnveloping.representLieMapSemilinear R L f h

/-- The all-degree CE joint coefficient/Lie map in the common carrier category, directly from the
differential naturality provider. -/
def nativeCoefficientLieComplexMap : coefficientComplex R L M ⟶ coefficientComplex R L' M' :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (coefficientLieDegreeMap R L f M M' h n)) (fun n => by
      simp only [coefficientComplex_d_succ]
      exact congrArg ModuleCat.ofHom (coefficientLieDifferential_naturality R L f M M' h n).symm)

theorem nativeCoefficientLieComplexMap_f_tmul (n : ℕ) (x : ⋀[R]^n L) (m : M) :
    ((nativeCoefficientLieComplexMap R L f M M' h).f n).hom (x ⊗ₜ[R] m) =
      exteriorPower.map n f.toLinearMap x ⊗ₜ[R] h m :=
  coefficientLieDegreeMap_tmul R L f M M' h n x m

/-- Identity-carrier coefficient recovery commutes with the joint CE variance map and the
semilinear right-representation map. -/
theorem nativeRightCoefficientComplexIso_lie_naturality :
    nativeCoefficientLieComplexMap R L f M M' h ≫ (nativeRightCoefficientComplexIso.{u, v', v, w} R L' M').hom =
      (nativeRightCoefficientComplexIso.{u, v, v', w} R L M).hom ≫ rightEnvelopingCoefficientLieComplexMap R L f g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x m
  change ((nativeRightCoefficientComplexIso.{u, v', v, w} R L' M').hom.f n).hom
      (((nativeCoefficientLieComplexMap R L f M M' h).f n).hom (x ⊗ₜ[R] m)) =
    ((rightEnvelopingCoefficientLieComplexMap R L f g).f n).hom
      (((nativeRightCoefficientComplexIso.{u, v, v', w} R L M).hom.f n).hom (x ⊗ₜ[R] m))
  rw [nativeCoefficientLieComplexMap_f_tmul, nativeRightCoefficientComplexIso_f_tmul,
    nativeRightCoefficientComplexIso_f_tmul, rightEnvelopingCoefficientLieComplexMap_f_tmul]
  rfl

/-- The canonical Tor map of Lie coefficient data is derived from their right representations and
scalar-change square. -/
def nativeLieCoefficientTorMap (n : ℕ) :=
  rightEnvelopingTorLieMapAt R L f N N' g n

end JointMaps

section ResolutionComparison

variable [Module.Free R L]

/-- The full Lie-coefficient CE homology computes the right-representation Tor, through the
constructed enveloping algebra resolution. -/
def nativeCoefficientHomologyIsoTor (M : LieModuleCat.{max u v v' w} R L) (n : ℕ) :
    (coefficientComplex R L M).homology n ≅
      (((ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L M) :
          ModuleCat.{max u v v' w} U ⥤ (ModuleCat.{max u v v' w} R)).leftDerived n).obj
        (liftedEnvelopingTrivial.{u, v, max u v v' w} R L)) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v v' w} R) (ComplexShape.down ℕ) n).mapIso
    (nativeRightCoefficientComplexIso.{u, v, v', w} R L M) ≪≫
      rightCoefficientHomologyIsoTorAt.{u, v, v', w} R L
        (LieModuleCat.RightUniversalEnveloping.representObj R L M) n

/-- The CE/Tor comparison agrees with the canonical coefficient/unit H₀ map through the derived
augmentation and lift cancellation. -/
theorem nativeCoefficientHomologyIsoTor_zero_canonical (M : LieModuleCat.{max u v v' w} R L) :
    (nativeCoefficientHomologyIsoTor.{u, v, v', w} R L M 0).hom ≫
      (ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L M) :
          ModuleCat.{max u v v' w} U ⥤ (ModuleCat.{max u v v' w} R)).fromLeftDerivedZero.app
            (liftedEnvelopingTrivial.{u, v, max u v v' w} R L) ≫
      (rightTrivialTensorLiftEquiv.{u, v, v', w} R L
        (LieModuleCat.RightUniversalEnveloping.representObj R L M)).toModuleIso.hom =
      (nativeCoefficientHomologyZeroTensorIso.{u, v, v', w} R L M).hom := by
  let a := HomologicalComplex.homologyMap (nativeRightCoefficientComplexIso.{u, v, v', w} R L M).hom 0
  have h := rightCoefficientHomologyIsoTorAt_zero_canonical.{u, v, v', w} R L
    (LieModuleCat.RightUniversalEnveloping.representObj R L M)
  exact (Category.assoc _ _ _).trans (congrArg (fun t => a ≫ t) h)

variable {L' : Type v'} [LieRing L'] [LieAlgebra R L'] [Module.Free R L']
  (f : L →ₗ⁅R⁆ L') (M : LieModuleCat.{max u v v' w} R L) (M' : LieModuleCat.{max u v v' w} R L')
  (h : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f M')

/-- Full joint Lie and coefficient naturality for arbitrary Lie modules, under exactly the
free-base resolution hypotheses. -/
theorem nativeCoefficientHomologyIsoTor_lie_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (nativeCoefficientLieComplexMap R L f M M' h) n ≫
      (nativeCoefficientHomologyIsoTor.{u, v', v, w} R L' M' n).hom =
        (nativeCoefficientHomologyIsoTor.{u, v, v', w} R L M n).hom ≫ nativeLieCoefficientTorMap R L f M M' h n := by
  have hH := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (nativeRightCoefficientComplexIso_lie_naturality R L f M M' h)
  simp only [HomologicalComplex.homologyMap_comp] at hH
  change HomologicalComplex.homologyMap (nativeCoefficientLieComplexMap R L f M M' h) n ≫
      (HomologicalComplex.homologyMap (nativeRightCoefficientComplexIso.{u, v', v, w} R L' M').hom n ≫ _) = _
  rw [← Category.assoc, hH, Category.assoc, rightCoefficientHomologyIsoTorAt_lie_naturality]
  rfl

end ResolutionComparison

end ChevalleyEilenberg
