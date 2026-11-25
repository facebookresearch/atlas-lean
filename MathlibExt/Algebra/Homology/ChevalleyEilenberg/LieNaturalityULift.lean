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

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.LieNaturality
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.Additive

/-!
# Chevalley–Eilenberg coefficient maps in independent universes

A Lie homomorphism and a compatible coefficient homomorphism induce a chain map between
Chevalley–Eilenberg complexes after universe lifting. The components apply the exterior-power
map and coefficient map to each exterior tensor.

Source and target Lie algebras and coefficient modules may have independent carrier universes.
All comparisons retain the ground-ring action.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v v' w w' z

namespace ChevalleyEilenberg

attribute [local implicit_reducible] coefficientComplex

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

/-- Apply the universe lift to the coefficient complex. -/
def coefficientComplexULift (M : LieModuleCat.{w} R L) :
    ChainComplex (ModuleCat.{max u v w z} R) ℕ :=
  ((ModuleCat.uliftFunctor.{z, max u v w} R).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (coefficientComplex R L M)

section Maps

variable {L' : Type v'} [LieRing L'] [LieAlgebra R L']
variable (f : L →ₗ⁅R⁆ L')
variable (M : LieModuleCat.{w} R L) (N : LieModuleCat.{w'} R L')

/-- The CE chain map, placed in the common lifted module universe. -/
def coefficientLieComplexMapULift (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) :
    coefficientComplexULift.{u,v,w,max u v v' w w'} R L M ⟶
      coefficientComplexULift.{u,v',w',max u v v' w w'} R L' N where
  f n := ModuleCat.ofHom
    (ULift.moduleEquiv.symm.toLinearMap.comp
      ((coefficientLieDegreeMap R L f M N g n).comp ULift.moduleEquiv.toLinearMap))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    change ULift.up
        (((coefficientComplex R L' N).d i j).hom
          (coefficientLieDegreeMap R L f M N g i (ULift.down p))) =
      ULift.up (coefficientLieDegreeMap R L f M N g j
        (((coefficientComplex R L M).d i j).hom (ULift.down p)))
    by_cases h : i = j + 1
    · subst i
      rw [coefficientComplex_d_succ, coefficientComplex_d_succ]
      change ULift.up
          (coefficientDifferential R L' N j
            (coefficientLieDegreeMap R L f M N g (j + 1) (ULift.down p))) =
        ULift.up (coefficientLieDegreeMap R L f M N g j
          (coefficientDifferential R L M j (ULift.down p)))
      exact congrArg ULift.up
        (LinearMap.congr_fun (coefficientLieDifferential_naturality R L f M N g j)
          (ULift.down p)).symm
    · rw [coefficientComplex_d_eq_zero R L' N i j h,
        coefficientComplex_d_eq_zero R L M i j h]
      change ULift.up (0 : (⋀[R]^j L') ⊗[R] N) =
        ULift.up (coefficientLieDegreeMap R L f M N g j (0 : (⋀[R]^j L) ⊗[R] M))
      rw [map_zero]

/-- The lifted chain map keeps the concrete exterior and coefficient formula. -/
theorem coefficientLieComplexMapULift_f_tmul
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) (n : ℕ)
    (a : ⋀[R]^n L) (m : M) :
    ((coefficientLieComplexMapULift R L f M N g).f n).hom (ULift.up (a ⊗ₜ[R] m)) =
      ULift.up (exteriorPower.map n f.toLinearMap a ⊗ₜ[R] g m) := by
  change ULift.up (coefficientLieDegreeMap R L f M N g n (a ⊗ₜ[R] m)) = _
  rw [coefficientLieDegreeMap_tmul]

end Maps

section Restriction

variable {L' : Type v'} [LieRing L'] [LieAlgebra R L']
variable (f : L →ₗ⁅R⁆ L') (N : LieModuleCat.{w} R L')

/-- The restriction map for independent Lie algebra universes. -/
def coefficientRestrictionMapULift :
    coefficientComplexULift.{u,v,w,max u v v' w} R L (LieModuleCat.restrictObj f N) ⟶
      coefficientComplexULift.{u,v',w,max u v v' w} R L' N :=
  coefficientLieComplexMapULift R L f (LieModuleCat.restrictObj f N) N LieModuleHom.id

@[simp]
theorem coefficientRestrictionMapULift_f_tmul (n : ℕ) (a : ⋀[R]^n L) (m : N) :
    ((coefficientRestrictionMapULift R L f N).f n).hom (ULift.up (a ⊗ₜ[R] m)) =
      ULift.up (exteriorPower.map n f.toLinearMap a ⊗ₜ[R] m) := by
  rw [coefficientRestrictionMapULift, coefficientLieComplexMapULift_f_tmul,
    LieModuleHom.id_apply]

/-- Restriction induces the homology map of the lifted CE complexes. -/
def coefficientRestrictionHomologyMapULift (n : ℕ) :
    (coefficientComplexULift.{u,v,w,max u v v' w} R L
      (LieModuleCat.restrictObj f N)).homology n ⟶
        (coefficientComplexULift.{u,v',w,max u v v' w} R L' N).homology n :=
  HomologicalComplex.homologyMap (coefficientRestrictionMapULift R L f N) n

end Restriction

end ChevalleyEilenberg
