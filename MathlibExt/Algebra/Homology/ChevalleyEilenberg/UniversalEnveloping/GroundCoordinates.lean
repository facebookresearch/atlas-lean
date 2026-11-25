/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.FilteredDifferential
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Ground-ring coordinates for enveloping Chevalley–Eilenberg terms

Scalar restriction sends enveloping-module terms and differentials to the
ground ring. Tensor cancellation and linear Yoneda use these restricted
module structures. On a pure tensor, ground scalar multiplication is the
usual tensor scalar action. The all-degree bracket/action differential
formula is expressed in these coordinates.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

attribute [local instance] rightRegularLieRingModule rightRegularLieModule
attribute [local implicit_reducible] coefficientComplex

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- The exact native scalar restriction of an original enveloping CE term. -/
abbrev envelopingGroundObject (n : ℕ) : ModuleCat.{max u v} R :=
  (ModuleCat.restrictScalars (algebraMap R U)).obj ((envelopingComplex R L).X n)

/-- Native scalar restriction of the existing U-linear tensor coordinates. -/
def envelopingGroundCoordinates (n : ℕ) :
    envelopingGroundObject R L n ≃ₗ[R] U ⊗[R] (⋀[R]^n L) := by
  letI : Module R ((envelopingComplex R L).X n) :=
    Module.compHom ((envelopingComplex R L).X n) (algebraMap R U)
  letI : IsScalarTower R U ((envelopingComplex R L).X n) :=
    IsScalarTower.of_compHom R U ((envelopingComplex R L).X n)
  exact (envelopingCoordinates R L n).restrictScalars R

@[simp]
theorem envelopingGroundCoordinates_tmul (n : ℕ) (w : ⋀[R]^n L)
    (a : regularCoefficients R L) :
    envelopingGroundCoordinates R L n (w ⊗ₜ[R] a) = a ⊗ₜ[R] w :=
  envelopingCoordinates_tmul R L n w a

/-- The computed native U action recovers the original ground scalar action
on every pure CE tensor. -/
theorem envelopingGround_smul_tmul (n : ℕ) (r : R) (w : ⋀[R]^n L)
    (a : regularCoefficients R L) :
    r • (show envelopingGroundObject R L n from w ⊗ₜ[R] a) = (r • w) ⊗ₜ[R] a := by
  apply (envelopingGroundCoordinates R L n).injective
  calc
    _ = r • envelopingGroundCoordinates R L n (w ⊗ₜ[R] a) :=
      (envelopingGroundCoordinates R L n).map_smul r (w ⊗ₜ[R] a)
    _ = r • (a ⊗ₜ[R] w) :=
      congrArg (fun z : U ⊗[R] (⋀[R]^n L) => r • z) (envelopingGroundCoordinates_tmul R L n w a)
    _ = a ⊗ₜ[R] (r • w) := (TensorProduct.tmul_smul r a w).symm
    _ = _ := (envelopingGroundCoordinates_tmul R L n (r • w) a).symm

/-- A fixed enveloping coefficient gives a ground-linear map into
the exact native restricted CE term. -/
def envelopingGroundTmul (n : ℕ) (a : regularCoefficients R L) :
    (⋀[R]^n L) →ₗ[R] envelopingGroundObject R L n where
  toFun w := w ⊗ₜ[R] a
  map_add' w z := TensorProduct.add_tmul w z a
  map_smul' r w := (envelopingGround_smul_tmul R L n r w a).symm

@[simp]
theorem envelopingGroundTmul_apply (n : ℕ) (a : regularCoefficients R L) (w : ⋀[R]^n L) :
    envelopingGroundTmul R L n a w = w ⊗ₜ[R] a := rfl

/-- The restricted original UEA differential. -/
@[implicit_reducible]
def envelopingGroundDifferential (n : ℕ) :
    envelopingGroundObject R L (n + 1) →ₗ[R] envelopingGroundObject R L n :=
  ((ModuleCat.restrictScalars (algebraMap R U)).map ((envelopingComplex R L).d (n + 1) n)).hom

@[simp]
theorem envelopingGroundDifferential_apply (n : ℕ)
    (z : envelopingGroundObject R L (n + 1)) :
    envelopingGroundDifferential R L n z =
      ((envelopingComplex R L).d (n + 1) n).hom z := rfl

/-- The native successor map has the original coefficient boundary value. -/
theorem envelopingGroundDifferential_apply_coefficient (n : ℕ)
    (z : envelopingGroundObject R L (n + 1)) :
    envelopingGroundDifferential R L n z =
      coefficientDifferential R L (regularCoefficients R L) n z := by
  rw [envelopingGroundDifferential_apply]
  unfold envelopingComplex coefficientScalarComplex
  simp only [ChainComplex.of_d]
  change ((coefficientComplex R L (regularCoefficients R L)).d (n + 1) n).hom z = _
  rw [coefficientComplex_d_succ]
  rfl

/-- The existing all-degree bracket/action formula in the exact scalar
dictionary used by balanced tensor and Hom. -/
theorem envelopingGroundDifferential_apply_ιMulti_tmul (n : ℕ)
    (v : Fin (n + 1) → L) (a : regularCoefficients R L) :
    envelopingGroundDifferential R L n
      (exteriorPower.ιMulti R (n + 1) v ⊗ₜ[R] a) =
      envelopingGroundTmul R L n a
        (differential R L n (exteriorPower.ιMulti R (n + 1) v)) +
        ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
          envelopingGroundTmul R L n (a * UniversalEnvelopingAlgebra.ι R (v i))
            (exteriorPower.ιMulti R n (v ∘ i.succAbove)) := by
  refine (envelopingGroundDifferential_apply_coefficient R L n
    (show envelopingGroundObject R L (n + 1) from
      exteriorPower.ιMulti R (n + 1) v ⊗ₜ[R] a)).trans ?_
  calc
    _ = differential R L n (exteriorPower.ιMulti R (n + 1) v) ⊗ₜ[R] a +
        ∑ i : Fin (n + 1),
          ((-1 : R) ^ i.val • exteriorPower.ιMulti R n (v ∘ i.succAbove)) ⊗ₜ[R]
            (a * UniversalEnvelopingAlgebra.ι R (v i)) := by
      simpa only [TensorProduct.smul_tmul'] using
        envelopingDifferential_apply_ιMulti_tmul R L n v a
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact (envelopingGround_smul_tmul R L n ((-1 : R) ^ i.val)
        (exteriorPower.ιMulti R n (v ∘ i.succAbove))
        (a * UniversalEnvelopingAlgebra.ι R (v i))).symm

end ChevalleyEilenberg
