/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.GroundCoordinates
public import MathlibExt.LinearAlgebra.TensorProduct.AlgebraTensorHom

/-!
# Hom cochains of the enveloping Chevalley–Eilenberg complex

The cochains are enveloping-linear maps to a left coefficient module.
Their differential is positive precomposition with the chain differential.
Tensor Hom cancellation identifies these maps with ground-linear exterior
cochains: evaluation at the regular coefficient unit gives the forward map,
and the left coefficient action gives its inverse. The coefficient carrier
may have an independent universe.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

variable (M : ModuleCat.{w} (UniversalEnvelopingAlgebra R L))

/-- Hom from the original enveloping CE term to the original left
UEA coefficient module. -/
abbrev envelopingHomTerm (n : ℕ) := (envelopingComplex R L).X n →ₗ[U] M

/-- The Hom differential is precomposition with the original native
enveloping differential, with positive precomposition. -/
def envelopingHomDifferential (n : ℕ) :
    envelopingHomTerm R L M n →ₗ[R] envelopingHomTerm R L M (n + 1) where
  toFun f := f.comp ((envelopingComplex R L).d (n + 1) n).hom
  map_add' f g := by ext z; rfl
  map_smul' r f := by ext z; rfl

theorem envelopingHomDifferential_apply (n : ℕ) (f : envelopingHomTerm R L M n)
    (z : (envelopingComplex R L).X (n + 1)) :
    envelopingHomDifferential R L M n f z =
      f (((envelopingComplex R L).d (n + 1) n).hom z) := rfl

/-- The Hom differential squares to zero by the original chain
complex's square-zero law. -/
theorem envelopingHomDifferential_comp (n : ℕ) :
    (envelopingHomDifferential R L M (n + 1)).comp
      (envelopingHomDifferential R L M n) = 0 := by
  ext f z
  change f (((envelopingComplex R L).d (n + 1) n).hom
    (((envelopingComplex R L).d (n + 2) (n + 1)).hom z)) = 0
  have hd := (envelopingComplex R L).d_comp_d (n + 2) (n + 1) n
  have hz := congrArg (fun h => h.hom z) hd
  change ((envelopingComplex R L).d (n + 1) n).hom
    (((envelopingComplex R L).d (n + 2) (n + 1)).hom z) = 0 at hz
  rw [hz, map_zero]

/-- The Hom cochain complex of the original UEA CE complex. -/
def envelopingHomComplex : CochainComplex (ModuleCat.{max u v w} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (envelopingHomTerm R L M n))
    (fun n => ModuleCat.ofHom (envelopingHomDifferential R L M n)) (by
      intro n
      rw [← ModuleCat.ofHom_comp, envelopingHomDifferential_comp, ModuleCat.ofHom_zero])

@[simp]
theorem envelopingHomComplex_d_succ (n : ℕ) :
    (envelopingHomComplex R L M).d n (n + 1) =
      ModuleCat.ofHom (envelopingHomDifferential R L M n) := by
  simp only [envelopingHomComplex, CochainComplex.of_d]

/-- Native U-linear coordinates and native noncommutative algebra tensor Hom
cancellation give the ground-linear exterior cochain coordinates. -/
def envelopingHomCoordinates (n : ℕ) :
    envelopingHomTerm R L M n ≃ₗ[R] ((⋀[R]^n L) →ₗ[R] M) :=
  (LinearEquiv.congrLeft (M := M) R (envelopingCoordinates R L n)).trans
    (TensorProduct.algebraTensorHomEquiv R U (⋀[R]^n L) M)

/-- The coordinates evaluate an UEA-linear map at the original regular
coefficient unit. -/
@[simp]
theorem envelopingHomCoordinates_apply (n : ℕ) (f : envelopingHomTerm R L M n)
    (w : ⋀[R]^n L) :
    envelopingHomCoordinates R L M n f w =
      f (w ⊗ₜ[R] (1 : regularCoefficients R L)) := by
  rw [envelopingHomCoordinates, LinearEquiv.trans_apply,
    TensorProduct.algebraTensorHomEquiv_apply]
  change f ((envelopingCoordinates R L n).symm ((1 : U) ⊗ₜ[R] w)) = _
  rw [envelopingCoordinates_symm_tmul]

/-- The inverse uses the positive left UEA coefficient action. -/
theorem envelopingHomCoordinates_symm_tmul (n : ℕ) (f : (⋀[R]^n L) →ₗ[R] M)
    (w : ⋀[R]^n L) (a : regularCoefficients R L) :
    (envelopingHomCoordinates R L M n).symm f (w ⊗ₜ[R] a) = a • f w := by
  change (TensorProduct.algebraTensorHomEquiv R U (⋀[R]^n L) M).symm f
    (envelopingCoordinates R L n (w ⊗ₜ[R] a)) = _
  rw [envelopingCoordinates_tmul, TensorProduct.algebraTensorHomEquiv_symm_tmul]

/-- Every UEA-linear cochain is determined by its value at the regular
unit, and recovers all regular coefficients by the positive left action. -/
theorem envelopingHomTerm_tmul (n : ℕ) (f : envelopingHomTerm R L M n)
    (w : ⋀[R]^n L) (a : regularCoefficients R L) :
    f (w ⊗ₜ[R] a) = a • envelopingHomCoordinates R L M n f w := by
  have h := congrArg (fun g : envelopingHomTerm R L M n => g (w ⊗ₜ[R] a))
    ((envelopingHomCoordinates R L M n).symm_apply_apply f)
  rw [envelopingHomCoordinates_symm_tmul] at h
  exact h.symm

/-- Restrict an UEA-linear cochain to the exact native ground scalar
dictionary on the original CE term. -/
def envelopingHomGroundMap (n : ℕ) (f : envelopingHomTerm R L M n) :
    envelopingGroundObject R L n →ₗ[R] M := by
  letI : Module R ((envelopingComplex R L).X n) :=
    Module.compHom ((envelopingComplex R L).X n) (algebraMap R U)
  letI : IsScalarTower R U ((envelopingComplex R L).X n) :=
    IsScalarTower.of_compHom R U ((envelopingComplex R L).X n)
  exact f.restrictScalars R

@[simp]
theorem envelopingHomGroundMap_apply (n : ℕ) (f : envelopingHomTerm R L M n)
    (z : envelopingGroundObject R L n) : envelopingHomGroundMap R L M n f z = f z := rfl

section CoefficientNaturality

variable {M} {M' : ModuleCat.{w} (UniversalEnvelopingAlgebra R L)} (g : M ⟶ M')

/-- coefficient morphisms commute with the Hom unit coordinates. -/
theorem envelopingHomCoordinates_naturality (n : ℕ) (f : envelopingHomTerm R L M n) :
    envelopingHomCoordinates R L M' n (g.hom.comp f) =
      (((ModuleCat.restrictScalars (algebraMap R U)).map g).hom).comp
        (envelopingHomCoordinates R L M n f) := by
  apply LinearMap.ext
  intro w
  change envelopingHomCoordinates R L M' n (g.hom.comp f) w =
    g.hom (envelopingHomCoordinates R L M n f w)
  rw [envelopingHomCoordinates_apply, envelopingHomCoordinates_apply]
  rfl

end CoefficientNaturality

end ChevalleyEilenberg
