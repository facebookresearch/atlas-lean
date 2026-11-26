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
# Enveloping Hom cochains and exterior coordinates

Let `R` be a commutative ring, `L` an `R`-Lie algebra, and `M` a left module over `U =
U_R(L)`. In degree `n`, the cochain module is `Hom_U(C_n,M)`, where `C_•` is the enveloping
Chevalley–Eilenberg complex. Its differential is positive precomposition `f ↦ f ∘ d`.

The coordinates `C_n ≅ U ⊗[R] ⋀ⁿ[R] L` and tensor–Hom adjunction identify these cochains with
`Hom_R(⋀ⁿ[R] L,M)`. The forward map evaluates `f` on `w ⊗ 1`; the inverse sends `(w,a)` to `a
• f(w)`. The comparison is natural in coefficient morphisms, and the coefficient carrier has
an independent universe.
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

/-- The enveloping-linear Hom term of a coefficient cochain complex.

For a left `U_R(L)`-module `M`, degree `n` is the module of `U_R(L)`-linear maps from the
degree-`n` enveloping chain term to `M`. -/
abbrev envelopingHomTerm (n : ℕ) := (envelopingComplex R L).X n →ₗ[U] M

/-- Positive precomposition on enveloping Hom cochains.

For `f ∈ Hom_U(C_n,M)`, the cochain differential is `f ∘ d_(n+1) ∈ Hom_U(C_(n+1),M)`. -/
def envelopingHomDifferential (n : ℕ) :
    envelopingHomTerm R L M n →ₗ[R] envelopingHomTerm R L M (n + 1) where
  toFun f := f.comp ((envelopingComplex R L).d (n + 1) n).hom
  map_add' f g := by ext z; rfl
  map_smul' r f := by ext z; rfl

/-- The value of an enveloping Hom differential.

For a cochain `f` and `z ∈ C_(n+1)`, the differential has value `f(d_(n+1)(z))`. -/
theorem envelopingHomDifferential_apply (n : ℕ) (f : envelopingHomTerm R L M n)
    (z : (envelopingComplex R L).X (n + 1)) :
    envelopingHomDifferential R L M n f z =
      f (((envelopingComplex R L).d (n + 1) n).hom z) := rfl

/-- The square-zero equation for enveloping Hom cochains.

The composite of successive positive-precomposition differentials is zero because the
enveloping chain differential squares to zero. -/
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

/-- The Hom cochain complex of the enveloping chain complex.

For a left `U_R(L)`-module `M`, the term in degree `n` is `Hom_U(C_n,M)` and the differential
is positive precomposition with the chain differential. It is an `R`-module cochain complex in
the joint ring, Lie, and coefficient universe. -/
def envelopingHomComplex : CochainComplex (ModuleCat.{max u v w} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (envelopingHomTerm R L M n))
    (fun n => ModuleCat.ofHom (envelopingHomDifferential R L M n)) (by
      intro n
      rw [← ModuleCat.ofHom_comp, envelopingHomDifferential_comp, ModuleCat.ofHom_zero])

/-- The successor differential of the enveloping Hom complex.

The map from cochain degree `n` to `n+1` is the categorical `R`-module map associated to
positive precomposition by the chain differential. -/
@[simp]
theorem envelopingHomComplex_d_succ (n : ℕ) :
    (envelopingHomComplex R L M).d n (n + 1) =
      ModuleCat.ofHom (envelopingHomDifferential R L M n) := by
  simp only [envelopingHomComplex, CochainComplex.of_d]

/-- The exterior coordinates of enveloping-linear cochains.

The `R`-linear equivalence `Hom_U(C_n,M) ≃ₗ[R] Hom_R(⋀ⁿ L,M)` evaluates on the regular
coefficient unit; its inverse extends by the left `U`-action on `M`. -/
def envelopingHomCoordinates (n : ℕ) :
    envelopingHomTerm R L M n ≃ₗ[R] ((⋀[R]^n L) →ₗ[R] M) :=
  (LinearEquiv.congrLeft (M := M) R (envelopingCoordinates R L n)).trans
    (TensorProduct.algebraTensorHomEquiv R U (⋀[R]^n L) M)

/-- Evaluation at the regular unit in enveloping Hom coordinates.

The exterior coordinate of an enveloping cochain `f` at `w ∈ ⋀ⁿ L` is `f(w ⊗ 1)`. -/
@[simp]
theorem envelopingHomCoordinates_apply (n : ℕ) (f : envelopingHomTerm R L M n)
    (w : ⋀[R]^n L) :
    envelopingHomCoordinates R L M n f w =
      f (w ⊗ₜ[R] (1 : regularCoefficients R L)) := by
  rw [envelopingHomCoordinates, LinearEquiv.trans_apply,
    TensorProduct.algebraTensorHomEquiv_apply]
  change f ((envelopingCoordinates R L n).symm ((1 : U) ⊗ₜ[R] w)) = _
  rw [envelopingCoordinates_symm_tmul]

/-- The coefficient-action formula for inverse Hom coordinates.

For an exterior cochain `f : ⋀ⁿ L →ₗ[R] M`, the corresponding enveloping-linear map sends `w ⊗
a` to `a • f(w)`. -/
theorem envelopingHomCoordinates_symm_tmul (n : ℕ) (f : (⋀[R]^n L) →ₗ[R] M)
    (w : ⋀[R]^n L) (a : regularCoefficients R L) :
    (envelopingHomCoordinates R L M n).symm f (w ⊗ₜ[R] a) = a • f w := by
  change (TensorProduct.algebraTensorHomEquiv R U (⋀[R]^n L) M).symm f
    (envelopingCoordinates R L n (w ⊗ₜ[R] a)) = _
  rw [envelopingCoordinates_tmul, TensorProduct.algebraTensorHomEquiv_symm_tmul]

/-- Reconstruction of an enveloping cochain from unit coordinates.

Every enveloping-linear cochain satisfies `f(w ⊗ a) = a • c(f)(w)`, where `c(f)(w) = f(w ⊗
1)`. -/
theorem envelopingHomTerm_tmul (n : ℕ) (f : envelopingHomTerm R L M n)
    (w : ⋀[R]^n L) (a : regularCoefficients R L) :
    f (w ⊗ₜ[R] a) = a • envelopingHomCoordinates R L M n f w := by
  have h := congrArg (fun g : envelopingHomTerm R L M n => g (w ⊗ₜ[R] a))
    ((envelopingHomCoordinates R L M n).symm_apply_apply f)
  rw [envelopingHomCoordinates_symm_tmul] at h
  exact h.symm

/-- The ground-linear restriction of an enveloping cochain.

An enveloping-linear map `C_n → M` restricts along `R → U_R(L)` to a ground-linear map from
the restricted chain term to `M`. -/
def envelopingHomGroundMap (n : ℕ) (f : envelopingHomTerm R L M n) :
    envelopingGroundObject R L n →ₗ[R] M := by
  letI : Module R ((envelopingComplex R L).X n) :=
    Module.compHom ((envelopingComplex R L).X n) (algebraMap R U)
  letI : IsScalarTower R U ((envelopingComplex R L).X n) :=
    IsScalarTower.of_compHom R U ((envelopingComplex R L).X n)
  exact f.restrictScalars R

/-- The value of a ground-restricted enveloping cochain.

Restricting an enveloping-linear cochain to the ground ring retains its value at every chain
element. -/
@[simp]
theorem envelopingHomGroundMap_apply (n : ℕ) (f : envelopingHomTerm R L M n)
    (z : envelopingGroundObject R L n) : envelopingHomGroundMap R L M n f z = f z := rfl

section CoefficientNaturality

variable {M} {M' : ModuleCat.{w} (UniversalEnvelopingAlgebra R L)} (g : M ⟶ M')

/-- Naturality of exterior Hom coordinates in the coefficient module.

For a `U_R(L)`-linear coefficient map `g : M → M'`, the exterior coordinates of `g ∘ f` equal
`g` restricted to `R` composed with the exterior coordinates of `f`. -/
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
