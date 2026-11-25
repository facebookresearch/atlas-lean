/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientFunctor
public import MathlibExt.Algebra.Category.LieModuleCat.End

/-!
# Commuting scalar actions on Chevalley–Eilenberg chains

A coefficient-ring action commuting with the Lie action induces actions on
coefficient chains and their homology. The degree actions make the
Chevalley–Eilenberg differential linear over the coefficient ring, giving a
complex with the same carriers and differential over that ring.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w z


namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]
  (X : LieModuleCat.{w} R L) {S : Type z} [Ring S]

/-- The existing coefficient functor sends a commuting action to the original CE complex. -/
def coefficientComplexRingAction (ρ : S →+* Module.End R X)
    (hρ : ∀ (s : S) (x : L) (m : X), ρ s ⁅x, m⁆ = ⁅x, ρ s m⁆) :
    S →+* End (coefficientComplex R L X) :=
  ((coefficientComplexFunctor R L).mapEndRingHom X).comp
    (LieModuleCat.endRingHomOfLinearAction R L X ρ hρ)

/-- Native CE homology inherits the same commuting coefficient action in every degree. -/
def coefficientHomologyRingAction (ρ : S →+* Module.End R X)
    (hρ : ∀ (s : S) (x : L) (m : X), ρ s ⁅x, m⁆ = ⁅x, ρ s m⁆) (n : ℕ) :
    S →+* End ((coefficientComplex R L X).homology n) :=
  ((coefficientHomologyFunctor R L n).mapEndRingHom X).comp
    (LieModuleCat.endRingHomOfLinearAction R L X ρ hρ)

/-- The complex action retains identity on the exterior factor and the original coefficient
action. -/
theorem coefficientComplexRingAction_f_tmul (ρ : S →+* Module.End R X)
    (hρ : ∀ (s : S) (x : L) (m : X), ρ s ⁅x, m⁆ = ⁅x, ρ s m⁆)
    (s : S) (n : ℕ) (a : ⋀[R]^n L) (m : X) :
    ((coefficientComplexRingAction R L X ρ hρ s).asHom.f n).hom
        (a ⊗ₜ[R] m) = a ⊗ₜ[R] ρ s m :=
  coefficientComplexFunctor_map_f_tmul R L
    (LieModuleCat.endRingHomOfLinearAction R L X ρ hρ s).asHom n a m

/-- The degree endomorphism on the original native module carrier. -/
def coefficientDegreeRingAction (ρ : S →+* Module.End R X)
    (hρ : ∀ (s : S) (x : L) (m : X), ρ s ⁅x, m⁆ = ⁅x, ρ s m⁆) (n : ℕ) :
    S →+* Module.End R ((coefficientComplex R L X).X n) :=
  (ModuleCat.endRingEquiv ((coefficientComplex R L X).X n)).toRingHom.comp
    (((HomologicalComplex.eval (ModuleCat.{max u v w} R) (ComplexShape.down ℕ) n).mapEndRingHom
      (coefficientComplex R L X)).comp
      (coefficientComplexRingAction R L X ρ hρ))

theorem coefficientDegreeRingAction_apply (ρ : S →+* Module.End R X)
    (hρ : ∀ (s : S) (x : L) (m : X), ρ s ⁅x, m⁆ = ⁅x, ρ s m⁆) (n : ℕ) (s : S)
    (p : (coefficientComplex R L X).X n) :
    coefficientDegreeRingAction R L X ρ hρ n s p =
      ((coefficientComplexRingAction R L X ρ hρ s).asHom.f n).hom p := rfl

/-- The original CE degree with the coefficient-ring module structure. -/
abbrev coefficientScalarChainObject (ρ : S →+* Module.End R X)
    (hρ : ∀ (s : S) (x : L) (m : X), ρ s ⁅x, m⁆ = ⁅x, ρ s m⁆) (n : ℕ) :
    ModuleCat.{max u v w} S :=
  let M := (coefficientComplex R L X).X n
  letI : Module S M := Module.compHom M (coefficientDegreeRingAction R L X ρ hρ n)
  ModuleCat.of S M

/-- The original differential is linear for every commuting coefficient-ring action. -/
def coefficientScalarDifferential (ρ : S →+* Module.End R X)
    (hρ : ∀ (s : S) (x : L) (m : X), ρ s ⁅x, m⁆ = ⁅x, ρ s m⁆) (n : ℕ) :
    coefficientScalarChainObject R L X ρ hρ (n + 1) →ₗ[S]
      coefficientScalarChainObject R L X ρ hρ n where
  toFun := ((coefficientComplex R L X).d (n + 1) n).hom
  map_add' := ((coefficientComplex R L X).d (n + 1) n).hom.map_add
  map_smul' s p := by
    dsimp only [coefficientScalarChainObject] at p ⊢
    have h := (coefficientComplexRingAction R L X ρ hρ s).asHom.comm (n + 1) n
    have hp := ConcreteCategory.congr_hom h p
    change ((coefficientComplex R L X).d (n + 1) n).hom
        (((coefficientComplexRingAction R L X ρ hρ s).asHom.f (n + 1)).hom p) =
      ((coefficientComplexRingAction R L X ρ hρ s).asHom.f n).hom
        (((coefficientComplex R L X).d (n + 1) n).hom p)
    simpa only [ModuleCat.comp_apply] using hp

/-- The CE complex over the commuting coefficient ring, with unchanged carriers/differential. -/
abbrev coefficientScalarComplex (ρ : S →+* Module.End R X)
    (hρ : ∀ (s : S) (x : L) (m : X), ρ s ⁅x, m⁆ = ⁅x, ρ s m⁆) :
    ChainComplex (ModuleCat.{max u v w} S) ℕ :=
  ChainComplex.of (coefficientScalarChainObject R L X ρ hρ)
    (fun n => (show coefficientScalarChainObject R L X ρ hρ (n + 1) ⟶
        coefficientScalarChainObject R L X ρ hρ n from
      ModuleCat.ofHom
        (X := coefficientScalarChainObject R L X ρ hρ (n + 1))
        (Y := coefficientScalarChainObject R L X ρ hρ n)
        (coefficientScalarDifferential R L X ρ hρ n))) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro p
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
        LinearMap.comp_apply, LinearMap.zero_apply]
      change ((coefficientComplex R L X).d (n + 1) n).hom
        (((coefficientComplex R L X).d (n + 2) (n + 1)).hom p) = 0
      have h := (coefficientComplex R L X).d_comp_d (n + 2) (n + 1) n
      have h' := congrArg ModuleCat.Hom.hom h
      simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h'
      exact LinearMap.congr_fun h' p)

end ChevalleyEilenberg
