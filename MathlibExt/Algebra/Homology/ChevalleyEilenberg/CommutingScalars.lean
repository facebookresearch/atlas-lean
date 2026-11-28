/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientFunctor
public import MathlibExt.Algebra.Category.LieModuleCat.End
public import MathlibExt.CategoryTheory.Preadditive.FunctorEnd

/-!
# Coefficient-ring actions commuting with the Lie action

Let X be a Lie module over an R-Lie algebra L, with R commutative. A ring homomorphism ρ : S →
End_R(X) commuting with every L-action map gives an S-action on the CE complex. Its degree-n
action is a ⊗ m ↦ a ⊗ ρ(s)(m), and the induced actions on homology are obtained from the
coefficient homology functors.

The CE boundary commutes with these degree actions. It is therefore S-linear, giving a chain
complex over S with the same underlying terms and boundary functions. The ring S may be
noncommutative and its carrier universe is independent of those of R, L and X.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w z


namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]
  (X : LieModuleCat.{w} R L) {S : Type z} [Ring S]

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra with its Lie ring
structure. Let X be a Lie module over L with carrier universe w, let S be a ring, and let ρ :
S →+* Module.End R X satisfy ρ(s)(⁅l, m⁆) = ⁅l, ρ(s)(m)⁆ for every s : S, l : L and m : X. The
coefficient functor gives a ring homomorphism S → End(coefficientComplex R L X). Its action in
each degree is identity on ⋀[R]^n L tensored with ρ(s) on X. -/
def coefficientComplexRingAction (ρ : S →+* Module.End R X)
    (hρ : ∀ (s : S) (x : L) (m : X), ρ s ⁅x, m⁆ = ⁅x, ρ s m⁆) :
    S →+* End (coefficientComplex R L X) :=
  ((coefficientComplexFunctor R L).mapEndRingHom X).comp
    (LieModuleCat.endRingHomOfLinearAction R L X ρ hρ)

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra with its Lie ring
structure. Let X be a Lie module over L with carrier universe w, let S be a ring, and let ρ :
S →+* Module.End R X satisfy ρ(s)(⁅l, m⁆) = ⁅l, ρ(s)(m)⁆ for every s : S, l : L and m : X. For
n : ℕ, the coefficient homology functor gives a ring homomorphism S →
End(H_n(coefficientComplex R L X)). It is the action induced on homology by the coefficient
chain endomorphisms. -/
def coefficientHomologyRingAction (ρ : S →+* Module.End R X)
    (hρ : ∀ (s : S) (x : L) (m : X), ρ s ⁅x, m⁆ = ⁅x, ρ s m⁆) (n : ℕ) :
    S →+* End ((coefficientComplex R L X).homology n) :=
  ((coefficientHomologyFunctor R L n).mapEndRingHom X).comp
    (LieModuleCat.endRingHomOfLinearAction R L X ρ hρ)

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra with its Lie ring
structure. Let X be a Lie module over L with carrier universe w, let S be a ring, and let ρ :
S →+* Module.End R X satisfy ρ(s)(⁅l, m⁆) = ⁅l, ρ(s)(m)⁆ for every s : S, l : L and m : X. For
s : S, n : ℕ, a : ⋀[R]^n L and m : X, the degree-n chain action sends a ⊗ₜ[R] m to a ⊗ₜ[R]
ρ(s)(m). -/
theorem coefficientComplexRingAction_f_tmul (ρ : S →+* Module.End R X)
    (hρ : ∀ (s : S) (x : L) (m : X), ρ s ⁅x, m⁆ = ⁅x, ρ s m⁆)
    (s : S) (n : ℕ) (a : ⋀[R]^n L) (m : X) :
    ((coefficientComplexRingAction R L X ρ hρ s).asHom.f n).hom
        (a ⊗ₜ[R] m) = a ⊗ₜ[R] ρ s m :=
  coefficientComplexFunctor_map_f_tmul R L
    (LieModuleCat.endRingHomOfLinearAction R L X ρ hρ s).asHom n a m

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra with its Lie ring
structure. Let X be a Lie module over L with carrier universe w, let S be a ring, and let ρ :
S →+* Module.End R X satisfy ρ(s)(⁅l, m⁆) = ⁅l, ρ(s)(m)⁆ for every s : S, l : L and m : X. For
n : ℕ, coefficientDegreeRingAction is the ring homomorphism S → Module.End R
((coefficientComplex R L X).X n) obtained by evaluating the chain action in degree n. -/
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

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra with its Lie ring
structure. Let X be a Lie module over L with carrier universe w, let S be a ring, and let ρ :
S →+* Module.End R X satisfy ρ(s)(⁅l, m⁆) = ⁅l, ρ(s)(m)⁆ for every s : S, l : L and m : X. For
n : ℕ, coefficientScalarChainObject is the carrier of ⋀[R]^n L ⊗[R] X equipped with the
S-module action induced by coefficientDegreeRingAction. It is an object of ModuleCat.{max u v
w} S. -/
abbrev coefficientScalarChainObject (ρ : S →+* Module.End R X)
    (hρ : ∀ (s : S) (x : L) (m : X), ρ s ⁅x, m⁆ = ⁅x, ρ s m⁆) (n : ℕ) :
    ModuleCat.{max u v w} S :=
  let M := (coefficientComplex R L X).X n
  letI : Module S M := Module.compHom M (coefficientDegreeRingAction R L X ρ hρ n)
  ModuleCat.of S M

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra with its Lie ring
structure. Let X be a Lie module over L with carrier universe w, let S be a ring, and let ρ :
S →+* Module.End R X satisfy ρ(s)(⁅l, m⁆) = ⁅l, ρ(s)(m)⁆ for every s : S, l : L and m : X. For
every n : ℕ, the CE boundary from degree n + 1 to n is an S-linear map between
coefficientScalarChainObject in those degrees. Its underlying function is the
coefficientComplex R L X boundary. -/
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

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra with its Lie ring
structure. Let X be a Lie module over L with carrier universe w, let S be a ring, and let ρ :
S →+* Module.End R X satisfy ρ(s)(⁅l, m⁆) = ⁅l, ρ(s)(m)⁆ for every s : S, l : L and m : X. The
coefficientScalarChainObject degrees and coefficientScalarDifferential boundaries define a
chain complex in ModuleCat.{max u v w} S indexed by ℕ. Its underlying carriers and boundary
functions are those of the R-linear CE coefficient complex. -/
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
