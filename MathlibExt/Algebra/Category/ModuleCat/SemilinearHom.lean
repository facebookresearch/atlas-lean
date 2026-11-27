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

public import MathlibExt.LinearAlgebra.TensorProduct.HomFiniteFactor
public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# Semilinear Hom functors and finite projective tensor factors

For a scalar homomorphism `σ : R →+* S`, semilinear Hom is contravariant in the `R`-source and
covariant in the `S`-coefficient. Its `S`-action is pointwise: `(s·f)(m)=s·f(m)`. The
semimodule functors use a semiring `R` and a commutative semiring `S`; the module functors use
a ring `R` and a commutative ring `S`.

When both scalar rings are commutative and `U` is finite projective over `S`, the map `(f ⊗
u)(m)=f(m) ⊗ u` gives an equivalence `Hom_σ(M,N) ⊗_S U ≅ Hom_σ(M,N ⊗_S U)`, natural in the
arbitrary source `M` and coefficient `N`. Scalar and carrier universes are independent. A
separate coefficient-linear equivalence identifies semilinear maps with morphisms into scalar
restriction when the two carriers have the same universe.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped TensorProduct

universe r s vM vN vU h

namespace TensorProduct

/-- Let `R : Type r` and `S : Type s` be commutative semirings, `σ : R →+* S`, `M` an
`R`-semimodule, and `N,U` independently sized `S`-semimodules. Assume `U` is finite and
projective over `S`. The linear equivalence `(M →ₛₗ[σ] N) ⊗[S] U ≃ₗ[S] (M →ₛₗ[σ] N ⊗[S] U)`
has forward map `rTensorHomToHomRTensor σ M N U`, sending `f ⊗ u` to `m ↦ f(m) ⊗ u`. The
source `M` is arbitrary. -/
def semilinearHomFiniteFactorEquiv
    {R : Type r} {S : Type s} [CommSemiring R] [CommSemiring S] (σ : R →+* S)
    (M : Type vM) [AddCommMonoid M] [Module R M]
    (N : Type vN) [AddCommMonoid N] [Module S N]
    (U : Type vU) [AddCommMonoid U] [Module S U]
    [Module.Finite S U] [Module.Projective S U] :
    (M →ₛₗ[σ] N) ⊗[S] U ≃ₗ[S] (M →ₛₗ[σ] N ⊗[S] U) :=
  LinearEquiv.ofBijective (rTensorHomToHomRTensor σ M N U)
    (rTensorHomToHomRTensor_bijective_of_finite_projective σ M N U)

end TensorProduct

namespace SemimoduleCat

section Tensor

variable {S : Type s} [CommSemiring S]

/-- For a commutative semiring `S : Type s` and `U : SemimoduleCat.{vU} S`, the functor
`SemimoduleCat.{vN} S → SemimoduleCat.{max vN vU} S` sends `N` to `N ⊗[S] U` and a linear map
`f` to `f.rTensor U`. The coefficient and tensor-factor carrier universes are independent. -/
def tensorRightFunctor (U : SemimoduleCat.{vU} S) :
    SemimoduleCat.{vN} S ⥤ SemimoduleCat.{max vN vU} S where
  obj N := of S (N ⊗[S] U)
  map f := ofHom (f.hom.rTensor U)
  map_id N := by
    apply SemimoduleCat.hom_ext
    apply TensorProduct.ext'
    intro n u
    rfl
  map_comp f g := by
    apply SemimoduleCat.hom_ext
    apply TensorProduct.ext'
    intro n u
    rfl

instance tensorRightFunctor_preservesZero (U : SemimoduleCat.{vU} S) :
    (tensorRightFunctor U : SemimoduleCat.{vN} S ⥤
      SemimoduleCat.{max vN vU} S).PreservesZeroMorphisms := by
  constructor
  intro X Y
  apply SemimoduleCat.hom_ext
  apply TensorProduct.ext'
  intro x u
  change (0 : Y) ⊗ₜ[S] u = 0
  simp only [TensorProduct.zero_tmul]

@[simp]
theorem tensorRightFunctor_map_tmul (U : SemimoduleCat.{vU} S)
    {N N' : SemimoduleCat.{vN} S} (f : N ⟶ N') (n : N) (u : U) :
    ((tensorRightFunctor U).map f).hom (n ⊗ₜ[S] u) = f.hom n ⊗ₜ[S] u := rfl

end Tensor

section Lift

variable (R : Type r) [Semiring R]

/-- For a semiring `R : Type ringU`, the functor `SemimoduleCat.{carrierU} R → SemimoduleCat.{max
liftU carrierU} R` sends `M` to `ULift.{liftU} M`, with the transported `R`-module structure.
It sends a linear map `f` to the map `ULift.up m ↦ ULift.up (f m)`. -/
def uliftFunctor.{liftU, ringU, carrierU} (R : Type ringU) [Semiring R] :
    SemimoduleCat.{carrierU} R ⥤ SemimoduleCat.{max liftU carrierU} R where
  obj M := of R (ULift.{liftU} M)
  map f := ofHom (ULift.moduleEquiv.symm.toLinearMap.comp
    (f.hom.comp ULift.moduleEquiv.toLinearMap))
  map_id M := by
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  map_comp f g := by
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

instance uliftFunctor_preservesZero : (uliftFunctor.{h, r, vM} R).PreservesZeroMorphisms := by
  constructor
  intro X Y
  apply SemimoduleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end Lift

section Hom

variable {R : Type r} {S : Type s} [Semiring R] [CommSemiring S] (σ : R →+* S)

/-- Let `R : Type r` be a semiring, `S : Type s` a commutative semiring, `σ : R →+* S`, and `M :
SemimoduleCat.{vM} R`. The functor `SemimoduleCat.{vN} S → SemimoduleCat.{max vM vN} S` sends
`N` to `M →ₛₗ[σ] N`, with pointwise `S`-action. Its map on `f : N → N'` is postcomposition `a
↦ f ∘ a`. -/
def semilinearHomCoeffFunctor (σ : R →+* S) (M : SemimoduleCat.{vM} R) :
    SemimoduleCat.{vN} S ⥤ SemimoduleCat.{max vM vN} S where
  obj N := of S (M →ₛₗ[σ] N)
  map {N N'} f := ofHom
    (show (M →ₛₗ[σ] N) →ₗ[S] (M →ₛₗ[σ] N') from
      { toFun := fun g => f.hom.comp (σ₁₂ := σ) (σ₁₃ := σ) g
        map_add' := fun g h => by
          apply LinearMap.ext
          intro x
          exact f.hom.map_add (g x) (h x)
        map_smul' := fun s g => by
          apply LinearMap.ext
          intro x
          exact f.hom.map_smul s (g x) })
  map_id N := by
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    rfl
  map_comp f g := by
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro k
    apply LinearMap.ext
    intro x
    rfl

attribute [local implicit_reducible] semilinearHomCoeffFunctor

instance semilinearHomCoeffFunctor_preservesZero (M : SemimoduleCat.{vM} R) :
    (semilinearHomCoeffFunctor σ M : SemimoduleCat.{vN} S ⥤
      SemimoduleCat.{max vM vN} S).PreservesZeroMorphisms := by
  constructor
  intro X Y
  apply SemimoduleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro x
  rfl

/-- Let `R : Type r` be a semiring, `S : Type s` a commutative semiring, and `σ : R →+* S`. The
bifunctor `(SemimoduleCat.{vM} R)ᵒᵖ ⥤ SemimoduleCat.{vN} S ⥤ SemimoduleCat.{max vM vN} S` has
value `M →ₛₗ[σ] N`. A source map `a : M' → M` acts by precomposition, and a coefficient map `b
: N → N'` acts by postcomposition. -/
def semilinearHomFunctor (σ : R →+* S) : (SemimoduleCat.{vM} R)ᵒᵖ ⥤
    SemimoduleCat.{vN} S ⥤ SemimoduleCat.{max vM vN} S where
  obj M := semilinearHomCoeffFunctor σ M.unop
  map {M M'} k :=
    { app N := ofHom (LinearMap.lcompₛₗ S N σ k.unop.hom)
      naturality N N' f := by
        apply SemimoduleCat.hom_ext
        apply LinearMap.ext
        intro g
        apply LinearMap.ext
        intro x
        rfl }
  map_id M := by
    apply NatTrans.ext
    funext N
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext N
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro k
    apply LinearMap.ext
    intro x
    rfl

attribute [local implicit_reducible] semilinearHomFunctor

/-- Let `R : Type r` be a semiring, `S : Type s` a commutative semiring, `σ : R →+* S`, and `N :
SemimoduleCat.{vN} S`. The functor `(SemimoduleCat.{vM} R)ᵒᵖ → SemimoduleCat.{max vM vN} S`
sends `M` to `M →ₛₗ[σ] N`; a linear map `a : M' → M` induces `f ↦ f ∘ a`. -/
def semilinearHomSourceFunctor (σ : R →+* S) (N : SemimoduleCat.{vN} S) :
    (SemimoduleCat.{vM} R)ᵒᵖ ⥤ SemimoduleCat.{max vM vN} S :=
  semilinearHomFunctor σ ⋙
    (evaluation (SemimoduleCat.{vN} S) (SemimoduleCat.{max vM vN} S)).obj N

attribute [local implicit_reducible] semilinearHomSourceFunctor

instance semilinearHomSourceFunctor_preservesZero (N : SemimoduleCat.{vN} S) :
    (semilinearHomSourceFunctor σ N : (SemimoduleCat.{vM} R)ᵒᵖ ⥤
      SemimoduleCat.{max vM vN} S).PreservesZeroMorphisms := by
  constructor
  intro X Y
  apply SemimoduleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro x
  exact f.map_zero

@[simp]
theorem semilinearHomCoeffFunctor_map_apply (M : SemimoduleCat.{vM} R)
    {N N' : SemimoduleCat.{vN} S} (g : N ⟶ N') (f : M →ₛₗ[σ] N) (x : M) :
    ((semilinearHomCoeffFunctor σ M).map g).hom f x = g.hom (f x) := rfl

@[simp]
theorem semilinearHomSourceFunctor_map_apply (N : SemimoduleCat.{vN} S)
    {M M' : SemimoduleCat.{vM} R} (k : M' ⟶ M) (f : M →ₛₗ[σ] N) (x : M') :
    ((semilinearHomSourceFunctor σ N).map k.op).hom f x = f (k.hom x) := rfl

end Hom

section FiniteFactor

variable {R : Type r} {S : Type s} [CommSemiring R] [CommSemiring S] (σ : R →+* S)

/-- Let `R,S` be commutative semirings, `σ : R →+* S`, `M : SemimoduleCat.{vM} R`, and `U :
SemimoduleCat.{vU} S` finite projective over `S`. The natural isomorphism in `N :
SemimoduleCat.{vN} S` identifies `Hom_σ(M,N) ⊗_S U` with `Hom_σ(M,N ⊗_S U)`. Its component
sends `f ⊗ u` to `m ↦ f(m) ⊗ u`, and its naturality maps are coefficient postcomposition and
tensoring on the right. -/
def semilinearHomCoeffTensorIso (M : SemimoduleCat.{vM} R) (U : SemimoduleCat.{vU} S)
    [Module.Finite S U] [Module.Projective S U] :
    (semilinearHomCoeffFunctor σ M : SemimoduleCat.{vN} S ⥤
        SemimoduleCat.{max vM vN} S) ⋙ tensorRightFunctor U ≅
      (tensorRightFunctor U : SemimoduleCat.{vN} S ⥤
        SemimoduleCat.{max vN vU} S) ⋙ semilinearHomCoeffFunctor σ M :=
  NatIso.ofComponents
    (fun N => (TensorProduct.semilinearHomFiniteFactorEquiv σ M N U).toModuleIsoₛ)
    (fun {N N'} g => by
      apply SemimoduleCat.hom_ext
      change
        (TensorProduct.rTensorHomToHomRTensor σ M N' U).comp
            ((LinearMap.llcomp (σ₁₂ := σ) (σ₁₃ := σ) S M N N' g.hom).rTensor U) =
          (LinearMap.llcomp (σ₁₂ := σ) (σ₁₃ := σ)
             S M (N ⊗[S] U) (N' ⊗[S] U) (g.hom.rTensor U)).comp
            (TensorProduct.rTensorHomToHomRTensor σ M N U)
      exact TensorProduct.rTensorHomToHomRTensor_postcomp σ M N (U := U) g.hom)

/-- Let `R,S` be commutative semirings, `σ : R →+* S`, `N : SemimoduleCat.{vN} S`, and `U :
SemimoduleCat.{vU} S` finite projective over `S`. The natural isomorphism on
`(SemimoduleCat.{vM} R)ᵒᵖ` identifies `Hom_σ(M,N) ⊗_S U` with `Hom_σ(M,N ⊗_S U)` for arbitrary
`M`. Its component is `f ⊗ u ↦ (m ↦ f(m) ⊗ u)` and it commutes with source precomposition. -/
def semilinearHomSourceTensorIso (N : SemimoduleCat.{vN} S) (U : SemimoduleCat.{vU} S)
    [Module.Finite S U] [Module.Projective S U] :
    (semilinearHomSourceFunctor σ N : (SemimoduleCat.{vM} R)ᵒᵖ ⥤
        SemimoduleCat.{max vM vN} S) ⋙ tensorRightFunctor U ≅
      (semilinearHomSourceFunctor σ (of S (N ⊗[S] U)) :
        (SemimoduleCat.{vM} R)ᵒᵖ ⥤ SemimoduleCat.{max vM vN vU} S) :=
  NatIso.ofComponents
    (fun M => (TensorProduct.semilinearHomFiniteFactorEquiv σ M.unop N U).toModuleIsoₛ)
    (fun {M M'} k => by
      apply SemimoduleCat.hom_ext
      change
        (TensorProduct.rTensorHomToHomRTensor σ M'.unop N U).comp
            ((LinearMap.lcompₛₗ S N σ k.unop.hom).rTensor U) =
          (LinearMap.lcompₛₗ S (N ⊗[S] U) σ k.unop.hom).comp
            (TensorProduct.rTensorHomToHomRTensor σ M.unop N U)
      exact TensorProduct.rTensorHomToHomRTensor_precomp σ M.unop N (U := U) k.unop.hom)

attribute [local implicit_reducible] semilinearHomCoeffTensorIso semilinearHomSourceTensorIso

@[simp]
theorem semilinearHomCoeffTensorIso_hom_apply (M : SemimoduleCat.{vM} R)
    (N : SemimoduleCat.{vN} S) (U : SemimoduleCat.{vU} S)
    [Module.Finite S U] [Module.Projective S U] (f : M →ₛₗ[σ] N) (u : U) (x : M) :
    ((semilinearHomCoeffTensorIso σ M U).hom.app N).hom (f ⊗ₜ[S] u) x =
      f x ⊗ₜ[S] u := rfl

@[simp]
theorem semilinearHomSourceTensorIso_hom_apply (M : SemimoduleCat.{vM} R)
    (N : SemimoduleCat.{vN} S) (U : SemimoduleCat.{vU} S)
    [Module.Finite S U] [Module.Projective S U] (f : M →ₛₗ[σ] N) (u : U) (x : M) :
    ((semilinearHomSourceTensorIso σ N U).hom.app (op M)).hom (f ⊗ₜ[S] u) x =
      f x ⊗ₜ[S] u := rfl

end FiniteFactor

end SemimoduleCat

namespace ModuleCat

section Hom

variable {R : Type r} {S : Type s} [Ring R] [CommRing S] (σ : R →+* S)

/-- Let `R : Type r` be a ring, `S : Type s` a commutative ring, `σ : R →+* S`, `M :
ModuleCat.{vM} R`, and `N : ModuleCat.{vM} S`. The `S`-linear equivalence `(M →ₛₗ[σ] N) ≃ₗ[S]
(M ⟶ (restrictScalars σ).obj N)` preserves the underlying function in both directions. The
coefficient `S`-action on the restricted Hom space uses the commuting `R`- and `S`-actions on
`N` induced by `σ`. -/
def semilinearMapLinearEquiv (M : ModuleCat.{vM} R) (N : ModuleCat.{vM} S) :
    letI : SMulCommClass R S ((restrictScalars σ).obj N) := sMulCommClass_mk σ N
    (M →ₛₗ[σ] N) ≃ₗ[S] (M ⟶ (restrictScalars σ).obj N) := by
  letI : SMulCommClass R S ((restrictScalars σ).obj N) := sMulCommClass_mk σ N
  refine { semilinearMapAddEquiv σ M N with map_smul' := ?_ }
  intro s f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

@[simp]
theorem semilinearMapLinearEquiv_apply (M : ModuleCat.{vM} R) (N : ModuleCat.{vM} S)
    (f : M →ₛₗ[σ] N) (x : M) : (semilinearMapLinearEquiv σ M N f).hom x = f x := rfl

@[simp]
theorem semilinearMapLinearEquiv_symm_apply (M : ModuleCat.{vM} R) (N : ModuleCat.{vM} S)
    (f : M ⟶ (restrictScalars σ).obj N) (x : M) :
    (semilinearMapLinearEquiv σ M N).symm f x = f.hom x := rfl

/-- Let `R : Type r` be a ring, `S : Type s` a commutative ring, `σ : R →+* S`, and `M :
ModuleCat.{vM} R`. The functor `ModuleCat.{vN} S → ModuleCat.{max vM vN} S` sends `N` to `M
→ₛₗ[σ] N`, with pointwise scalar action. An `S`-linear map `b : N → N'` induces
postcomposition `f ↦ b ∘ f`. -/
def semilinearHomCoeffFunctor (σ : R →+* S) (M : ModuleCat.{vM} R) :
    ModuleCat.{vN} S ⥤ ModuleCat.{max vM vN} S where
  obj N := of S (M →ₛₗ[σ] N)
  map {N N'} f := ofHom
    (show (M →ₛₗ[σ] N) →ₗ[S] (M →ₛₗ[σ] N') from
      { toFun := fun g => f.hom.comp (σ₁₂ := σ) (σ₁₃ := σ) g
        map_add' := fun g h => by
          apply LinearMap.ext
          intro x
          exact f.hom.map_add (g x) (h x)
        map_smul' := fun s g => by
          apply LinearMap.ext
          intro x
          exact f.hom.map_smul s (g x) })
  map_id N := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro k
    apply LinearMap.ext
    intro x
    rfl

attribute [local implicit_reducible] semilinearHomCoeffFunctor

instance semilinearHomCoeffFunctor_additive (M : ModuleCat.{vM} R) :
    (semilinearHomCoeffFunctor σ M : ModuleCat.{vN} S ⥤
      ModuleCat.{max vM vN} S).Additive where
  map_add {X Y f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro k
    apply LinearMap.ext
    intro x
    rfl

instance semilinearHomCoeffFunctor_linear (M : ModuleCat.{vM} R) :
    Functor.Linear S (semilinearHomCoeffFunctor σ M : ModuleCat.{vN} S ⥤
      ModuleCat.{max vM vN} S) where
  map_smul f s := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro k
    apply LinearMap.ext
    intro x
    rfl

/-- Let `R : Type r` be a ring, `S : Type s` a commutative ring, and `σ : R →+* S`. The bifunctor
`(ModuleCat.{vM} R)ᵒᵖ ⥤ ModuleCat.{vN} S ⥤ ModuleCat.{max vM vN} S` has value `M →ₛₗ[σ] N`.
For `a : M' → M` and `b : N → N'`, the induced map is `f ↦ b ∘ f ∘ a`; the source and
coefficient carrier universes are independent. -/
def semilinearHomFunctor (σ : R →+* S) : (ModuleCat.{vM} R)ᵒᵖ ⥤
    ModuleCat.{vN} S ⥤ ModuleCat.{max vM vN} S where
  obj M := semilinearHomCoeffFunctor σ M.unop
  map {M M'} k :=
    { app N := ofHom (LinearMap.lcompₛₗ S N σ k.unop.hom)
      naturality N N' f := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro g
        apply LinearMap.ext
        intro x
        rfl }
  map_id M := by
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro k
    apply LinearMap.ext
    intro x
    rfl

attribute [local implicit_reducible] semilinearHomFunctor

/-- Let `R : Type r` be a ring, `S : Type s` a commutative ring, `σ : R →+* S`, and `N :
ModuleCat.{vN} S`. The functor `(ModuleCat.{vM} R)ᵒᵖ → ModuleCat.{max vM vN} S` sends an
arbitrary `R`-module `M` to `M →ₛₗ[σ] N`. Its map on `a : M' → M` is precomposition `f ↦ f ∘
a`. -/
def semilinearHomSourceFunctor (σ : R →+* S) (N : ModuleCat.{vN} S) :
    (ModuleCat.{vM} R)ᵒᵖ ⥤ ModuleCat.{max vM vN} S :=
  semilinearHomFunctor σ ⋙
    (evaluation (ModuleCat.{vN} S) (ModuleCat.{max vM vN} S)).obj N

attribute [local implicit_reducible] semilinearHomSourceFunctor

instance semilinearHomSourceFunctor_additive (N : ModuleCat.{vN} S) :
    (semilinearHomSourceFunctor σ N : (ModuleCat.{vM} R)ᵒᵖ ⥤
      ModuleCat.{max vM vN} S).Additive where
  map_add {X Y f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro k
    apply LinearMap.ext
    intro x
    exact k.map_add _ _

@[simp]
theorem semilinearHomCoeffFunctor_map_apply (M : ModuleCat.{vM} R)
    {N N' : ModuleCat.{vN} S} (g : N ⟶ N') (f : M →ₛₗ[σ] N) (x : M) :
    ((semilinearHomCoeffFunctor σ M).map g).hom f x = g.hom (f x) := rfl

@[simp]
theorem semilinearHomSourceFunctor_map_apply (N : ModuleCat.{vN} S)
    {M M' : ModuleCat.{vM} R} (k : M' ⟶ M) (f : M →ₛₗ[σ] N) (x : M') :
    ((semilinearHomSourceFunctor σ N).map k.op).hom f x = f (k.hom x) := rfl

end Hom

section FiniteFactor

variable {R : Type r} {S : Type s} [CommRing R] [CommRing S] (σ : R →+* S)

/-- Let `R,S` be commutative rings, `σ : R →+* S`, `M : ModuleCat.{vM} R`, and `U : ModuleCat.{vU}
S` finite projective over `S`. The natural isomorphism in `N : ModuleCat.{vN} S` identifies
`Hom_σ(M,N) ⊗_S U` with `Hom_σ(M,N ⊗_S U)`. Each component sends `f ⊗ u` to `m ↦ f(m) ⊗ u`,
and the naturality square uses coefficient postcomposition and right tensoring. -/
def semilinearHomCoeffTensorIso (M : ModuleCat.{vM} R) (U : ModuleCat.{vU} S)
    [Module.Finite S U] [Module.Projective S U] :
    (semilinearHomCoeffFunctor σ M : ModuleCat.{vN} S ⥤
        ModuleCat.{max vM vN} S) ⋙
        (tensorBifunctorAt.{s, max vM vN, vU} S).flip.obj U ≅
      (tensorBifunctorAt.{s, vN, vU} S).flip.obj U ⋙ semilinearHomCoeffFunctor σ M :=
  NatIso.ofComponents
    (fun N => (TensorProduct.semilinearHomFiniteFactorEquiv σ M N U).toModuleIso)
    (fun {N N'} g => by
      apply ModuleCat.hom_ext
      change
        (TensorProduct.rTensorHomToHomRTensor σ M N' U).comp
            ((LinearMap.llcomp (σ₁₂ := σ) (σ₁₃ := σ) S M N N' g.hom).rTensor U) =
          (LinearMap.llcomp (σ₁₂ := σ) (σ₁₃ := σ)
             S M (N ⊗[S] U) (N' ⊗[S] U) (g.hom.rTensor U)).comp
            (TensorProduct.rTensorHomToHomRTensor σ M N U)
      exact TensorProduct.rTensorHomToHomRTensor_postcomp σ M N (U := U) g.hom)

/-- Let `R,S` be commutative rings, `σ : R →+* S`, `N : ModuleCat.{vN} S`, and `U : ModuleCat.{vU}
S` finite projective over `S`. On `(ModuleCat.{vM} R)ᵒᵖ`, there is a natural isomorphism
`Hom_σ(-,N) ⊗_S U ≅ Hom_σ(-,N ⊗_S U)`. Its component sends `f ⊗ u` to `m ↦ f(m) ⊗ u` and
commutes with precomposition by arbitrary source morphisms. All three carrier universes are
independent. -/
def semilinearHomSourceTensorIso (N : ModuleCat.{vN} S) (U : ModuleCat.{vU} S)
    [Module.Finite S U] [Module.Projective S U] :
    (semilinearHomSourceFunctor σ N : (ModuleCat.{vM} R)ᵒᵖ ⥤
        ModuleCat.{max vM vN} S) ⋙
        (tensorBifunctorAt.{s, max vM vN, vU} S).flip.obj U ≅
      (semilinearHomSourceFunctor σ (tensorObjAt S N U) :
        (ModuleCat.{vM} R)ᵒᵖ ⥤ ModuleCat.{max vM vN vU} S) :=
  NatIso.ofComponents
    (fun M => (TensorProduct.semilinearHomFiniteFactorEquiv σ M.unop N U).toModuleIso)
    (fun {M M'} k => by
      apply ModuleCat.hom_ext
      change
        (TensorProduct.rTensorHomToHomRTensor σ M'.unop N U).comp
            ((LinearMap.lcompₛₗ S N σ k.unop.hom).rTensor U) =
          (LinearMap.lcompₛₗ S (N ⊗[S] U) σ k.unop.hom).comp
            (TensorProduct.rTensorHomToHomRTensor σ M.unop N U)
      exact TensorProduct.rTensorHomToHomRTensor_precomp σ M.unop N (U := U) k.unop.hom)

attribute [local implicit_reducible] semilinearHomCoeffTensorIso semilinearHomSourceTensorIso

@[simp]
theorem semilinearHomCoeffTensorIso_hom_apply (M : ModuleCat.{vM} R)
    (N : ModuleCat.{vN} S) (U : ModuleCat.{vU} S)
    [Module.Finite S U] [Module.Projective S U] (f : M →ₛₗ[σ] N) (u : U) (x : M) :
    ((semilinearHomCoeffTensorIso σ M U).hom.app N).hom (f ⊗ₜ[S] u) x =
      f x ⊗ₜ[S] u := rfl

@[simp]
theorem semilinearHomSourceTensorIso_hom_apply (M : ModuleCat.{vM} R)
    (N : ModuleCat.{vN} S) (U : ModuleCat.{vU} S)
    [Module.Finite S U] [Module.Projective S U] (f : M →ₛₗ[σ] N) (u : U) (x : M) :
    ((semilinearHomSourceTensorIso σ N U).hom.app (op M)).hom (f ⊗ₜ[S] u) x =
      f x ⊗ₜ[S] u := rfl

end FiniteFactor

end ModuleCat
