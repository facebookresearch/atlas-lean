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

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Finiteness.Projective
public import MathlibExt.LinearAlgebra.LinearMap.RetractComparison

/-!
# Semilinear Hom–tensor comparison with a finite projective tensor factor

For a homomorphism `σ : R →+* S`, the source of the semilinear maps is an
arbitrary `R`-module. Finite product coordinates identify the comparison for
a finite free `S`-module tensor factor. A finite free retraction of a finite
projective `S`-module then proves bijectivity of the same comparison.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open scoped TensorProduct

namespace TensorProduct

universe uR uS uP uP' uN uN' uU uV

attribute [local ext high] TensorProduct.ext

section Semilinear

variable {R : Type uR} {S : Type uS} [CommSemiring R] [CommSemiring S]
  (σ : R →+* S) (P : Type uP) [AddCommMonoid P] [Module R P]
  (N : Type uN) [AddCommMonoid N] [Module S N]

/-- The semilinear comparison commutes with a map of tensor factors. -/
theorem rTensorHomToHomRTensor_naturality
    {U : Type uU} {V : Type uV}
    [AddCommMonoid U] [Module S U] [AddCommMonoid V] [Module S V]
    (g : U →ₗ[S] V) :
    (rTensorHomToHomRTensor σ P N V).comp (g.lTensor (P →ₛₗ[σ] N)) =
      (LinearMap.llcomp S P (N ⊗[S] U) (N ⊗[S] V) (g.lTensor N)).comp
        (rTensorHomToHomRTensor σ P N U) := by
  apply TensorProduct.ext'
  intro f u
  apply LinearMap.ext
  intro p
  rfl

/-- The semilinear comparison is contravariantly natural in its source. -/
theorem rTensorHomToHomRTensor_precomp
    {P' : Type uP'} [AddCommMonoid P'] [Module R P']
    {U : Type uU} [AddCommMonoid U] [Module S U] (k : P' →ₗ[R] P) :
    (rTensorHomToHomRTensor σ P' N U).comp
        ((LinearMap.lcompₛₗ S N σ k).rTensor U) =
      (LinearMap.lcompₛₗ S (N ⊗[S] U) σ k).comp
        (rTensorHomToHomRTensor σ P N U) := by
  apply TensorProduct.ext'
  intro h u
  apply LinearMap.ext
  intro p
  rfl

/-- The semilinear comparison is covariantly natural in its coefficient module. -/
theorem rTensorHomToHomRTensor_postcomp
    {N' : Type uN'} [AddCommMonoid N'] [Module S N']
    {U : Type uU} [AddCommMonoid U] [Module S U] (f : N →ₗ[S] N') :
    (rTensorHomToHomRTensor σ P N' U).comp
        ((LinearMap.llcomp S P N N' f).rTensor U) =
      (LinearMap.llcomp S P (N ⊗[S] U) (N' ⊗[S] U) (f.rTensor U)).comp
        (rTensorHomToHomRTensor σ P N U) := by
  apply TensorProduct.ext'
  intro h u
  apply LinearMap.ext
  intro p
  rfl

/-- Source precomposition, coefficient postcomposition and a tensor-factor map
commute simultaneously with the native semilinear comparison. -/
theorem rTensorHomToHomRTensor_map_precomp
    {P' : Type uP'} [AddCommMonoid P'] [Module R P']
    {N' : Type uN'} [AddCommMonoid N'] [Module S N']
    {U : Type uU} [AddCommMonoid U] [Module S U]
    {V : Type uV} [AddCommMonoid V] [Module S V]
    (k : P' →ₗ[R] P) (f : N →ₗ[S] N') (g : U →ₗ[S] V) :
    (rTensorHomToHomRTensor σ P' N' V).comp
        (TensorProduct.map
          ((LinearMap.llcomp S P' N N' f).comp (LinearMap.lcompₛₗ S N σ k)) g) =
      (LinearMap.llcomp S P' (N ⊗[S] U) (N' ⊗[S] V) (TensorProduct.map f g)).comp
        ((LinearMap.lcompₛₗ S (N ⊗[S] U) σ k).comp
          (rTensorHomToHomRTensor σ P N U)) := by
  apply TensorProduct.ext'
  intro h u
  apply LinearMap.ext
  intro p
  rfl

/-- Coordinate evaluation identifies a semilinear map into a product with
a product of semilinear maps. -/
private def homTensorSemilinearPi (ι : Type*) :
    (P →ₛₗ[σ] (ι → N)) ≃ₗ[S] (ι → (P →ₛₗ[σ] N)) where
  toFun f i := (LinearMap.proj i).comp f
  invFun f :=
    { toFun := fun p i => f i p
      map_add' := fun p q => funext fun i => (f i).map_add p q
      map_smul' := fun r p => funext fun i => (f i).map_smulₛₗ r p }
  map_add' f g := by
    funext i
    apply LinearMap.ext
    intro p
    rfl
  map_smul' s f := by
    funext i
    apply LinearMap.ext
    intro p
    rfl
  left_inv f := by
    apply LinearMap.ext
    intro p
    funext i
    rfl
  right_inv f := by
    funext i
    apply LinearMap.ext
    intro p
    rfl

private theorem homTensorFiniteFree_semilinear_bijective (n : ℕ) :
    Function.Bijective (rTensorHomToHomRTensor σ P N (Fin n → S)) := by
  let e : (P →ₛₗ[σ] N) ⊗[S] (Fin n → S) ≃ₗ[S] (Fin n → (P →ₛₗ[σ] N)) :=
    TensorProduct.piScalarRight S S (P →ₛₗ[σ] N) (Fin n)
  let t : (P →ₛₗ[σ] N ⊗[S] (Fin n → S)) ≃ₗ[S] (Fin n → (P →ₛₗ[σ] N)) :=
    (LinearEquiv.refl R P).arrowCongr (TensorProduct.piScalarRight S S N (Fin n)) ≪≫ₗ
      homTensorSemilinearPi σ P N (Fin n)
  have he : t.toLinearMap.comp (rTensorHomToHomRTensor σ P N (Fin n → S)) =
      e.toLinearMap := by
    apply TensorProduct.ext'
    intro f u
    funext i
    apply LinearMap.ext
    intro p
    change (TensorProduct.piScalarRight S S N (Fin n)
        ((rTensorHomToHomRTensor σ P N (Fin n → S) (f ⊗ₜ[S] u)) p)) i =
      (TensorProduct.piScalarRight S S (P →ₛₗ[σ] N) (Fin n) (f ⊗ₜ[S] u)) i p
    rw [rTensorHomToHomRTensor_apply]
    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      LinearMap.smul_apply]
  have hb : Function.Bijective
      (fun x => t (rTensorHomToHomRTensor σ P N (Fin n → S) x)) := by
    change Function.Bijective (t.toLinearMap.comp
      (rTensorHomToHomRTensor σ P N (Fin n → S)))
    rw [he]
    exact e.bijective
  constructor
  · intro x y h
    exact hb.injective (congrArg t h)
  · intro y
    obtain ⟨x, hx⟩ := hb.surjective (t y)
    exact ⟨x, t.injective hx⟩

/-- A finite projective tensor factor over `S` makes the native semilinear
Hom–tensor comparison bijective. No `S`-module structure or finiteness
hypothesis is required on the `R`-module `P`. -/
theorem rTensorHomToHomRTensor_bijective_of_finite_projective
    (U : Type uU) [AddCommMonoid U] [Module S U]
    [Module.Finite S U] [Module.Projective S U] :
    Function.Bijective (rTensorHomToHomRTensor σ P N U) := by
  obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective S U
  let dF := f.lTensor (P →ₛₗ[σ] N)
  let dG := g.lTensor (P →ₛₗ[σ] N)
  let cF : (P →ₛₗ[σ] N ⊗[S] (Fin n → S)) →ₗ[S] (P →ₛₗ[σ] N ⊗[S] U) :=
    LinearMap.llcomp S P _ _ (f.lTensor N)
  let cG : (P →ₛₗ[σ] N ⊗[S] U) →ₗ[S] (P →ₛₗ[σ] N ⊗[S] (Fin n → S)) :=
    LinearMap.llcomp S P _ _ (g.lTensor N)
  have hd : dF.comp dG = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, hfg, LinearMap.lTensor_id]
  have hfgN : (f.lTensor N).comp (g.lTensor N) = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, hfg, LinearMap.lTensor_id]
  have hc : cF.comp cG = LinearMap.id := by
    ext h p
    change (f.lTensor N) ((g.lTensor N) (h p)) = h p
    exact LinearMap.congr_fun hfgN (h p)
  have hFree := homTensorFiniteFree_semilinear_bijective σ P N n
  have hNatF := rTensorHomToHomRTensor_naturality σ P N f
  have hNatG := rTensorHomToHomRTensor_naturality σ P N g
  exact LinearMap.comparison_bijective_of_retract
    (rTensorHomToHomRTensor σ P N U)
    (rTensorHomToHomRTensor σ P N (Fin n → S))
    dG dF cG cF hd hc hNatG hNatF hFree

/-- The inverse of the finite projective comparison commutes with the same
source, coefficient and tensor-factor maps. Both inverses are constructed
from the finite projective tensor factors. -/
theorem rTensorHomToHomRTensor_symm_map_precomp
    {P' : Type uP'} [AddCommMonoid P'] [Module R P']
    {N' : Type uN'} [AddCommMonoid N'] [Module S N']
    {U : Type uU} [AddCommMonoid U] [Module S U]
    {V : Type uV} [AddCommMonoid V] [Module S V]
    [Module.Finite S U] [Module.Projective S U]
    [Module.Finite S V] [Module.Projective S V]
    (k : P' →ₗ[R] P) (f : N →ₗ[S] N') (g : U →ₗ[S] V) :
    let e := LinearEquiv.ofBijective (rTensorHomToHomRTensor σ P N U)
      (rTensorHomToHomRTensor_bijective_of_finite_projective σ P N U)
    let e' := LinearEquiv.ofBijective (rTensorHomToHomRTensor σ P' N' V)
      (rTensorHomToHomRTensor_bijective_of_finite_projective σ P' N' V)
    e'.symm.toLinearMap.comp
        ((LinearMap.llcomp S P' (N ⊗[S] U) (N' ⊗[S] V) (TensorProduct.map f g)).comp
          (LinearMap.lcompₛₗ S (N ⊗[S] U) σ k)) =
      (TensorProduct.map
        ((LinearMap.llcomp S P' N N' f).comp (LinearMap.lcompₛₗ S N σ k)) g).comp
        e.symm.toLinearMap := by
  let e := LinearEquiv.ofBijective (rTensorHomToHomRTensor σ P N U)
    (rTensorHomToHomRTensor_bijective_of_finite_projective σ P N U)
  let e' := LinearEquiv.ofBijective (rTensorHomToHomRTensor σ P' N' V)
    (rTensorHomToHomRTensor_bijective_of_finite_projective σ P' N' V)
  let a := TensorProduct.map
    ((LinearMap.llcomp S P' N N' f).comp (LinearMap.lcompₛₗ S N σ k)) g
  let b :=
    (LinearMap.llcomp S P' (N ⊗[S] U) (N' ⊗[S] V) (TensorProduct.map f g)).comp
      (LinearMap.lcompₛₗ S (N ⊗[S] U) σ k)
  change e'.symm.toLinearMap.comp b = a.comp e.symm.toLinearMap
  have hn : e'.toLinearMap.comp a = b.comp e.toLinearMap :=
    rTensorHomToHomRTensor_map_precomp σ P N k f g
  apply LinearMap.ext
  intro y
  apply e'.injective
  change e' (e'.symm (b y)) = e' (a (e.symm y))
  rw [e'.apply_symm_apply]
  calc
    b y = b (e (e.symm y)) := by rw [e.apply_symm_apply]
    _ = e' (a (e.symm y)) := (LinearMap.congr_fun hn (e.symm y)).symm

/-- Swapping the domain tensor factors and the codomain tensor factors
identifies the native left and right semilinear comparisons. -/
theorem lTensorHomToHomLTensor_eq_comm_rTensorHom
    (U : Type uU) [AddCommMonoid U] [Module S U] :
    lTensorHomToHomLTensor σ P U N =
      ((LinearEquiv.refl R P).arrowCongr (TensorProduct.comm S N U)).toLinearMap.comp
        ((rTensorHomToHomRTensor σ P N U).comp
          (TensorProduct.comm S U (P →ₛₗ[σ] N)).toLinearMap) := by
  apply TensorProduct.ext'
  intro u f
  apply LinearMap.ext
  intro p
  rfl

/-- A finite projective left tensor factor over `S` makes the native left
semilinear Hom–tensor comparison bijective for an arbitrary `R`-module source. -/
theorem lTensorHomToHomLTensor_bijective_of_finite_projective
    (U : Type uU) [AddCommMonoid U] [Module S U]
    [Module.Finite S U] [Module.Projective S U] :
    Function.Bijective (lTensorHomToHomLTensor σ P U N) := by
  let d : U ⊗[S] (P →ₛₗ[σ] N) ≃ₗ[S] (P →ₛₗ[σ] N) ⊗[S] U :=
    TensorProduct.comm S U (P →ₛₗ[σ] N)
  let c : (P →ₛₗ[σ] N ⊗[S] U) ≃ₗ[S] (P →ₛₗ[σ] U ⊗[S] N) :=
    (LinearEquiv.refl R P).arrowCongr (TensorProduct.comm S N U)
  have hc := lTensorHomToHomLTensor_eq_comm_rTensorHom σ P N U
  change lTensorHomToHomLTensor σ P U N =
    c.toLinearMap.comp ((rTensorHomToHomRTensor σ P N U).comp d.toLinearMap) at hc
  rw [hc]
  exact c.bijective.comp
    ((rTensorHomToHomRTensor_bijective_of_finite_projective σ P N U).comp d.bijective)

/-- The equivalence whose forward map is the native left semilinear comparison,
with finite projectivity required only on its left tensor factor. -/
def lTensorHomToHomLTensorEquiv
    (U : Type uU) [AddCommMonoid U] [Module S U]
    [Module.Finite S U] [Module.Projective S U] :
    U ⊗[S] (P →ₛₗ[σ] N) ≃ₗ[S] (P →ₛₗ[σ] U ⊗[S] N) :=
  LinearEquiv.ofBijective (lTensorHomToHomLTensor σ P U N)
    (lTensorHomToHomLTensor_bijective_of_finite_projective σ P N U)

@[simp]
theorem lTensorHomToHomLTensorEquiv_toLinearMap
    (U : Type uU) [AddCommMonoid U] [Module S U]
    [Module.Finite S U] [Module.Projective S U] :
    (lTensorHomToHomLTensorEquiv σ P N U).toLinearMap =
      lTensorHomToHomLTensor σ P U N := rfl

@[simp]
theorem lTensorHomToHomLTensorEquiv_tmul
    (U : Type uU) [AddCommMonoid U] [Module S U]
    [Module.Finite S U] [Module.Projective S U]
    (u : U) (f : P →ₛₗ[σ] N) (p : P) :
    lTensorHomToHomLTensorEquiv σ P N U (u ⊗ₜ[S] f) p = u ⊗ₜ[S] f p := rfl

end Semilinear

variable (R : Type uR) [CommRing R]
  (P : Type uP) [AddCommGroup P] [Module R P]
  (N : Type uN) [AddCommGroup N] [Module R N]

/-- Naturality of the linear comparison in its tensor factor. -/
theorem homTensorCoefficient_naturality
    {U : Type uU} {V : Type uV}
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (g : U →ₗ[R] V) :
    (rTensorHomToHomRTensor (.id R) P N V).comp (g.lTensor (P →ₗ[R] N)) =
      ((g.lTensor N).compRight R).comp (rTensorHomToHomRTensor (.id R) P N U) :=
  rTensorHomToHomRTensor_naturality (.id R) P N g

/-- The linear comparison is bijective for a finite free tensor factor. -/
theorem homTensorFiniteFree_bijective (n : ℕ) :
    Function.Bijective (rTensorHomToHomRTensor (.id R) P N (Fin n → R)) :=
  homTensorFiniteFree_semilinear_bijective (.id R) P N n

/-- The linear comparison is bijective for a finite projective tensor factor,
with arbitrary Hom source. -/
theorem homTensorFiniteFactor_bijective
    (U : Type uU) [AddCommGroup U] [Module R U]
    [Module.Finite R U] [Module.Projective R U] :
    Function.Bijective (rTensorHomToHomRTensor (.id R) P N U) :=
  rTensorHomToHomRTensor_bijective_of_finite_projective (.id R) P N U

/-- The linear equivalence whose forward map is the canonical comparison. -/
def homTensorFiniteFactorEquiv
    (U : Type uU) [AddCommGroup U] [Module R U]
    [Module.Finite R U] [Module.Projective R U] :
    (P →ₗ[R] N) ⊗[R] U ≃ₗ[R] P →ₗ[R] N ⊗[R] U :=
  LinearEquiv.ofBijective (rTensorHomToHomRTensor (.id R) P N U)
    (homTensorFiniteFactor_bijective R P N U)

theorem homTensorFiniteFactorEquiv_toLinearMap
    (U : Type uU) [AddCommGroup U] [Module R U]
    [Module.Finite R U] [Module.Projective R U] :
    (homTensorFiniteFactorEquiv R P N U).toLinearMap =
      rTensorHomToHomRTensor (.id R) P N U := rfl

end TensorProduct
