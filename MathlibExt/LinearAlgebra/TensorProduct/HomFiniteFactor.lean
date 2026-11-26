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
# Hom–tensor comparison with a finite-projective factor

Let R be a commutative ring and P,N R-modules. For an R-module U, define C_U:Hom_R(P,N)⊗_R
U→Hom_R(P,N⊗_R U) by C_U(f⊗u)(p)=f(p)⊗u. If U is finitely generated projective over R, C_U is
an R-linear isomorphism. The Hom source P has no finiteness requirement.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open scoped TensorProduct

namespace TensorProduct

universe uR uP uN uU uV

variable (R : Type uR) [CommRing R]
  (P : Type uP) [AddCommGroup P] [Module R P]
  (N : Type uN) [AddCommGroup N] [Module R N]

attribute [local ext high] TensorProduct.ext

/-- **Naturality of the Hom–tensor comparison in its tensor factor.**

Let R be a commutative ring and P,N R-modules. For an R-module U, define C_U:Hom_R(P,N)⊗_R
U→Hom_R(P,N⊗_R U) by C_U(f⊗u)(p)=f(p)⊗u. For R-modules U,V and R-linear g:U→V,
C_V∘(id⊗g)=postcompose(id_N⊗g)∘C_U.
-/
theorem homTensorCoefficient_naturality
    {U : Type uU} {V : Type uV}
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (g : U →ₗ[R] V) :
    (rTensorHomToHomRTensor (.id R) P N V).comp (g.lTensor (P →ₗ[R] N)) =
      ((g.lTensor N).compRight R).comp (rTensorHomToHomRTensor (.id R) P N U) := by
  apply TensorProduct.ext'
  intro f u
  apply LinearMap.ext
  intro p
  rfl

/-- **Hom–tensor comparison for a finite-free factor.**

Let R be a commutative ring and P,N R-modules. For an R-module U, define C_U:Hom_R(P,N)⊗_R
U→Hom_R(P,N⊗_R U) by C_U(f⊗u)(p)=f(p)⊗u. For n∈ℕ and U=R^(Fin n), C_U is bijective.
-/
theorem homTensorFiniteFree_bijective (n : ℕ) :
    Function.Bijective (rTensorHomToHomRTensor (.id R) P N (Fin n → R)) := by
  let e : (P →ₗ[R] N) ⊗[R] (Fin n → R) ≃ₗ[R] (Fin n → (P →ₗ[R] N)) :=
    TensorProduct.piScalarRight R R (P →ₗ[R] N) (Fin n)
  let t : (P →ₗ[R] N ⊗[R] (Fin n → R)) ≃ₗ[R] (Fin n → (P →ₗ[R] N)) :=
    (LinearEquiv.refl R P).arrowCongr (TensorProduct.piScalarRight R R N (Fin n)) ≪≫ₗ
      (LinearEquiv.linearMapPi R (R := R) (M₂ := P) (φ := fun _ : Fin n => N)).symm
  have he : t.toLinearMap.comp (rTensorHomToHomRTensor (.id R) P N (Fin n → R)) =
      e.toLinearMap := by
    apply TensorProduct.ext'
    intro f u
    funext i
    apply LinearMap.ext
    intro p
    change (TensorProduct.piScalarRight R R N (Fin n)
        ((rTensorHomToHomRTensor (.id R) P N (Fin n → R) (f ⊗ₜ[R] u)) p)) i =
      (TensorProduct.piScalarRight R R (P →ₗ[R] N) (Fin n) (f ⊗ₜ[R] u)) i p
    rw [rTensorHomToHomRTensor_apply]
    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      LinearMap.smul_apply]
  have hb : Function.Bijective
      (fun x => t (rTensorHomToHomRTensor (.id R) P N (Fin n → R) x)) := by
    change Function.Bijective (t.toLinearMap.comp
      (rTensorHomToHomRTensor (.id R) P N (Fin n → R)))
    rw [he]
    exact e.bijective
  constructor
  · intro x y h
    exact hb.injective (congrArg t h)
  · intro y
    obtain ⟨x, hx⟩ := hb.surjective (t y)
    exact ⟨x, t.injective hx⟩

/-- **Hom–tensor comparison for a finite-projective factor.**

Let R be a commutative ring and P,N R-modules. For an R-module U, define C_U:Hom_R(P,N)⊗_R
U→Hom_R(P,N⊗_R U) by C_U(f⊗u)(p)=f(p)⊗u. If U is finitely generated projective over R, C_U is
bijective.
-/
theorem homTensorFiniteFactor_bijective
    (U : Type uU) [AddCommGroup U] [Module R U]
    [Module.Finite R U] [Module.Projective R U] :
    Function.Bijective (rTensorHomToHomRTensor (.id R) P N U) := by
  obtain ⟨n, f, g, hf, hg, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R U
  let dF := f.lTensor (P →ₗ[R] N)
  let dG := g.lTensor (P →ₗ[R] N)
  let cF := (f.lTensor N).compRight R (M := P)
  let cG := (g.lTensor N).compRight R (M := P)
  have hd : dF.comp dG = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, hfg, LinearMap.lTensor_id]
  have hfgN : (f.lTensor N).comp (g.lTensor N) = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, hfg, LinearMap.lTensor_id]
  have hc : cF.comp cG = LinearMap.id := by
    ext h p
    change (f.lTensor N) ((g.lTensor N) (h p)) = h p
    exact LinearMap.congr_fun hfgN (h p)
  have hFree := homTensorFiniteFree_bijective R P N n
  have hNatF := homTensorCoefficient_naturality R P N f
  have hNatG := homTensorCoefficient_naturality R P N g
  exact LinearMap.comparison_bijective_of_retract
    (rTensorHomToHomRTensor (.id R) P N U)
    (rTensorHomToHomRTensor (.id R) P N (Fin n → R))
    dG dF cG cF hd hc hNatG hNatF hFree

/-- **Hom–tensor linear equivalence for a finite-projective factor.**

Let R be a commutative ring and P,N R-modules. For an R-module U, define C_U:Hom_R(P,N)⊗_R
U→Hom_R(P,N⊗_R U) by C_U(f⊗u)(p)=f(p)⊗u. For U finitely generated projective over R,
homTensorFiniteFactorEquiv R P N U:Hom_R(P,N)⊗_R U≃ₗ[R]Hom_R(P,N⊗_R U) is C_U, with
C_U(f⊗u)(p)=f(p)⊗u.
-/
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
