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
public import Mathlib.RingTheory.Finiteness.Projective
public import MathlibExt.LinearAlgebra.LinearMap.RetractComparison

/-!
# A finite projective factor commutes with arbitrary products

Let R be commutative, N_i an arbitrary family of R-modules and U a finitely generated projective
R-module. The canonical map π:U⊗_R(∏_iN_i)→∏_i(U⊗_RN_i), π(u⊗x)_i=u⊗x_i, is bijective and gives
a linear equivalence. The product index may be infinite.

For U=R^n this is finite-free coordinate interchange. Taking a finite projective U as a retract
of a finite free module and using factor naturality gives the general result. The forward map
remains π, with independent scalar, index and carrier universes.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open scoped TensorProduct

namespace TensorProduct

universe uR uI uN uU uV

variable (R : Type uR) [CommRing R] {ι : Type uI}
  (N : ι → Type uN) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

attribute [local ext high] TensorProduct.ext

/-- Let R be a commutative ring, ι an arbitrary index type and N_i R-modules, with independent ring,
index and carrier universes. For n∈ℕ, the R-linear equivalence (Fin n→∏_iN_i)≅∏_i(Fin n→N_i)
sends x to y_i(j)=x_j(i). Its inverse exchanges the same coordinates. -/
def finitePiFlip (n : ℕ) : (Fin n → ∀ i, N i) ≃ₗ[R] ∀ i, Fin n → N i where
  toFun x i j := x j i
  invFun x j i := x i j
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Let R be a commutative ring, ι an arbitrary index type and N_i R-modules, with independent ring,
index and carrier universes. For linear f:U→V in independent carrier universes,
π_V∘(f⊗id_{∏N_i})=(∏_i(f⊗id_{N_i}))∘π_U, where π_U,π_V are the componentwise tensor maps.
Neither factor needs to be finite for this square. -/
theorem piRightHom_factor_naturality
    {U : Type uU} {V : Type uV}
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (f : U →ₗ[R] V) :
    (piRightHom R R V N).comp (f.rTensor (∀ i, N i)) =
      (LinearMap.piMap (fun i => f.rTensor (N i))).comp (piRightHom R R U N) := by
  apply TensorProduct.ext'
  intro u x
  funext i
  rfl

/-- Let R be a commutative ring, ι an arbitrary index type and N_i R-modules, with independent ring,
index and carrier universes. For n∈ℕ, R^n⊗_R(∏_iN_i)→∏_i(R^n⊗_RN_i) is bijective. Finite-free
coordinates identify both sides with ∏_i(N_i)^n, including n=0. -/
theorem piRightHom_finiteFree_bijective (n : ℕ) :
    Function.Bijective (piRightHom R R (Fin n → R) N) := by
  let eD : (Fin n → R) ⊗[R] (∀ i, N i) ≃ₗ[R] (∀ i, Fin n → N i) :=
    TensorProduct.comm R _ _ ≪≫ₗ TensorProduct.piScalarRight R R (∀ i, N i) (Fin n) ≪≫ₗ
      finitePiFlip R N n
  let eC : (∀ i, (Fin n → R) ⊗[R] N i) ≃ₗ[R] (∀ i, Fin n → N i) :=
    LinearEquiv.piCongrRight (fun i => TensorProduct.comm R _ _ ≪≫ₗ
      TensorProduct.piScalarRight R R (N i) (Fin n))
  have he : eC.toLinearMap.comp (piRightHom R R (Fin n → R) N) = eD.toLinearMap := by
    apply TensorProduct.ext'
    intro u x
    funext i j
    change (TensorProduct.piScalarRight R R (N i) (Fin n) (x i ⊗ₜ[R] u)) j =
      (TensorProduct.piScalarRight R R (∀ i, N i) (Fin n) (x ⊗ₜ[R] u)) j i
    simp only [TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul, Pi.smul_apply]
  have hb : Function.Bijective (fun x => eC (piRightHom R R (Fin n → R) N x)) := by
    change Function.Bijective (eC.toLinearMap.comp (piRightHom R R (Fin n → R) N))
    rw [he]
    exact eD.bijective
  constructor
  · intro x y h
    exact hb.injective (congrArg eC h)
  · intro y
    obtain ⟨x, hx⟩ := hb.surjective (eC y)
    exact ⟨x, eC.injective hx⟩

/-- Let R be a commutative ring, ι an arbitrary index type and N_i R-modules, with independent ring,
index and carrier universes. For finitely generated projective U, π_U:U⊗_R(∏_iN_i)→∏_i(U⊗_RN_i)
is bijective. U is a retract of a finite free module and factor naturality carries the
comparison through that retract. -/
theorem piRightHom_finiteFactor_bijective
    (U : Type uU) [AddCommGroup U] [Module R U]
    [Module.Finite R U] [Module.Projective R U] :
    Function.Bijective (piRightHom R R U N) := by
  obtain ⟨n, f, g, hf, hg, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R U
  let dF := f.rTensor (∀ i, N i)
  let dG := g.rTensor (∀ i, N i)
  let cF := LinearMap.piMap (fun i => f.rTensor (N i))
  let cG := LinearMap.piMap (fun i => g.rTensor (N i))
  have hd : dF.comp dG = LinearMap.id := by
    rw [← LinearMap.rTensor_comp, hfg, LinearMap.rTensor_id]
  have hc : cF.comp cG = LinearMap.id := by
    ext x i
    have h : (f.rTensor (N i)).comp (g.rTensor (N i)) = LinearMap.id := by
      rw [← LinearMap.rTensor_comp, hfg, LinearMap.rTensor_id]
    exact LinearMap.congr_fun h (x i)
  exact LinearMap.comparison_bijective_of_retract
    (piRightHom R R U N) (piRightHom R R (Fin n → R) N)
    dG dF cG cF hd hc (piRightHom_factor_naturality R N g)
      (piRightHom_factor_naturality R N f) (piRightHom_finiteFree_bijective R N n)

/-- Let R be a commutative ring, ι an arbitrary index type and N_i R-modules, with independent ring,
index and carrier universes. For finitely generated projective U, this is the R-linear
equivalence U⊗_R(∏_iN_i)≅∏_i(U⊗_RN_i), with forward map u⊗x↦(i↦u⊗x_i). U is the left factor and
the arbitrary product is on the right. -/
def piRightFiniteFactor
    (U : Type uU) [AddCommGroup U] [Module R U]
    [Module.Finite R U] [Module.Projective R U] :
    U ⊗[R] (∀ i, N i) ≃ₗ[R] ∀ i, U ⊗[R] N i :=
  LinearEquiv.ofBijective (piRightHom R R U N) (piRightHom_finiteFactor_bijective R N U)

/-- Let R be a commutative ring, ι an arbitrary index type and N_i R-modules, with independent ring,
index and carrier universes. For finitely generated projective U, the underlying linear map of
the product equivalence is π_U, characterized by π_U(u⊗x)_i=u⊗x_i. -/
theorem piRightFiniteFactor_toLinearMap
    (U : Type uU) [AddCommGroup U] [Module R U]
    [Module.Finite R U] [Module.Projective R U] :
    (piRightFiniteFactor R N U).toLinearMap = piRightHom R R U N := rfl

end TensorProduct
