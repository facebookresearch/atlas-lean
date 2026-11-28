/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# Exterior powers of a product of modules

For modules `M,N` over a commutative ring `R`, `Λ^n_R(M×N)` is the direct sum of `Λ^p_R M ⊗[R]
Λ^q_R N` over `p+q=n`.

The inverse comparison assembles a mixed tensor by mapping its `M`-factor through the first
inclusion, mapping its `N`-factor through the second inclusion, and multiplying in that order
in the exterior algebra of `M×N`.

Reference: Bourbaki, *Algebra*, Chapter III.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct DirectSum

namespace exteriorPower

universe u v w
variable (R : Type u) [CommRing R]
variable (M : Type v) (N : Type w) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

local notation "β" => (fun p : ℕ × ℕ =>
  (ExteriorAlgebra.exteriorPower R (Prod.fst p) M) ⊗[R]
    (ExteriorAlgebra.exteriorPower R (Prod.snd p) N))
local notation "Fiber" n => {p : ℕ × ℕ // Prod.fst p + Prod.snd p = n}

/-- Let `R` be a commutative ring and `M,N` be `R`-modules. For `n : ℕ`, `productPieces R M N n`
is `⨁ (p,q) with p+q=n, Λ^p_R M ⊗[R] Λ^q_R N`, with the `M`-factor first and the `N`-factor
second. -/
abbrev productPieces (n : ℕ) :=
  ⨁ p : {p : ℕ × ℕ // p.1 + p.2 = n}, (⋀[R]^p.val.1 M) ⊗[R] (⋀[R]^p.val.2 N)

private def productBigEquiv : ExteriorAlgebra R (M × N) ≃ₗ[R]
    (⨁ p : ℕ × ℕ, (⋀[R]^p.1 M) ⊗[R] (⋀[R]^p.2 N)) :=
  (ExteriorAlgebra.prodEquivTensor R M N).toLinearEquiv.trans
    ((GradedTensorProduct.auxEquiv R (fun i : ℕ => ⋀[R]^i M) (fun j : ℕ => ⋀[R]^j N)).trans
      (TensorProduct.directSum R R (fun i : ℕ => ⋀[R]^i M) (fun j : ℕ => ⋀[R]^j N)))

private def productRegroupEquiv :
    (⨁ p : ℕ × ℕ, (⋀[R]^p.1 M) ⊗[R] (⋀[R]^p.2 N)) ≃ₗ[R]
      (⨁ n : ℕ, productPieces R M N n) :=
  (DirectSum.lequivCongrLeft R (Equiv.sigmaFiberEquiv (fun p : ℕ × ℕ => p.1 + p.2)).symm).trans
    (DirectSum.sigmaLcurryEquiv R (δ := fun (n : ℕ) (p : Fiber n) => β p.val))

private theorem productRegroupEquiv_of (i j : ℕ) (z : (⋀[R]^i M) ⊗[R] (⋀[R]^j N)) :
    productRegroupEquiv R M N (DirectSum.of β (i, j) z) =
      DirectSum.of (productPieces R M N) (i + j)
        (DirectSum.of (fun p : Fiber (i + j) => β p.val) ⟨(i, j), rfl⟩ z) := by
  change DirectSum.sigmaFiberAddEquiv (fun p : ℕ × ℕ => p.1 + p.2) (DirectSum.of β (i, j) z) = _
  exact DirectSum.sigmaFiberAddEquiv_of _ _ _

private def productTotalEquiv : ExteriorAlgebra R (M × N) ≃ₗ[R] (⨁ n : ℕ, productPieces R M N n) :=
  (productBigEquiv R M N).trans (productRegroupEquiv R M N)

private theorem productTotalEquiv_mixed (i j : ℕ) (x : ⋀[R]^i M) (y : ⋀[R]^j N) :
    productTotalEquiv R M N
      (ExteriorAlgebra.map (LinearMap.inl R M N) x * ExteriorAlgebra.map (LinearMap.inr R M N) y) =
      DirectSum.of (productPieces R M N) (i + j)
        (DirectSum.of (fun p : Fiber (i + j) => β p.val) ⟨(i, j), rfl⟩ (x ⊗ₜ[R] y)) := by
  rw [← ExteriorAlgebra.prodEquivTensor_symm_tmul R M N (x : ExteriorAlgebra R M)
    (y : ExteriorAlgebra R N)]
  unfold productTotalEquiv productBigEquiv
  simp only [LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply, AlgEquiv.apply_symm_apply]
  rw [GradedTensorProduct.auxEquiv_tmul, DirectSum.decompose_coe, DirectSum.decompose_coe]
  rw [← DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of R, TensorProduct.directSum_lof_tmul_lof,
    DirectSum.lof_eq_of, productRegroupEquiv_of]

private theorem productTotalEquiv_symm_mixed (n : ℕ)
    (p : {p : ℕ × ℕ // p.1 + p.2 = n}) (x : ⋀[R]^p.val.1 M) (y : ⋀[R]^p.val.2 N) :
    (productTotalEquiv R M N).symm
      (DirectSum.of (productPieces R M N) n
        (DirectSum.of (fun p : Fiber n => β p.val) p (x ⊗ₜ[R] y))) =
      ExteriorAlgebra.map (LinearMap.inl R M N) x *
        ExteriorAlgebra.map (LinearMap.inr R M N) y := by
  rcases p with ⟨⟨i, j⟩, h⟩
  subst n
  exact ((productTotalEquiv R M N).eq_symm_apply.mpr (productTotalEquiv_mixed R M N i j x y)).symm

private theorem productTotalEquiv_symm_mem (n : ℕ) (z : productPieces R M N n) :
    (productTotalEquiv R M N).symm (DirectSum.lof R ℕ (productPieces R M N) n z) ∈
      ⋀[R]^n (M × N) := by
  induction z using DirectSum.induction_on with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add z t hz ht =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hz ht
  | of p z =>
    rcases p with ⟨⟨i, j⟩, h⟩
    subst n
    induction z using TensorProduct.inductionOn with
    | add z t hz ht =>
      rw [map_add, map_add, map_add]
      exact Submodule.add_mem _ hz ht
    | tmul x y =>
      rw [DirectSum.lof_eq_of, productTotalEquiv_symm_mixed]
      have hx : ExteriorAlgebra.map (LinearMap.inl R M N) x ∈ ⋀[R]^i (M × N) := by
        simpa only [exteriorPower.coe_map] using
          (exteriorPower.map i (LinearMap.inl R M N) x).property
      have hy : ExteriorAlgebra.map (LinearMap.inr R M N) y ∈ ⋀[R]^j (M × N) := by
        simpa only [exteriorPower.coe_map] using
          (exteriorPower.map j (LinearMap.inr R M N) y).property
      exact SetLike.mul_mem_graded hx hy

private def productAssembly (n : ℕ) : productPieces R M N n →ₗ[R] (⋀[R]^n (M × N)) :=
  (((productTotalEquiv R M N).symm.toLinearMap).comp
    (DirectSum.lof R ℕ (productPieces R M N) n)).codRestrict
    (⋀[R]^n (M × N)) (productTotalEquiv_symm_mem R M N n)

private theorem productAssembly_bijective (n : ℕ) :
    Function.Bijective (productAssembly R M N n) := by
  have hinj : Function.Injective (productAssembly R M N n) := by
    intro x y hxy
    have h := (productTotalEquiv R M N).symm.injective (congrArg Subtype.val hxy)
    have h' := congrArg (fun z : ⨁ n : ℕ, productPieces R M N n => z n) h
    simpa only [DirectSum.lof_eq_of, DirectSum.of_eq_same] using h'
  let G : (⨁ n : ℕ, productPieces R M N n) →ₗ[R] (⨁ n : ℕ, ⋀[R]^n (M × N)) :=
    DirectSum.lmap (productAssembly R M N)
  have hG : (DirectSum.coeLinearMap (fun n : ℕ => ⋀[R]^n (M × N))).comp G =
      (productTotalEquiv R M N).symm.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro k
    apply LinearMap.ext
    intro z
    simp only [G, LinearMap.comp_apply, DirectSum.lmap_lof, DirectSum.coeLinearMap_lof]
    rfl
  have hsur : Function.Surjective G := by
    intro z
    let y : ⨁ n : ℕ, productPieces R M N n :=
      productTotalEquiv R M N (DirectSum.coeLinearMap (fun n : ℕ => ⋀[R]^n (M × N)) z)
    refine ⟨y, ?_⟩
    apply (DirectSum.Decomposition.isInternal (fun n : ℕ => ⋀[R]^n (M × N))).injective
    change DirectSum.coeLinearMap (fun n : ℕ => ⋀[R]^n (M × N)) (G y) =
      DirectSum.coeLinearMap (fun n : ℕ => ⋀[R]^n (M × N)) z
    rw [← LinearMap.comp_apply, hG]
    exact (productTotalEquiv R M N).symm_apply_apply _
  refine ⟨hinj, ?_⟩
  intro w
  obtain ⟨z, hz⟩ := hsur (DirectSum.lof R ℕ (fun n : ℕ => ⋀[R]^n (M × N)) n w)
  refine ⟨z n, ?_⟩
  have h := congrArg (fun t : ⨁ n : ℕ, ⋀[R]^n (M × N) => t n) hz
  simpa only [G, DirectSum.lmap_apply, DirectSum.lof_eq_of, DirectSum.of_eq_same] using h

/-- Let `R` be a commutative ring and `M,N` be `R`-modules. For `n : ℕ`, `productEquiv R M N n` is
the `R`-linear equivalence `Λ^n_R(M×N) ≃ₗ[R] ⨁_(p+q=n) Λ^p_R M ⊗[R] Λ^q_R N`. -/
@[no_expose]
def productEquiv (n : ℕ) : (⋀[R]^n (M × N)) ≃ₗ[R] productPieces R M N n :=
  (LinearEquiv.ofBijective (productAssembly R M N n) (productAssembly_bijective R M N n)).symm

/-- Let `R` be a commutative ring and `M,N` be `R`-modules. Let `p+q=n`, `x ∈ Λ^p_R M`, and `y ∈
Λ^q_R N`. The inverse of `productEquiv R M N n` sends the inclusion of `x ⊗ y` to `Λ(inl)(x) *
Λ(inr)(y)` in `ExteriorAlgebra R (M×N)`. -/
theorem productEquiv_symm_mixed (n : ℕ)
    (p : {p : ℕ × ℕ // p.1 + p.2 = n}) (x : ⋀[R]^p.val.1 M) (y : ⋀[R]^p.val.2 N) :
    ((productEquiv R M N n).symm (DirectSum.of _ p (x ⊗ₜ[R] y)) : ExteriorAlgebra R (M × N)) =
      ExteriorAlgebra.map (LinearMap.inl R M N) x *
        ExteriorAlgebra.map (LinearMap.inr R M N) y := by
  change (productTotalEquiv R M N).symm
    (DirectSum.lof R ℕ (productPieces R M N) n (DirectSum.of _ p (x ⊗ₜ[R] y))) = _
  rw [DirectSum.lof_eq_of]
  exact productTotalEquiv_symm_mixed R M N n p x y

end exteriorPower
