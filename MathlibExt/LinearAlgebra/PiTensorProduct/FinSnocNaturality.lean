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

public import MathlibExt.LinearAlgebra.PiTensorProduct.FinSnoc

/-!
# Naturality of the ordered last-factor splitting

For a family of semimodule maps over a commutative semiring, the finite-dependent tensor
splitting commutes with the maps of its ordered prefix and final factor. This law supplies
the native carrier transport of categorical representation tensor powers.
-/

@[expose] public section
noncomputable section
universe r v w
namespace PiTensorProduct
variable (R : Type r) [CommSemiring R]

/-- The ordered last-factor splitting commutes with a family of linear maps. -/
theorem finSnocEquiv_naturality (n : ℕ)
    (V : Fin (n + 1) → Type v) (W : Fin (n + 1) → Type w)
    [∀ j, AddCommMonoid (V j)] [∀ j, Module R (V j)]
    [∀ j, AddCommMonoid (W j)] [∀ j, Module R (W j)]
    (f : ∀ j, V j →ₗ[R] W j) :
    (finSnocEquiv R n W).toLinearMap.comp (PiTensorProduct.map f) =
      (TensorProduct.map (PiTensorProduct.map (fun j : Fin n => f j.castSucc))
        (f (Fin.last n))).comp (finSnocEquiv R n V).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    PiTensorProduct.map_tprod]
  change finSnocEquiv R n W (PiTensorProduct.tprod R (fun j => f j (x j))) =
    TensorProduct.map (PiTensorProduct.map (fun j : Fin n => f j.castSucc)) (f (Fin.last n))
      (finSnocEquiv R n V (PiTensorProduct.tprod R x))
  calc
    _ = PiTensorProduct.tprod R (fun j : Fin n => f j.castSucc (x j.castSucc)) ⊗ₜ[R]
        f (Fin.last n) (x (Fin.last n)) :=
      finSnocEquiv_tprod R n W (fun j => f j (x j))
    _ = TensorProduct.map (PiTensorProduct.map (fun j : Fin n => f j.castSucc))
        (f (Fin.last n))
        (PiTensorProduct.tprod R (fun j : Fin n => x j.castSucc) ⊗ₜ[R] x (Fin.last n)) := by
      rw [TensorProduct.map_tmul, PiTensorProduct.map_tprod]
    _ = _ := congrArg
      (TensorProduct.map (PiTensorProduct.map (fun j : Fin n => f j.castSucc)) (f (Fin.last n)))
      (finSnocEquiv_tprod R n V x).symm

end PiTensorProduct
