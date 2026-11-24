/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/- Balanced coefficients of scalar-extended exterior powers. -/
module

public import MathlibExt.LinearAlgebra.ExteriorPower.BaseChange
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced

/-!
# Balanced coefficients of scalar-extended exterior powers

Exterior powers commute with scalar extension without a basis or flatness
hypothesis. Combining that existing equivalence with the actual balanced
tensor cancellation identifies
`M ⊗_R ⋀_R^n (R ⊗_k V)` with `M ⊗_k ⋀_k^n V`.

The original right `R`-action and original ground action of `M` are retained.
All carrier universes are independent. Neither `M` nor `V` is assumed free,
projective, flat or finite. The comparison is canonical on exterior words.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct
open MulOpposite

universe u v w z z'

namespace exteriorPower

variable (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R]
  (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
  [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ M]
  (V : Type z) [AddCommGroup V] [Module k V]

/-- The actual balanced tensor of a scalar-extended exterior power cancels
the regular scalar factor, preserving the original coefficient module. -/
def balancedBaseChangeEquiv (n : ℕ) :
    letI : Module k (⋀[R]^n (R ⊗[k] V)) := Module.compHom _ (algebraMap k R)
    TensorProduct.Balanced k R M (⋀[R]^n (R ⊗[k] V)) ≃ₗ[k] M ⊗[k] (⋀[k]^n V) := by
  letI : Module k (⋀[R]^n (R ⊗[k] V)) := Module.compHom _ (algebraMap k R)
  letI : IsScalarTower k R (⋀[R]^n (R ⊗[k] V)) := IsScalarTower.of_compHom _ _ _
  let e : (⋀[R]^n (R ⊗[k] V)) ≃ₗ[R] (R ⊗[k] (⋀[k]^n V)) :=
    (baseChangeEquiv k R V n).symm
  let eK : (⋀[R]^n (R ⊗[k] V)) ≃ₗ[k] (R ⊗[k] (⋀[k]^n V)) := {
    toFun := e
    invFun := e.symm
    left_inv := e.symm_apply_apply
    right_inv := e.apply_symm_apply
    map_add' := e.map_add
    map_smul' := fun c x => by
      change e ((algebraMap k R c) • x) = c • e x
      rw [e.map_smul]
      exact IsScalarTower.algebraMap_smul R c (e x) }
  exact (TensorProduct.Balanced.congr (LinearEquiv.refl k M) eK
    (fun _ _ => rfl) (fun r x => e.map_smul r x)).trans
      (TensorProduct.Balanced.cancelEquiv k R M (⋀[k]^n V))

/-- A scalar-extended pure exterior word is absorbed by its actual original
right coefficient action; no transported coefficient action is chosen. -/
theorem balancedBaseChangeEquiv_mk_smul_ιMulti
    (n : ℕ) (m : M) (r : R) (a : Fin n → V) :
    letI : Module k (⋀[R]^n (R ⊗[k] V)) := Module.compHom _ (algebraMap k R)
    balancedBaseChangeEquiv k R M V n
      (TensorProduct.Balanced.mk k R M (⋀[R]^n (R ⊗[k] V)) m
        (r • ιMulti R n (fun j => (1 : R) ⊗ₜ[k] a j))) =
      (op r • m) ⊗ₜ[k] ιMulti k n a := by
  letI : Module k (⋀[R]^n (R ⊗[k] V)) := Module.compHom _ (algebraMap k R)
  letI : IsScalarTower k R (⋀[R]^n (R ⊗[k] V)) := IsScalarTower.of_compHom _ _ _
  erw [balancedBaseChangeEquiv, LinearEquiv.trans_apply,
    TensorProduct.Balanced.congr_mk]
  change TensorProduct.Balanced.cancelEquiv k R M (⋀[k]^n V)
    (TensorProduct.Balanced.mk k R M (R ⊗[k] (⋀[k]^n V)) m
      ((baseChangeEquiv k R V n).symm
        (r • ιMulti R n (fun j => (1 : R) ⊗ₜ[k] a j)))) = _
  erw [baseChangeEquiv_symm_apply_smul_ιMulti, TensorProduct.Balanced.cancelEquiv_mk_tmul]

/-- On an unscaled original exterior word the original coefficient head is unchanged. -/
theorem balancedBaseChangeEquiv_mk_ιMulti (n : ℕ) (m : M) (a : Fin n → V) :
    letI : Module k (⋀[R]^n (R ⊗[k] V)) := Module.compHom _ (algebraMap k R)
    balancedBaseChangeEquiv k R M V n
      (TensorProduct.Balanced.mk k R M (⋀[R]^n (R ⊗[k] V)) m
        (ιMulti R n (fun j => (1 : R) ⊗ₜ[k] a j))) = m ⊗ₜ[k] ιMulti k n a := by
  simpa only [one_smul, op_one] using
    balancedBaseChangeEquiv_mk_smul_ιMulti k R M V n m (1 : R) a

/-- The inverse inserts the original scalar unit into each generator before balancing. -/
theorem balancedBaseChangeEquiv_symm_tmul_ιMulti
    (n : ℕ) (m : M) (a : Fin n → V) :
    letI : Module k (⋀[R]^n (R ⊗[k] V)) := Module.compHom _ (algebraMap k R)
    (balancedBaseChangeEquiv k R M V n).symm (m ⊗ₜ[k] ιMulti k n a) =
      TensorProduct.Balanced.mk k R M (⋀[R]^n (R ⊗[k] V)) m
        (ιMulti R n (fun j => (1 : R) ⊗ₜ[k] a j)) := by
  letI : Module k (⋀[R]^n (R ⊗[k] V)) := Module.compHom _ (algebraMap k R)
  apply (balancedBaseChangeEquiv k R M V n).injective
  rw [LinearEquiv.apply_symm_apply, balancedBaseChangeEquiv_mk_ιMulti]

section Maps

variable {W : Type z'} [AddCommGroup W] [Module k W]

/-- The actual exterior map of a ground-linear map, on the balanced scalar-extended model. -/
def balancedBaseChangeMap (f : V →ₗ[k] W) (n : ℕ) :
    letI : Module k (⋀[R]^n (R ⊗[k] V)) := Module.compHom _ (algebraMap k R)
    letI : Module k (⋀[R]^n (R ⊗[k] W)) := Module.compHom _ (algebraMap k R)
    TensorProduct.Balanced k R M (⋀[R]^n (R ⊗[k] V)) →ₗ[k]
      TensorProduct.Balanced k R M (⋀[R]^n (R ⊗[k] W)) := by
  letI : Module k (⋀[R]^n (R ⊗[k] V)) := Module.compHom _ (algebraMap k R)
  letI : Module k (⋀[R]^n (R ⊗[k] W)) := Module.compHom _ (algebraMap k R)
  letI : IsScalarTower k R (⋀[R]^n (R ⊗[k] V)) := IsScalarTower.of_compHom _ _ _
  letI : IsScalarTower k R (⋀[R]^n (R ⊗[k] W)) := IsScalarTower.of_compHom _ _ _
  let g : (⋀[R]^n (R ⊗[k] V)) →ₗ[R] (⋀[R]^n (R ⊗[k] W)) := map n (f.baseChange R)
  let gK : (⋀[R]^n (R ⊗[k] V)) →ₗ[k] (⋀[R]^n (R ⊗[k] W)) := {
    toFun := g
    map_add' := g.map_add
    map_smul' := fun c x => by
      change g ((algebraMap k R c) • x) = (algebraMap k R c) • g x
      exact g.map_smul _ _ }
  exact TensorProduct.Balanced.map (LinearMap.id : M →ₗ[k] M) gK
    (fun _ _ => rfl) (fun r x => g.map_smul r x)

omit [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ M] in
/-- The original ground-linear map applies to every original exterior generator. -/
theorem balancedBaseChangeMap_mk_ιMulti
    (f : V →ₗ[k] W) (n : ℕ) (m : M) (a : Fin n → V) :
    letI : Module k (⋀[R]^n (R ⊗[k] V)) := Module.compHom _ (algebraMap k R)
    letI : Module k (⋀[R]^n (R ⊗[k] W)) := Module.compHom _ (algebraMap k R)
    balancedBaseChangeMap k R M V f n
      (TensorProduct.Balanced.mk k R M (⋀[R]^n (R ⊗[k] V)) m
        (ιMulti R n (fun j => (1 : R) ⊗ₜ[k] a j))) =
      TensorProduct.Balanced.mk k R M (⋀[R]^n (R ⊗[k] W)) m
        (ιMulti R n (fun j => (1 : R) ⊗ₜ[k] f (a j))) := by
  letI : Module k (⋀[R]^n (R ⊗[k] V)) := Module.compHom _ (algebraMap k R)
  letI : Module k (⋀[R]^n (R ⊗[k] W)) := Module.compHom _ (algebraMap k R)
  letI : IsScalarTower k R (⋀[R]^n (R ⊗[k] V)) := IsScalarTower.of_compHom _ _ _
  letI : IsScalarTower k R (⋀[R]^n (R ⊗[k] W)) := IsScalarTower.of_compHom _ _ _
  erw [balancedBaseChangeMap, TensorProduct.Balanced.map_mk]
  change TensorProduct.Balanced.mk k R M (⋀[R]^n (R ⊗[k] W)) m
    ((map n (f.baseChange R)) (ιMulti R n (fun j => (1 : R) ⊗ₜ[k] a j))) = _
  rw [map_apply_ιMulti]
  apply congrArg (TensorProduct.Balanced.mk k R M (⋀[R]^n (R ⊗[k] W)) m)
  apply congrArg (ιMulti R n)
  funext j
  change (f.baseChange R) ((1 : R) ⊗ₜ[k] a j) = (1 : R) ⊗ₜ[k] f (a j)
  rw [LinearMap.baseChange_tmul]

/-- Canonical cancellation is natural in the original ground module, across independent worlds. -/
theorem balancedBaseChangeEquiv_naturality (f : V →ₗ[k] W) (n : ℕ) :
    letI : Module k (⋀[R]^n (R ⊗[k] V)) := Module.compHom _ (algebraMap k R)
    letI : Module k (⋀[R]^n (R ⊗[k] W)) := Module.compHom _ (algebraMap k R)
    (balancedBaseChangeEquiv k R M W n).toLinearMap.comp
        (balancedBaseChangeMap k R M V f n) =
      (TensorProduct.map LinearMap.id (map n f)).comp
        (balancedBaseChangeEquiv k R M V n).toLinearMap := by
  letI : Module k (⋀[R]^n (R ⊗[k] V)) := Module.compHom _ (algebraMap k R)
  letI : Module k (⋀[R]^n (R ⊗[k] W)) := Module.compHom _ (algebraMap k R)
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (balancedBaseChangeEquiv k R M V n).symm.surjective x
  have h :
      ((balancedBaseChangeEquiv k R M W n).toLinearMap.comp
        (balancedBaseChangeMap k R M V f n)).comp
          (balancedBaseChangeEquiv k R M V n).symm.toLinearMap =
      ((TensorProduct.map LinearMap.id (map n f)).comp
        (balancedBaseChangeEquiv k R M V n).toLinearMap).comp
          (balancedBaseChangeEquiv k R M V n).symm.toLinearMap := by
    apply TensorProduct.curry_injective
    apply LinearMap.ext
    intro m
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    change balancedBaseChangeEquiv k R M W n
      (balancedBaseChangeMap k R M V f n
        ((balancedBaseChangeEquiv k R M V n).symm (m ⊗ₜ[k] ιMulti k n a))) =
      TensorProduct.map (LinearMap.id : M →ₗ[k] M) (map n f)
        (balancedBaseChangeEquiv k R M V n
          ((balancedBaseChangeEquiv k R M V n).symm (m ⊗ₜ[k] ιMulti k n a)))
    rw [LinearEquiv.apply_symm_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      map_apply_ιMulti, balancedBaseChangeEquiv_symm_tmul_ιMulti,
      balancedBaseChangeMap_mk_ιMulti, balancedBaseChangeEquiv_mk_ιMulti]
    rfl
  exact DFunLike.congr_fun h y

end Maps

end exteriorPower
