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
# Balanced base change of exterior powers

Let `k,R` be commutative rings with `R` a `k`-algebra. Let `M` be a `k`-module and right
`R`-module with commuting compatible actions, and let `V` be a `k`-module. The comparison is
the `k`-linear equivalence `M ⊗_R Λ^n_R(R ⊗_k V) ≃ M ⊗_k Λ^n_k V`, using the balanced tensor
presentation on the left.

On a word it sends `[m, r • ιMulti_R(1⊗v_j)]` to `(op r • m) ⊗ ιMulti_k(v_j)`. Its inverse
inserts `1` in each scalar-extended generator. The comparison commutes with ground-linear maps
`V → W`.

Reference: Bourbaki, *Algebra*, Chapter III.
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

/-- Let `k,R` be commutative rings with a `k`-algebra structure on `R`. Let `M` be a `k`-module
and a right `R`-module (`Module Rᵐᵒᵖ M`) whose actions commute and form the tower `k → Rᵐᵒᵖ →
M`. Let `V` be a `k`-module and put `N_n(V)=Λ^n_R(R ⊗[k] V)`, with its induced `k`-action. For
`n : ℕ`, the comparison is `TensorProduct.Balanced k R M N_n(V) ≃ₗ[k] M ⊗[k] Λ^n_k V`,
absorbing the scalar extension through the right coefficient action. -/
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

/-- Let `k,R` be commutative rings with a `k`-algebra structure on `R`. Let `M` be a `k`-module
and a right `R`-module (`Module Rᵐᵒᵖ M`) whose actions commute and form the tower `k → Rᵐᵒᵖ →
M`. Let `V` be a `k`-module and put `N_n(V)=Λ^n_R(R ⊗[k] V)`, with its induced `k`-action. For
`n : ℕ`, `m : M`, `r : R`, and `a : Fin n → V`, the balanced class of `(m, r • ιMulti_R(fun j
↦ 1⊗a j))` maps to `(op r • m) ⊗ ιMulti_k a`. -/
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

/-- Let `k,R` be commutative rings with a `k`-algebra structure on `R`. Let `M` be a `k`-module
and a right `R`-module (`Module Rᵐᵒᵖ M`) whose actions commute and form the tower `k → Rᵐᵒᵖ →
M`. Let `V` be a `k`-module and put `N_n(V)=Λ^n_R(R ⊗[k] V)`, with its induced `k`-action. For
`n : ℕ`, `m : M`, and `a : Fin n → V`, the balanced class of `(m, ιMulti_R(fun j ↦ 1⊗a j))`
maps to `m ⊗ ιMulti_k a`. -/
theorem balancedBaseChangeEquiv_mk_ιMulti (n : ℕ) (m : M) (a : Fin n → V) :
    letI : Module k (⋀[R]^n (R ⊗[k] V)) := Module.compHom _ (algebraMap k R)
    balancedBaseChangeEquiv k R M V n
      (TensorProduct.Balanced.mk k R M (⋀[R]^n (R ⊗[k] V)) m
        (ιMulti R n (fun j => (1 : R) ⊗ₜ[k] a j))) = m ⊗ₜ[k] ιMulti k n a := by
  simpa only [one_smul, op_one] using
    balancedBaseChangeEquiv_mk_smul_ιMulti k R M V n m (1 : R) a

/-- Let `k,R` be commutative rings with a `k`-algebra structure on `R`. Let `M` be a `k`-module
and a right `R`-module (`Module Rᵐᵒᵖ M`) whose actions commute and form the tower `k → Rᵐᵒᵖ →
M`. Let `V` be a `k`-module and put `N_n(V)=Λ^n_R(R ⊗[k] V)`, with its induced `k`-action. For
`n : ℕ`, `m : M`, and `a : Fin n → V`, the inverse comparison sends `m ⊗ ιMulti_k a` to the
balanced class of `(m, ιMulti_R(fun j ↦ 1⊗a j))`. -/
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

/-- Let `k,R` be commutative rings with `R` a `k`-algebra, `M` a `k`-module and right `R`-module,
`V,W` be `k`-modules, and `f : V →ₗ[k] W`. Put `N_n(V)=Λ^n_R(R ⊗[k] V)` with its induced
ground action. For `n : ℕ`, the `k`-linear balanced map fixes `M` and applies `Λ^n_R(id_R ⊗ f)
: N_n(V) → N_n(W)` to the exterior factor. -/
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
/-- Let `k,R` be commutative rings with `R` a `k`-algebra, `M` a `k`-module and right `R`-module,
`V,W` be `k`-modules, and `f : V →ₗ[k] W`. Put `N_n(V)=Λ^n_R(R ⊗[k] V)` with its induced
ground action. For `n : ℕ`, `m : M`, and `a : Fin n → V`, the balanced map sends `[m,
ιMulti_R(1⊗a_j)]` to `[m, ιMulti_R(1⊗f(a_j))]`. -/
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

/-- Let `k,R` be commutative rings with a `k`-algebra structure on `R`. Let `M` be a `k`-module
and a right `R`-module (`Module Rᵐᵒᵖ M`) whose actions commute and form the tower `k → Rᵐᵒᵖ →
M`. Let `V` be a `k`-module and put `N_n(V)=Λ^n_R(R ⊗[k] V)`, with its induced `k`-action. For
a `k`-module `W`, `f : V →ₗ[k] W`, and `n : ℕ`, `E_W ∘ B_f = (id_M ⊗ Λ^n_k f) ∘ E_V`, where
`E_V,E_W` are the balanced cancellation equivalences and `B_f` the induced balanced exterior
map. -/
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
