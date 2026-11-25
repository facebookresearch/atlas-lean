/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.ModuleCat.RingHomInduction.Universes

/-!
# Identity induction

Induction along the identity scalar map is isomorphic to the identity functor. Evaluation and
insertion of the unit tensor are inverse, natural maps; induction also preserves coefficient
isomorphisms.
-/

@[expose] public section

open CategoryTheory

universe u v w z

namespace ModuleCat.RingHomInduction

section CoefficientEquivalence

variable {k : Type u} {R : Type v} [Ring k] [Ring R] (φ : k →+* R)
variable {M : Type w} {N : Type z}
  [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]

/-- Induction sends inverse coefficient maps to inverse maps. -/
def mapEquiv (e : M ≃ₗ[k] N) : Carrier φ M ≃ₗ[R] Carrier φ N := by
  refine LinearEquiv.ofLinearMap (map φ e.toLinearMap) (map φ e.symm.toLinearMap) ?_ ?_
  · apply hom_ext φ N
    intro r n
    simp only [LinearMap.comp_apply, map_tensor]
    change tensor φ N r (e (e.symm n)) = tensor φ N r n
    exact congrArg (tensor φ N r) (e.apply_symm_apply n)
  · apply hom_ext φ M
    intro r m
    simp only [LinearMap.comp_apply, map_tensor]
    change tensor φ M r (e.symm (e m)) = tensor φ M r m
    exact congrArg (tensor φ M r) (e.symm_apply_apply m)

theorem mapEquiv_tensor (e : M ≃ₗ[k] N) (r : R) (m : M) :
    mapEquiv φ e (tensor φ M r m) = tensor φ N r (e m) := map_tensor φ e.toLinearMap r m

theorem mapEquiv_symm_tensor (e : M ≃ₗ[k] N) (r : R) (n : N) :
    (mapEquiv φ e).symm (tensor φ N r n) = tensor φ M r (e.symm n) :=
  map_tensor φ e.symm.toLinearMap r n

end CoefficientEquivalence

section Identity

variable (k : Type u) [Ring k]
variable (M : Type w) [AddCommGroup M] [Module k M]

/-- Evaluate identity induction on the module action. -/
def identityEval : Carrier (RingHom.id k) M →ₗ[k] M :=
  extendHom (RingHom.id k) (LinearMap.id : M →ₗ[k] M)

theorem identityEval_tensor (r : k) (m : M) :
    identityEval k M (tensor (RingHom.id k) M r m) = r • m := rfl

/-- Insert the unit tensor; its linearity follows from balancing. -/
def identityInsert : M →ₗ[k] Carrier (RingHom.id k) M where
  toFun m := tensor (RingHom.id k) M 1 m
  map_add' m n := tensor_add_right (RingHom.id k) M 1 m n
  map_smul' a m := tensor_one_smul (RingHom.id k) M a m

theorem identityInsert_apply (m : M) :
    identityInsert k M m = tensor (RingHom.id k) M 1 m := rfl

theorem identityEval_insert :
    (identityEval k M).comp (identityInsert k M) = LinearMap.id := by
  apply LinearMap.ext
  intro m
  change identityEval k M (tensor (RingHom.id k) M 1 m) = m
  rw [identityEval_tensor, one_smul]

theorem identityInsert_eval :
    (identityInsert k M).comp (identityEval k M) = LinearMap.id := by
  apply hom_ext (RingHom.id k) M
  intro r m
  change tensor (RingHom.id k) M 1
    (identityEval k M (tensor (RingHom.id k) M r m)) = tensor (RingHom.id k) M r m
  rw [identityEval_tensor]
  simpa only [RingHom.id_apply, one_mul] using
    (tensor_balance (RingHom.id k) M r 1 m).symm

/-- Identity induction on any coefficient carrier, without identifying its universe with k's. -/
def identityEquiv : Carrier (RingHom.id k) M ≃ₗ[k] M :=
  LinearEquiv.ofLinearMap (identityEval k M) (identityInsert k M)
    (identityEval_insert k M) (identityInsert_eval k M)

theorem identityEquiv_tensor (r : k) (m : M) :
    identityEquiv k M (tensor (RingHom.id k) M r m) = r • m := rfl

theorem identityEquiv_symm (m : M) :
    (identityEquiv k M).symm m = tensor (RingHom.id k) M 1 m := rfl

variable {M}

theorem identityEval_naturality {N : Type z} [AddCommGroup N] [Module k N]
    (f : M →ₗ[k] N) :
    (identityEval k N).comp (map (RingHom.id k) f) = f.comp (identityEval k M) := by
  apply hom_ext (RingHom.id k) M
  intro r m
  simp only [LinearMap.comp_apply, map_tensor, identityEval_tensor]
  exact (f.map_smul r m).symm

theorem identityInsert_naturality {N : Type z} [AddCommGroup N] [Module k N]
    (f : M →ₗ[k] N) :
    (map (RingHom.id k) f).comp (identityInsert k M) = (identityInsert k N).comp f := by
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, identityInsert_apply, map_tensor]

/-- The identity comparison is natural on the constructed common carrier universe. -/
def identityIso : ModuleCat.induceScalars.{u, u, w} (RingHom.id k) ≅
    𝟭 (ModuleCat.{max u w} k) :=
  NatIso.ofComponents (fun M => (identityEquiv k M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    exact identityEval_naturality k f.hom)

theorem identityIso_hom_tensor (M : ModuleCat.{max u w} k) (r : k) (m : M) :
    (identityIso k).hom.app M (tensor (RingHom.id k) M r m) = r • m := rfl

theorem identityIso_inv (M : ModuleCat.{max u w} k) (m : M) :
    (identityIso k).inv.app M m = tensor (RingHom.id k) M 1 m := rfl

end Identity

end ModuleCat.RingHomInduction
