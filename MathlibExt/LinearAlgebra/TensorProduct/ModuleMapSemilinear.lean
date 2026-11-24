/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.TensorProduct.ModuleMap
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Semilinear maps for native tensor-product module actions

The two endpoint algebras may change independently and need not commute
internally. Equivariance under their actual commuting actions is equivalent
to semilinearity under the native tensor ring map. The source and target
module carriers retain their independent universes and their given ground
modules. No category of artificial bundled bimodules is introduced.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u a a' a'' b b' b'' m n p

namespace TensorProduct.Algebra

variable {k : Type u} [CommSemiring k]
  {A : Type a} {A' : Type a'} {B : Type b} {B' : Type b'}
  [Semiring A] [Semiring A'] [Semiring B] [Semiring B']
  [Algebra k A] [Algebra k A'] [Algebra k B] [Algebra k B']
  {M : Type m} {N : Type n}
  [AddCommMonoid M] [AddCommMonoid N] [Module k M] [Module k N]
  [Module A M] [Module B M] [Module A' N] [Module B' N]
  [IsScalarTower k A M] [IsScalarTower k B M]
  [IsScalarTower k A' N] [IsScalarTower k B' N]
  [SMulCommClass A B M] [SMulCommClass A' B' N]

/-- An equivariant ground map is semilinear for the actual native tensor ring map. -/
def ofSemilinearMap (φ : A →ₐ[k] A') (ψ : B →ₐ[k] B') (f : M →ₗ[k] N)
    (hA : ∀ (a : A) (x : M), f (a • x) = φ a • f x)
    (hB : ∀ (b : B) (x : M), f (b • x) = ψ b • f x) :
    letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
    letI : Module (A' ⊗[k] B') N := TensorProduct.Algebra.module
    M →ₛₗ[(Algebra.TensorProduct.map φ ψ).toRingHom] N := by
  letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
  letI : Module (A' ⊗[k] B') N := TensorProduct.Algebra.module
  refine { toFun := f, map_add' := f.map_add, map_smul' := ?_ }
  intro z x
  change f (z • x) = Algebra.TensorProduct.map φ ψ z • f x
  induction z using TensorProduct.inductionOn with
  | tmul a b => rw [smul_def, Algebra.TensorProduct.map_tmul, smul_def, hA, hB]
  | add z w hz hw => rw [add_smul, f.map_add, hz, hw, map_add, add_smul]

/-- The semilinear tensor-module map keeps the supplied original function. -/
theorem ofSemilinearMap_apply (φ : A →ₐ[k] A') (ψ : B →ₐ[k] B')
    (f : M →ₗ[k] N) (hA hB) (x : M) :
    ofSemilinearMap φ ψ f hA hB x = f x := rfl

/-- Native tensor semilinearity implies semilinearity under the first original action. -/
def toLeftSemilinearMap (φ : A →ₐ[k] A') (ψ : B →ₐ[k] B')
    (f : letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
      letI : Module (A' ⊗[k] B') N := TensorProduct.Algebra.module
      M →ₛₗ[(Algebra.TensorProduct.map φ ψ).toRingHom] N) :
    M →ₛₗ[φ.toRingHom] N := by
  letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
  letI : Module (A' ⊗[k] B') N := TensorProduct.Algebra.module
  refine { toFun := f, map_add' := f.map_add, map_smul' := ?_ }
  intro a x
  have h := f.map_smul' (a ⊗ₜ[k] (1 : B)) x
  change f ((a ⊗ₜ[k] (1 : B)) • x) =
    (Algebra.TensorProduct.map φ ψ (a ⊗ₜ[k] (1 : B))) • f x at h
  change f (a • x) = φ a • f x
  simpa only [Algebra.TensorProduct.map_tmul, map_one, smul_def, one_smul] using h

/-- Native tensor semilinearity likewise preserves the second original action. -/
def toRightSemilinearMap (φ : A →ₐ[k] A') (ψ : B →ₐ[k] B')
    (f : letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
      letI : Module (A' ⊗[k] B') N := TensorProduct.Algebra.module
      M →ₛₗ[(Algebra.TensorProduct.map φ ψ).toRingHom] N) :
    M →ₛₗ[ψ.toRingHom] N := by
  letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
  letI : Module (A' ⊗[k] B') N := TensorProduct.Algebra.module
  refine { toFun := f, map_add' := f.map_add, map_smul' := ?_ }
  intro b x
  have h := f.map_smul' ((1 : A) ⊗ₜ[k] b) x
  change f (((1 : A) ⊗ₜ[k] b) • x) =
    (Algebra.TensorProduct.map φ ψ ((1 : A) ⊗ₜ[k] b)) • f x at h
  change f (b • x) = ψ b • f x
  simpa only [Algebra.TensorProduct.map_tmul, map_one, smul_def, one_smul] using h

/-- The endpoint algebra maps retain the original ground-linear function. -/
def toGroundLinearMap (φ : A →ₐ[k] A') (ψ : B →ₐ[k] B')
    (f : letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
      letI : Module (A' ⊗[k] B') N := TensorProduct.Algebra.module
      M →ₛₗ[(Algebra.TensorProduct.map φ ψ).toRingHom] N) : M →ₗ[k] N := by
  let h := toLeftSemilinearMap φ ψ f
  refine { toFun := h, map_add' := h.map_add, map_smul' := ?_ }
  intro c x
  have hx := h.map_smulₛₗ (algebraMap k A c) x
  change h ((algebraMap k A c) • x) = φ (algebraMap k A c) • h x at hx
  simpa only [φ.commutes, IsScalarTower.algebraMap_smul, RingHom.id_apply] using hx

/-- The two endpoint equations characterize a native semilinear bimodule map. -/
def semilinearMapEquiv (φ : A →ₐ[k] A') (ψ : B →ₐ[k] B') :
    (letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
     letI : Module (A' ⊗[k] B') N := TensorProduct.Algebra.module
     M →ₛₗ[(Algebra.TensorProduct.map φ ψ).toRingHom] N) ≃
    {f : M →ₗ[k] N //
      (∀ (a : A) (x : M), f (a • x) = φ a • f x) ∧
        (∀ (b : B) (x : M), f (b • x) = ψ b • f x)} where
  toFun f := ⟨toGroundLinearMap φ ψ f,
    fun a x => (toLeftSemilinearMap φ ψ f).map_smulₛₗ a x,
    fun b x => by
      dsimp only [toGroundLinearMap, toLeftSemilinearMap]
      have h := (toRightSemilinearMap φ ψ f).map_smul' b x
      change f (b • x) = ψ b • f x at h
      exact h⟩
  invFun f := ofSemilinearMap φ ψ f.1 f.2.1 f.2.2
  left_inv f := by
    letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
    letI : Module (A' ⊗[k] B') N := TensorProduct.Algebra.module
    apply LinearMap.ext
    intro x
    rfl
  right_inv f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    rfl

/-- Reading the first action after constructing the tensor map changes no values. -/
theorem toLeftSemilinearMap_ofSemilinearMap (φ : A →ₐ[k] A') (ψ : B →ₐ[k] B')
    (f : M →ₗ[k] N) (hA hB) (x : M) :
    toLeftSemilinearMap φ ψ (ofSemilinearMap φ ψ f hA hB) x = f x := rfl

/-- Reading the second action has the same identity on original values. -/
theorem toRightSemilinearMap_ofSemilinearMap (φ : A →ₐ[k] A') (ψ : B →ₐ[k] B')
    (f : M →ₗ[k] N) (hA hB) (x : M) :
    toRightSemilinearMap φ ψ (ofSemilinearMap φ ψ f hA hB) x = f x := rfl

/-- The same supplied ground-module dictionary is recovered exactly. -/
theorem toGroundLinearMap_ofSemilinearMap (φ : A →ₐ[k] A') (ψ : B →ₐ[k] B')
    (f : M →ₗ[k] N) (hA hB) :
    toGroundLinearMap φ ψ (ofSemilinearMap φ ψ f hA hB) = f := by
  apply LinearMap.ext
  intro x
  rfl

section Composition

variable {A'' : Type a''} {B'' : Type b''} [Semiring A''] [Semiring B'']
  [Algebra k A''] [Algebra k B''] {P : Type p}
  [AddCommMonoid P] [Module k P] [Module A'' P] [Module B'' P]
  [IsScalarTower k A'' P] [IsScalarTower k B'' P] [SMulCommClass A'' B'' P]

/-- The earned tensor-semilinear maps compose on their original additive functions.
The scalar identification is the native `Algebra.TensorProduct.map_comp` law. -/
theorem ofSemilinearMap_comp (φ : A →ₐ[k] A') (ψ : B →ₐ[k] B')
    (φ' : A' →ₐ[k] A'') (ψ' : B' →ₐ[k] B'')
    (f : M →ₗ[k] N) (g : N →ₗ[k] P)
    (hA : ∀ (a : A) (x : M), f (a • x) = φ a • f x)
    (hB : ∀ (b : B) (x : M), f (b • x) = ψ b • f x)
    (hA' : ∀ (a : A') (x : N), g (a • x) = φ' a • g x)
    (hB' : ∀ (b : B') (x : N), g (b • x) = ψ' b • g x) :
    (ofSemilinearMap φ' ψ' g hA' hB').toAddMonoidHom.comp
        (ofSemilinearMap φ ψ f hA hB).toAddMonoidHom =
      (ofSemilinearMap (φ'.comp φ) (ψ'.comp ψ) (g.comp f)
        (fun a x => by
          change g (f (a • x)) = φ' (φ a) • g (f x)
          rw [hA, hA'])
        (fun b x => by
          change g (f (b • x)) = ψ' (ψ b) • g (f x)
          rw [hB, hB'])).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  rfl

end Composition

end TensorProduct.Algebra
