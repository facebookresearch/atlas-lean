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

public import MathlibExt.LinearAlgebra.TensorProduct.Balanced
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.GroundChange
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Integer-balanced cancellation of a scalar-extended factor

Let k be a commutative ring, R a possibly noncommutative k-algebra,
M a right R-module with compatible commuting k-action, and V a k-module.
Their additive groups and all scalar and carrier universes are independent.
The integer-ground balanced tensor product has an additive equivalence
M ⊗_R (R ⊗[k] V) ≅ M ⊗[k] V.

The forward map sends [m ⊗ (r ⊗ v)] to (m r) ⊗ v, and the inverse
sends m ⊗ v to [m ⊗ (1 ⊗ v)]. Comparing the two integer quotient
presentations and the k-ground quotient gives these maps without an
additional k-module structure on the integer quotient as an input.
They are natural in a k-linear right R-equivariant map on M and a
k-linear map on V.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open MulOpposite

universe u v w z w' z'

namespace TensorProduct.Balanced

variable (k : Type u) (R : Type v) (M : Type w) (V : Type z)
  [CommRing k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
  [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ M]
  [AddCommGroup V] [Module k V]

/-- Let k be a commutative ring, R a possibly noncommutative k-algebra,
M a right R-module with a compatible k-action commuting with R,
and V an additive commutative group with a k-module structure.
This is an additive equivalence between the integer-ground quotient
M ⊗_R (R ⊗[k] V) and its GroundChange.integral presentation,
together with the formula taking every pure pair [m ⊗ x] to the
same pure pair in that presentation. -/
def integralCoordinateData :
    {e : Balanced ℤ R M (R ⊗[k] V) ≃+
        GroundChange.integral R M (R ⊗[k] V) //
      ∀ (m : M) (x : R ⊗[k] V),
        e (mk ℤ R M (R ⊗[k] V) m x) =
          GroundChange.integralMk R M (R ⊗[k] V) m x} := by
  let N := R ⊗[k] V
  let dM : Module ℤ M := inferInstance
  let dN : Module ℤ N := inferInstance
  let cM : Module ℤ M := AddCommGroup.toIntModule M
  let cN : Module ℤ N := AddCommGroup.toIntModule N
  let K : Module ℤ M → Module ℤ N → Type (max w v z) := fun a b =>
    letI : Module ℤ M := a
    letI : Module ℤ N := b
    Balanced ℤ R M N
  let z : ∀ (a : Module ℤ M) (b : Module ℤ N), M → N → K a b := fun a b m n =>
    letI : Module ℤ M := a
    letI : Module ℤ N := b
    mk ℤ R M N m n
  have compare (a a' : Module ℤ M) (b b' : Module ℤ N)
      (ha : a = a') (hb : b = b') :
      {e : K a b ≃+ K a' b' // ∀ (m : M) (n : N), e (z a b m n) = z a' b' m n} := by
    cases ha
    cases hb
    exact ⟨AddEquiv.refl _, fun _ _ => rfl⟩
  exact compare dM cM dN cN (Subsingleton.elim _ _) (Subsingleton.elim _ _)

/-- Let k be a commutative ring, R a possibly noncommutative k-algebra,
M a right R-module with a compatible k-action commuting with R,
and V an additive commutative group with a k-module structure.
The additive coordinate equivalence compares the two presentations of
the integer-ground balanced quotient M ⊗_R (R ⊗[k] V).
It sends [m ⊗ x] to the corresponding [m ⊗ x] in the integral presentation. -/
def integralCoordinates : Balanced ℤ R M (R ⊗[k] V) ≃+
    GroundChange.integral R M (R ⊗[k] V) :=
  (integralCoordinateData k R M V).1

omit [Module k M] [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ M] in
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem integralCoordinates_mk (m : M) (x : R ⊗[k] V) :
    integralCoordinates k R M V (mk ℤ R M (R ⊗[k] V) m x) =
      GroundChange.integralMk R M (R ⊗[k] V) m x :=
  (integralCoordinateData k R M V).2 m x

/-- Let k be a commutative ring, R a possibly noncommutative k-algebra,
M a right R-module with a compatible k-action commuting with R,
and V an additive commutative group with a k-module structure.
The additive cancellation equivalence
M ⊗_R (R ⊗[k] V) ≅ M ⊗[k] V uses the integer-ground quotient
on the left. Its pure value is [m ⊗ (r ⊗ v)] ↦ (m r) ⊗ v,
and its inverse inserts 1 in the R factor. -/
def integralCancelEquiv : Balanced ℤ R M (R ⊗[k] V) ≃+ (M ⊗[k] V) :=
  letI : Module k (GroundChange.integral R M (R ⊗[k] V)) :=
    GroundChange.integralModule k R M (R ⊗[k] V)
  (integralCoordinates k R M V).trans
    ((GroundChange.equiv k R M (R ⊗[k] V)).symm.toAddEquiv.trans
      (cancelEquiv k R M V).toAddEquiv)

/-- Let k be a commutative ring, R a possibly noncommutative k-algebra,
M a right R-module with a compatible k-action commuting with R,
and V an additive commutative group with a k-module structure.
This is the integer-linear forward cancellation map
M ⊗_R (R ⊗[k] V) → M ⊗[k] V, with the source integer actions
as supplied by the tensor modules. It sends
[m ⊗ (r ⊗ v)] to (m r) ⊗ v. -/
def integralCancel : Balanced ℤ R M (R ⊗[k] V) →ₗ[ℤ] (M ⊗[k] V) :=
  ((integralCancelEquiv k R M V).toIntLinearEquiv
    (modM := inferInstance) (modM₂ := inferInstance)).toLinearMap

theorem integralCancel_mk (m : M) (x : R ⊗[k] V) :
    integralCancel k R M V (mk ℤ R M (R ⊗[k] V) m x) = absorb k R M V m x := by
  let : Module k (GroundChange.integral R M (R ⊗[k] V)) :=
    GroundChange.integralModule k R M (R ⊗[k] V)
  change cancelEquiv k R M V
      ((GroundChange.equiv k R M (R ⊗[k] V)).symm
        (integralCoordinates k R M V (mk ℤ R M (R ⊗[k] V) m x))) = _
  rw [integralCoordinates_mk, GroundChange.equiv_symm_mk]
  rfl

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem integralCancel_mk_tmul (m : M) (r : R) (v : V) :
    integralCancel k R M V (mk ℤ R M (R ⊗[k] V) m (r ⊗ₜ[k] v)) =
      (op r • m) ⊗ₜ[k] v := by
  rw [integralCancel_mk]
  rfl

/-- Let k be a commutative ring, R a possibly noncommutative k-algebra,
M a right R-module with a compatible k-action commuting with R,
and V an additive commutative group with a k-module structure.
The additive insertion map M ⊗[k] V → M ⊗_R (R ⊗[k] V)
sends m ⊗ v to [m ⊗ (1 ⊗ v)]. It is the inverse of integer-balanced
cancellation. -/
def integralInsert : M ⊗[k] V →+ Balanced ℤ R M (R ⊗[k] V) :=
  (integralCancelEquiv k R M V).symm.toAddMonoidHom

@[simp]
theorem integralInsert_tmul (m : M) (v : V) :
    integralInsert k R M V (m ⊗ₜ[k] v) =
      mk ℤ R M (R ⊗[k] V) m ((1 : R) ⊗ₜ[k] v) := by
  apply (integralCancelEquiv k R M V).injective
  change integralCancelEquiv k R M V
      ((integralCancelEquiv k R M V).symm (m ⊗ₜ[k] v)) =
    integralCancelEquiv k R M V (mk ℤ R M (R ⊗[k] V) m (1 ⊗ₜ[k] v))
  rw [AddEquiv.apply_symm_apply]
  have h : integralCancelEquiv k R M V (mk ℤ R M (R ⊗[k] V) m (1 ⊗ₜ[k] v)) =
      m ⊗ₜ[k] v := by
    change integralCancel k R M V (mk ℤ R M (R ⊗[k] V) m (1 ⊗ₜ[k] v)) = _
    rw [integralCancel_mk_tmul, op_one, one_smul]
  exact h.symm

theorem integralCancel_insert (x : M ⊗[k] V) :
    integralCancel k R M V (integralInsert k R M V x) = x :=
  (integralCancelEquiv k R M V).apply_symm_apply x

theorem integralInsert_cancel (q : Balanced ℤ R M (R ⊗[k] V)) :
    integralInsert k R M V (integralCancel k R M V q) = q :=
  (integralCancelEquiv k R M V).symm_apply_apply q

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem integralCancelEquiv_mk_tmul (m : M) (r : R) (v : V) :
    integralCancelEquiv k R M V (mk ℤ R M (R ⊗[k] V) m (r ⊗ₜ[k] v)) =
      (op r • m) ⊗ₜ[k] v :=
  integralCancel_mk_tmul k R M V m r v

@[simp]
theorem integralCancelEquiv_symm_tmul (m : M) (v : V) :
    (integralCancelEquiv k R M V).symm (m ⊗ₜ[k] v) =
      mk ℤ R M (R ⊗[k] V) m ((1 : R) ⊗ₜ[k] v) :=
  integralInsert_tmul k R M V m v

section Naturality

variable {M' : Type w'} [AddCommGroup M'] [Module k M'] [Module Rᵐᵒᵖ M']
  [SMulCommClass k Rᵐᵒᵖ M'] [IsScalarTower k Rᵐᵒᵖ M']
  {V' : Type z'} [AddCommGroup V'] [Module k V']

/-- Let k be a commutative ring, R a possibly noncommutative k-algebra,
M a right R-module with a compatible k-action commuting with R,
and V an additive commutative group with a k-module structure.
For k-linear f : M → M′ preserving the right R-action and
g : V → V′, with the same structures on the targets, the induced
integer-linear map sends [m ⊗ (r ⊗ v)] to
[f(m) ⊗ (r ⊗ g(v))]. The carrier universes of both targets may be independent. -/
def integralMap (f : M →ₗ[k] M') (g : V →ₗ[k] V')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op r • f m) :
    Balanced ℤ R M (R ⊗[k] V) →ₗ[ℤ] Balanced ℤ R M' (R ⊗[k] V') := by
  let f0 : M →ₗ[ℤ] M' := f.toAddMonoidHom.toIntLinearMap
  let g0 : (R ⊗[k] V) →ₗ[ℤ] (R ⊗[k] V') :=
    (TensorProduct.map (LinearMap.id : R →ₗ[k] R) g).toAddMonoidHom.toIntLinearMap
  have hf0 (r : R) (m : M) : f0 (op r • m) = op r • f0 m := by
    change f (op r • m) = op r • f m
    exact hf r m
  have hg0 (r : R) (x : R ⊗[k] V) : g0 (r • x) = r • g0 x := by
    change (TensorProduct.AlgebraTensorModule.lTensor R R g) (r • x) =
      r • (TensorProduct.AlgebraTensorModule.lTensor R R g) x
    exact (TensorProduct.AlgebraTensorModule.lTensor R R g).map_smul r x
  exact map f0 g0 hf0 hg0

omit [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ M]
  [SMulCommClass k Rᵐᵒᵖ M'] [IsScalarTower k Rᵐᵒᵖ M'] in
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem integralMap_mk_tmul (f : M →ₗ[k] M') (g : V →ₗ[k] V')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op r • f m)
    (m : M) (r : R) (v : V) :
    integralMap k R M V f g hf (mk ℤ R M (R ⊗[k] V) m (r ⊗ₜ[k] v)) =
      mk ℤ R M' (R ⊗[k] V') (f m) (r ⊗ₜ[k] g v) := by
  let f0 : M →ₗ[ℤ] M' := f.toAddMonoidHom.toIntLinearMap
  let g0 : (R ⊗[k] V) →ₗ[ℤ] (R ⊗[k] V') :=
    (TensorProduct.map (LinearMap.id : R →ₗ[k] R) g).toAddMonoidHom.toIntLinearMap
  have hf0 (r : R) (m : M) : f0 (op r • m) = op r • f0 m := by
    change f (op r • m) = op r • f m
    exact hf r m
  have hg0 (r : R) (x : R ⊗[k] V) : g0 (r • x) = r • g0 x := by
    change (TensorProduct.AlgebraTensorModule.lTensor R R g) (r • x) =
      r • (TensorProduct.AlgebraTensorModule.lTensor R R g) x
    exact (TensorProduct.AlgebraTensorModule.lTensor R R g).map_smul r x
  have hMap : map f0 g0 hf0 hg0 (mk ℤ R M (R ⊗[k] V) m (r ⊗ₜ[k] v)) =
      mk ℤ R M' (R ⊗[k] V') (f0 m) (g0 (r ⊗ₜ[k] v)) :=
    map_mk (k := ℤ) (R := R) (M := M) (N := R ⊗[k] V)
      (M' := M') (N' := R ⊗[k] V') f0 g0 hf0 hg0 m (r ⊗ₜ[k] v)
  have hWord : g0 (r ⊗ₜ[k] v) = r ⊗ₜ[k] g v := by
    change TensorProduct.map (LinearMap.id : R →ₗ[k] R) g (r ⊗ₜ[k] v) = r ⊗ₜ[k] g v
    exact TensorProduct.map_tmul (LinearMap.id : R →ₗ[k] R) g r v
  change map f0 g0 hf0 hg0 (mk ℤ R M (R ⊗[k] V) m (r ⊗ₜ[k] v)) = _
  exact hMap.trans (congrArg₂
    (fun (m' : M') (x : R ⊗[k] V') => mk ℤ R M' (R ⊗[k] V') m' x)
    (show f0 m = f m from rfl) hWord)

/-- Let k be a commutative ring, R a possibly noncommutative k-algebra,
M a right R-module with a compatible k-action commuting with R,
and V an additive commutative group with a k-module structure.
For k-linear f : M → M′ preserving the right R-action and
g : V → V′, the cancellation square commutes:
cancel′ ∘ integralMap(f, g) = (f ⊗ g) ∘ cancel.
The source and target carrier universes are independent. -/
theorem integralCancelEquiv_naturality (f : M →ₗ[k] M') (g : V →ₗ[k] V')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op r • f m)
    (q : Balanced ℤ R M (R ⊗[k] V)) :
    integralCancelEquiv k R M' V' (integralMap k R M V f g hf q) =
      TensorProduct.map f g (integralCancelEquiv k R M V q) := by
  have h : (integralCancelEquiv k R M' V').toAddMonoidHom.comp
      (integralMap k R M V f g hf).toAddMonoidHom =
      (TensorProduct.map f g).toAddMonoidHom.comp
        (integralCancelEquiv k R M V).toAddMonoidHom := by
    apply addHom_ext ℤ R M (R ⊗[k] V)
    intro m x
    induction x using TensorProduct.inductionOn with
    | tmul r v =>
        change integralCancelEquiv k R M' V'
            (integralMap k R M V f g hf (mk ℤ R M (R ⊗[k] V) m (r ⊗ₜ[k] v))) =
          TensorProduct.map f g
            (integralCancelEquiv k R M V (mk ℤ R M (R ⊗[k] V) m (r ⊗ₜ[k] v)))
        rw [integralMap_mk_tmul, integralCancelEquiv_mk_tmul,
          integralCancelEquiv_mk_tmul, TensorProduct.map_tmul, hf]
    | add x y hx hy =>
        simp only [map_add] at hx hy ⊢
        rw [hx, hy]
  exact DFunLike.congr_fun h q

end Naturality

end TensorProduct.Balanced
