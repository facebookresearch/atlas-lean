/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.Normalized
public import Mathlib.Algebra.Algebra.Unitization

/-!
# Unitization maps and the reduced ground module

Let `k` be a commutative ring and `A` a nonunital ground algebra. Its unitization `A⁺ = k ⊕ A`
has augmentation `(r,a) ↦ r`, scalar section `r ↦ (r,0)`, and nonunital inclusion `a ↦ (0,a)`.
The scalar projector is `(r,a) ↦ (r,0)`.

A nonunital map `f : A → B` extends to `(r,a) ↦ (r,f(a))`, with independent algebra-carrier
universes. The ground-module quotient `A⁺ / k·1` is linearly equivalent to `A` by the second
coordinate; the inverse takes `a` to the class of its nonunital inclusion. This comparison is
a quotient of ground modules.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The scalar augmentation of a unitization.

For `A⁺ = k ⊕ A`, the `k`-algebra homomorphism to `k` is the first projection `(r,a) ↦ r`. -/
abbrev unitizationAugmentation : Unitization k A →ₐ[k] k := Unitization.fstHom k A

/-- The scalar section of a unitization augmentation.

The `k`-algebra map `k → A⁺` sends `r` to `(r,0)`, the scalar multiple of the external unit. -/
abbrev unitizationScalarSection : k →ₐ[k] Unitization k A := Algebra.ofId k (Unitization k A)

/-- The scalar projector of a unitization.

Augmentation followed by its scalar section is the algebra endomorphism `(r,a) ↦ (r,0)` of
`A⁺`. -/
def unitizationScalarProjector : Unitization k A →ₐ[k] Unitization k A :=
  (unitizationScalarSection k A).comp (unitizationAugmentation k A)

/-- The coordinate formula for unitization scalar projection.

The scalar projector sends `x ∈ A⁺` to `Unitization.inl x.fst`. -/
@[simp]
theorem unitizationScalarProjector_apply (x : Unitization k A) :
    unitizationScalarProjector k A x = Unitization.inl x.fst := rfl

/-- Idempotence of the unitization scalar algebra projector.

Composing the scalar projector with itself gives the same algebra endomorphism. -/
theorem unitizationScalarProjector_idempotent :
    (unitizationScalarProjector k A).comp (unitizationScalarProjector k A) =
      unitizationScalarProjector k A := by
  apply AlgHom.ext
  intro x
  rfl

/-- The unitization of a nonunital algebra homomorphism.

For `f : A →ₙₐ[k] B`, the universal unitization map is a unital `k`-algebra homomorphism `A⁺ →
B⁺` sending `(r,a)` to `(r,f(a))`. -/
def unitizationMap {B : Type w} [NonUnitalRing B] [Module k B]
    [IsScalarTower k B B] [SMulCommClass k B B] (f : A →ₙₐ[k] B) :
    Unitization k A →ₐ[k] Unitization k B :=
  Unitization.lift ((Unitization.inrNonUnitalAlgHom k B).comp f)

/-- The ideal-coordinate formula for a unitization map.

The lifted map of `f` sends the nonunital inclusion of `a` to the inclusion of `f(a)`. -/
@[simp]
theorem unitizationMap_inr {B : Type w} [NonUnitalRing B] [Module k B]
    [IsScalarTower k B B] [SMulCommClass k B B] (f : A →ₙₐ[k] B) (a : A) :
    unitizationMap k A f (Unitization.inr a) = Unitization.inr (f a) := by
  simp [unitizationMap, Unitization.lift]

/-- The scalar-coordinate formula for a unitization map.

The lifted map of `f : A → B` retains each scalar element `Unitization.inl r`. -/
@[simp]
theorem unitizationMap_inl {B : Type w} [NonUnitalRing B] [Module k B]
    [IsScalarTower k B B] [SMulCommClass k B B] (f : A →ₙₐ[k] B) (r : k) :
    unitizationMap k A f (Unitization.inl r) = Unitization.inl r := by
  simpa only [Unitization.algebraMap_eq_inl] using (unitizationMap k A f).commutes r

/-- The full coordinate formula for a unitization homomorphism.

For independently sized `A` and `B`, the extension of `f : A → B` sends `x = (x.fst,x.snd)` to
`(x.fst,f(x.snd))`. -/
theorem unitizationMap_apply {B : Type w} [NonUnitalRing B] [Module k B]
    [IsScalarTower k B B] [SMulCommClass k B B] (f : A →ₙₐ[k] B) (x : Unitization k A) :
    unitizationMap k A f x = Unitization.mk (x.fst, f x.snd) := by
  conv_lhs =>
    rw [← Unitization.inl_fst_add_inr_snd_eq x, map_add,
      unitizationMap_inl, unitizationMap_inr]
  apply Unitization.ext
  · simp only [Unitization.fst_add, Unitization.fst_inl, Unitization.fst_inr, add_zero]
  · simp only [Unitization.snd_add, Unitization.snd_inl, Unitization.snd_inr, zero_add]

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- The unit span in the kernel of unitization's second projection.

The ground submodule spanned by the external unit of `A⁺` is contained in the kernel of `(r,a)
↦ a`. -/
theorem unitSubmodule_le_ker_unitizationSnd :
    ModuleCat.Algebra.Hochschild.unitSubmodule k (Unitization k A) ≤
      LinearMap.ker (Unitization.sndHom k k A) := by
  apply Submodule.span_le.mpr
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  change (1 : Unitization k A).snd = 0
  rfl

/-- The reduced unitization map to its nonunital summand.

The second projection descends to a ground-linear map `A⁺ / k·1 → A` sending the class of
`(r,a)` to `a`. -/
def unitizationQuotientToOriginal :
    ModuleCat.Algebra.Hochschild.quotientCarrier k (Unitization k A) →ₗ[k] A :=
  (ModuleCat.Algebra.Hochschild.unitSubmodule k (Unitization k A)).liftQ
    (Unitization.sndHom k k A) (unitSubmodule_le_ker_unitizationSnd k A)

/-- The inclusion into the reduced unitization ground module.

The ground-linear map `A → A⁺ / k·1` sends `a` to the class of `Unitization.inr a`. -/
def originalToUnitizationQuotient :
    A →ₗ[k] ModuleCat.Algebra.Hochschild.quotientCarrier k (Unitization k A) :=
  (ModuleCat.Algebra.Hochschild.unitSubmodule k (Unitization k A)).mkQ.comp
    (Unitization.inrHom k k A)

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- The second-coordinate formula on a reduced unitization class.

The reduced ground-module map sends the class of `x ∈ A⁺` to `x.snd`. -/
theorem unitizationQuotientToOriginal_mkQ (x : Unitization k A) :
    unitizationQuotientToOriginal k A
      ((ModuleCat.Algebra.Hochschild.unitSubmodule k (Unitization k A)).mkQ x) = x.snd := rfl

/-- Removal of the scalar coordinate in the unitization quotient.

The classes of `x ∈ A⁺` and `Unitization.inr x.snd` are equal in the ground-module quotient by
`k·1`. -/
theorem unitizationQuotient_mkQ_eq_inr (x : Unitization k A) :
    (ModuleCat.Algebra.Hochschild.unitSubmodule k (Unitization k A)).mkQ x =
      (ModuleCat.Algebra.Hochschild.unitSubmodule k (Unitization k A)).mkQ (Unitization.inr x.snd) := by
  have hOne : (ModuleCat.Algebra.Hochschild.unitSubmodule k (Unitization k A)).mkQ 1 = 0 :=
    (Submodule.Quotient.mk_eq_zero
      (ModuleCat.Algebra.Hochschild.unitSubmodule k (Unitization k A))).mpr
      (ModuleCat.Algebra.Hochschild.one_mem_unitSubmodule k (Unitization k A))
  have hScalar : Unitization.inl x.fst = x.fst • (1 : Unitization k A) := by
    rw [← Unitization.algebraMap_eq_inl]
    exact Algebra.algebraMap_eq_smul_one x.fst
  conv_lhs =>
    rw [← Unitization.inl_fst_add_inr_snd_eq x, map_add, hScalar, map_smul,
      hOne, smul_zero, zero_add]

/-- The reduced unitization ground-module equivalence.

The quotient `A⁺ / k·1` is `k`-linearly equivalent to `A`, with forward map the second
coordinate and inverse the class of the nonunital inclusion. -/
def unitizationQuotientEquiv :
    ModuleCat.Algebra.Hochschild.quotientCarrier k (Unitization k A) ≃ₗ[k] A where
  toLinearMap := unitizationQuotientToOriginal k A
  invFun := originalToUnitizationQuotient k A
  left_inv x := by
    refine Submodule.Quotient.induction_on _ x ?_
    intro a
    change (ModuleCat.Algebra.Hochschild.unitSubmodule k (Unitization k A)).mkQ
        (Unitization.inr a.snd) = _
    exact (unitizationQuotient_mkQ_eq_inr k A a).symm
  right_inv a := rfl

end ModuleCat.Algebra.Hochschild.NonUnital
