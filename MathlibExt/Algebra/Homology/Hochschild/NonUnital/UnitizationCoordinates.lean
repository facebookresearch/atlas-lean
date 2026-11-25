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
# unitization maps and its reduced ground module

The source unitization k⊕A is native Unitization k A. Its augmentation,
scalar section, nonunital inclusion and lifted original maps are retained.
The reduced quotient by the span of 1 is canonically the original A.
This is a ground-module comparison, not an algebra quotient or a cyclic
operator on arbitrary normalized coefficient levels.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The original unitization augmentation is the native first projection. -/
abbrev unitizationAugmentation : Unitization k A →ₐ[k] k := Unitization.fstHom k A

/-- The original scalar section inserts the external unit. -/
abbrev unitizationScalarSection : k →ₐ[k] Unitization k A := Algebra.ofId k (Unitization k A)

/-- The scalar projector is augmentation followed by its original scalar section. -/
def unitizationScalarProjector : Unitization k A →ₐ[k] Unitization k A :=
  (unitizationScalarSection k A).comp (unitizationAugmentation k A)

@[simp]
theorem unitizationScalarProjector_apply (x : Unitization k A) :
    unitizationScalarProjector k A x = Unitization.inl x.fst := rfl

theorem unitizationScalarProjector_idempotent :
    (unitizationScalarProjector k A).comp (unitizationScalarProjector k A) =
      unitizationScalarProjector k A := by
  apply AlgHom.ext
  intro x
  rfl

/-- The original nonunital algebra map lifts through the unitization property. -/
def unitizationMap {B : Type w} [NonUnitalRing B] [Module k B]
    [IsScalarTower k B B] [SMulCommClass k B B] (f : A →ₙₐ[k] B) :
    Unitization k A →ₐ[k] Unitization k B :=
  Unitization.lift ((Unitization.inrNonUnitalAlgHom k B).comp f)

@[simp]
theorem unitizationMap_inr {B : Type w} [NonUnitalRing B] [Module k B]
    [IsScalarTower k B B] [SMulCommClass k B B] (f : A →ₙₐ[k] B) (a : A) :
    unitizationMap k A f (Unitization.inr a) = Unitization.inr (f a) := by
  simp [unitizationMap, Unitization.lift]

@[simp]
theorem unitizationMap_inl {B : Type w} [NonUnitalRing B] [Module k B]
    [IsScalarTower k B B] [SMulCommClass k B B] (f : A →ₙₐ[k] B) (r : k) :
    unitizationMap k A f (Unitization.inl r) = Unitization.inl r := by
  simpa only [Unitization.algebraMap_eq_inl] using (unitizationMap k A f).commutes r

/-- Independent original algebra carriers keep both native unitization coordinates. -/
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
/-- The ground unit span is killed by the second projection. -/
theorem unitSubmodule_le_ker_unitizationSnd :
    ModuleCat.Algebra.Hochschild.unitSubmodule k (Unitization k A) ≤
      LinearMap.ker (Unitization.sndHom k k A) := by
  apply Submodule.span_le.mpr
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  change (1 : Unitization k A).snd = 0
  rfl

/-- The original second projection descends through precisely the k·1 quotient. -/
def unitizationQuotientToOriginal :
    ModuleCat.Algebra.Hochschild.quotientCarrier k (Unitization k A) →ₗ[k] A :=
  (ModuleCat.Algebra.Hochschild.unitSubmodule k (Unitization k A)).liftQ
    (Unitization.sndHom k k A) (unitSubmodule_le_ker_unitizationSnd k A)

/-- The inverse uses the original nonunital inclusion followed by the quotient projection. -/
def originalToUnitizationQuotient :
    A →ₗ[k] ModuleCat.Algebra.Hochschild.quotientCarrier k (Unitization k A) :=
  (ModuleCat.Algebra.Hochschild.unitSubmodule k (Unitization k A)).mkQ.comp
    (Unitization.inrHom k k A)

omit [IsScalarTower k A A] [SMulCommClass k A A] in
theorem unitizationQuotientToOriginal_mkQ (x : Unitization k A) :
    unitizationQuotientToOriginal k A
      ((ModuleCat.Algebra.Hochschild.unitSubmodule k (Unitization k A)).mkQ x) = x.snd := rfl

/-- The scalar coordinate vanishes in exactly the source's reduced ground quotient. -/
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

/-- The source reduced unitization carrier is the original nonunital algebra as a ground module. -/
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
