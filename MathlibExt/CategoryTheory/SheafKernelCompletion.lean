/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Kernel-adic completion in the actual ring-sheaf category

Each finite quotient is sheafified before taking the inverse limit.
Consequently the construction uses the ideal-sheaf power quotient;
it makes no identification of its sections with a quotient by powers
of the global-section ideal on an arbitrary object.

This is the completion operation in Scholze, arXiv:1205.3463v2,
Definitions 6.1 and 6.8. The objects, quotient maps and projections below
are native Mathlib sheafifications and limits, Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.SheafKernelCompletion

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R S : Sheaf J CommRingCat.{1}) (θ : R ⟶ S)

def kernelIdeal (U : Cᵒᵖ) : Ideal (R.obj.obj U) :=
  RingHom.ker (θ.hom.app U).hom

theorem map_kernel_le {U V : Cᵒᵖ} (f : U ⟶ V) :
    (kernelIdeal R S θ U).map (R.obj.map f).hom ≤ kernelIdeal R S θ V := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha
  change (θ.hom.app V).hom ((R.obj.map f).hom a) = 0
  have h := congrArg (fun g => g.hom a) (θ.hom.naturality f)
  change (θ.hom.app V).hom ((R.obj.map f).hom a) =
    (S.obj.map f).hom ((θ.hom.app U).hom a) at h
  rw [h]
  change (θ.hom.app U).hom a = 0 at ha
  simpa using congrArg (S.obj.map f).hom ha

theorem map_power_le {U V : Cᵒᵖ} (f : U ⟶ V) (n : ℕ) :
    ((kernelIdeal R S θ U) ^ (n + 1)).map (R.obj.map f).hom ≤
      (kernelIdeal R S θ V) ^ (n + 1) := by
  rw [Ideal.map_pow]
  exact pow_le_pow_left' (map_kernel_le R S θ f) (n + 1)

def rawQuotient (n : ℕ) : Cᵒᵖ ⥤ CommRingCat.{1} where
  obj U := CommRingCat.of ((R.obj.obj U) ⧸ (kernelIdeal R S θ U) ^ (n + 1))
  map {U V} f := CommRingCat.ofHom
    (Ideal.Quotient.lift _
      ((Ideal.Quotient.mk ((kernelIdeal R S θ V) ^ (n + 1))).comp (R.obj.map f).hom)
      (by
        intro a ha
        exact Ideal.Quotient.eq_zero_iff_mem.mpr
          (map_power_le R S θ f n (Ideal.mem_map_of_mem _ ha))))
  map_id U := by
    ext a
    change Ideal.Quotient.mk _ ((R.obj.map (𝟙 U)).hom a) = Ideal.Quotient.mk _ a
    rw [_root_.CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    ext a
    change Ideal.Quotient.mk _ ((R.obj.map (f ≫ g)).hom a) =
      Ideal.Quotient.mk _ ((R.obj.map g).hom ((R.obj.map f).hom a))
    rw [_root_.CategoryTheory.Functor.map_comp]
    rfl

def rawUnit (n : ℕ) : R.obj ⟶ rawQuotient R S θ n where
  app U := CommRingCat.ofHom (Ideal.Quotient.mk ((kernelIdeal R S θ U) ^ (n + 1)))
  naturality {U V} f := by ext a; rfl

def rawReduction {n m : ℕ} (h : n ≤ m) :
    rawQuotient R S θ m ⟶ rawQuotient R S θ n where
  app U := CommRingCat.ofHom
    (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)))
  naturality {U V} f := by
    ext a
    refine Quotient.inductionOn a (fun x => ?_)
    rfl

theorem rawReduction_refl (n : ℕ) :
    rawReduction R S θ (le_refl n) = 𝟙 (rawQuotient R S θ n) := by
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  exact Ideal.Quotient.factor_eq

theorem rawReduction_comp {n m k : ℕ} (h : n ≤ m) (j : m ≤ k) :
    rawReduction R S θ j ≫ rawReduction R S θ h = rawReduction R S θ (h.trans j) := by
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  exact Ideal.Quotient.factor_comp
    (Ideal.pow_le_pow_right (Nat.add_le_add_right j 1))
    (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

def rawTower : ℕᵒᵖ ⥤ (Cᵒᵖ ⥤ CommRingCat.{1}) where
  obj n := rawQuotient R S θ n.unop
  map f := rawReduction R S θ (leOfHom f.unop)
  map_id n := by
    exact rawReduction_refl R S θ n.unop
  map_comp f g := by
    exact (rawReduction_comp R S θ (leOfHom g.unop) (leOfHom f.unop)).symm

def rawCone : Cone (rawTower R S θ) where
  pt := R.obj
  π :=
    { app n := rawUnit R S θ n.unop
      naturality {n m} f := by
        apply NatTrans.ext
        funext U
        ext a
        rfl }

variable [HasSheafify J CommRingCat.{1}]

abbrev quotientSheaf (n : ℕ) : Sheaf J CommRingCat.{1} :=
  (presheafToSheaf J CommRingCat.{1}).obj (rawQuotient R S θ n)

def quotientUnit (n : ℕ) : R ⟶ quotientSheaf R S θ n :=
  inv ((sheafificationAdjunction J CommRingCat.{1}).counit.app R) ≫
    (presheafToSheaf J CommRingCat.{1}).map (rawUnit R S θ n)

abbrev tower : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{1} :=
  rawTower R S θ ⋙ presheafToSheaf J CommRingCat.{1}

/-- Completion is the native inverse limit of the sheafified finite quotients. -/
abbrev completion : Sheaf J CommRingCat.{1} := limit (tower R S θ)

def projection (n : ℕ) : completion R S θ ⟶ quotientSheaf R S θ n :=
  limit.π (tower R S θ) (op n)

/-- The unit is the canonical quotient cone after native sheafification. -/
def completionUnit : R ⟶ completion R S θ :=
  inv ((sheafificationAdjunction J CommRingCat.{1}).counit.app R) ≫
    limit.lift (tower R S θ)
      ((presheafToSheaf J CommRingCat.{1}).mapCone (rawCone R S θ))

@[reassoc (attr := simp)] theorem completionUnit_projection (n : ℕ) :
    completionUnit R S θ ≫ projection R S θ n = quotientUnit R S θ n := by
  unfold completionUnit projection quotientUnit
  exact (_root_.CategoryTheory.Category.assoc _ _ _).trans
    (congrArg (fun f => inv ((sheafificationAdjunction J CommRingCat.{1}).counit.app R) ≫ f)
      (limit.lift_π ((presheafToSheaf J CommRingCat.{1}).mapCone (rawCone R S θ)) (op n)))

def rawKernelFactor : rawQuotient R S θ 0 ⟶ S.obj where
  app U := CommRingCat.ofHom
    (Ideal.Quotient.lift _ (θ.hom.app U).hom
      (by intro a ha; simpa [kernelIdeal] using ha))
  naturality {U V} f := by
    ext a
    refine Quotient.inductionOn a (fun x => ?_)
    exact congrArg (fun g => g.hom x) (θ.hom.naturality f)

def kernelFactor : quotientSheaf R S θ 0 ⟶ S :=
  ((sheafificationAdjunction J CommRingCat.{1}).homEquiv
    (rawQuotient R S θ 0) S).symm (rawKernelFactor R S θ)

/-- The completed map is its first quotient projection followed by the native kernel factor. -/
def completedTheta : completion R S θ ⟶ S :=
  projection R S θ 0 ≫ kernelFactor R S θ

end MathlibExt.CategoryTheory.SheafKernelCompletion
