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

public import MathlibExt.KTheory.Exact.K0.Functor
public import MathlibExt.CategoryTheory.Products.FunctorExact
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Exact-category K₀ of a product

The original exact projections and zero inclusions give an additive equivalence
between `K₀ (C × D)` and `K₀ C × K₀ D`. Its inverse adds the two actual inclusion
maps. The inverse identities use the original biproduct decomposition, with
independent category object and Hom universes.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v₁ u₁ v₂ u₂

namespace AlgebraicKTheory

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u₂) [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

private theorem zeroFunctor_isExact : (0 : C ⥤ D).IsExact := by
  let hZ : ∀ X : C, IsZero ((0 : C ⥤ D).obj X) :=
    (Functor.isZero_iff (0 : C ⥤ D)).mp (isZero_zero _)
  exact ⟨fun S _ => ExactCategory.isAdmissibleExact_of_splitting
    (ShortComplex.Splitting.ofIsZero (S.map (0 : C ⥤ D))
      (hZ S.X₁) (hZ S.X₂) (hZ S.X₃))⟩

local instance : (0 : C ⥤ D).IsExact := zeroFunctor_isExact C D
local instance : (0 : D ⥤ C).IsExact := zeroFunctor_isExact D C

/-- The original pairing of the identity on `C` with the zero functor to `D`. -/
noncomputable def K0.prodFstInclusionFunctor : C ⥤ C × D :=
  (𝟭 C).prod' (0 : C ⥤ D)

/-- The original pairing of the zero functor to `C` with the identity on `D`. -/
noncomputable def K0.prodSndInclusionFunctor : D ⥤ C × D :=
  (0 : D ⥤ C).prod' (𝟭 D)

instance K0.prodFstInclusionFunctorAdditive : (K0.prodFstInclusionFunctor C D).Additive := by
  unfold K0.prodFstInclusionFunctor
  infer_instance

instance K0.prodFstInclusionFunctorIsExact : (K0.prodFstInclusionFunctor C D).IsExact := by
  unfold K0.prodFstInclusionFunctor
  infer_instance

instance K0.prodSndInclusionFunctorAdditive : (K0.prodSndInclusionFunctor C D).Additive := by
  unfold K0.prodSndInclusionFunctor
  infer_instance

instance K0.prodSndInclusionFunctorIsExact : (K0.prodSndInclusionFunctor C D).IsExact := by
  unfold K0.prodSndInclusionFunctor
  infer_instance

/-- The original first projection map on exact-category `K₀`. -/
noncomputable def K0.prodFstHom : K0 (C × D) →+ K0 C :=
  K0.map (CategoryTheory.Prod.fst C D)

/-- The original second projection map on exact-category `K₀`. -/
noncomputable def K0.prodSndHom : K0 (C × D) →+ K0 D :=
  K0.map (CategoryTheory.Prod.snd C D)

/-- The first zero-inclusion map on exact-category `K₀`. -/
noncomputable def K0.prodFstInclusionHom : K0 C →+ K0 (C × D) :=
  K0.map (K0.prodFstInclusionFunctor C D)

/-- The second zero-inclusion map on exact-category `K₀`. -/
noncomputable def K0.prodSndInclusionHom : K0 D →+ K0 (C × D) :=
  K0.map (K0.prodSndInclusionFunctor C D)

/-- The whole forward product map is the pair of original exact projections. -/
noncomputable def K0.prodForwardHom : K0 (C × D) →+ K0 C × K0 D :=
  (K0.prodFstHom C D).prod (K0.prodSndHom C D)

/-- The whole inverse product map adds the two original zero inclusions. -/
noncomputable def K0.prodInverseHom : K0 C × K0 D →+ K0 (C × D) :=
  (K0.prodFstInclusionHom C D).coprod (K0.prodSndInclusionHom C D)

@[simp]
lemma K0.prodFstHom_mk (Z : C × D) :
    K0.prodFstHom C D (K0.mk Z) = K0.mk Z.1 :=
  K0.map_mk _ Z

@[simp]
lemma K0.prodSndHom_mk (Z : C × D) :
    K0.prodSndHom C D (K0.mk Z) = K0.mk Z.2 :=
  K0.map_mk _ Z

/-- The first inclusion retains the original object and its actual zero-functor image. -/
@[simp]
lemma K0.prodFstInclusionHom_mk (X : C) :
    K0.prodFstInclusionHom C D (K0.mk X) = K0.mk (X, (0 : C ⥤ D).obj X) :=
  K0.map_mk _ X

/-- The second inclusion retains its actual zero-functor image and original object. -/
@[simp]
lemma K0.prodSndInclusionHom_mk (Y : D) :
    K0.prodSndInclusionHom C D (K0.mk Y) = K0.mk ((0 : D ⥤ C).obj Y, Y) :=
  K0.map_mk _ Y

@[simp]
lemma K0.prodForwardHom_mk (Z : C × D) :
    K0.prodForwardHom C D (K0.mk Z) = (K0.mk Z.1, K0.mk Z.2) := by
  apply Prod.ext <;> simp [K0.prodForwardHom]

lemma K0.prodInverseHom_apply (a : K0 C) (b : K0 D) :
    K0.prodInverseHom C D (a, b) =
      K0.prodFstInclusionHom C D a + K0.prodSndInclusionHom C D b :=
  rfl

theorem K0.prodFstHom_comp_prodFstInclusionHom :
    (K0.prodFstHom C D).comp (K0.prodFstInclusionHom C D) = AddMonoidHom.id (K0 C) := by
  apply K0.hom_ext
  intro X
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
  change K0.map (CategoryTheory.Prod.fst C D)
    (K0.map (K0.prodFstInclusionFunctor C D) (K0.mk X)) = K0.mk X
  rw [K0.map_mk, K0.map_mk]
  rfl

theorem K0.prodSndHom_comp_prodSndInclusionHom :
    (K0.prodSndHom C D).comp (K0.prodSndInclusionHom C D) = AddMonoidHom.id (K0 D) := by
  apply K0.hom_ext
  intro Y
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
  change K0.map (CategoryTheory.Prod.snd C D)
    (K0.map (K0.prodSndInclusionFunctor C D) (K0.mk Y)) = K0.mk Y
  rw [K0.map_mk, K0.map_mk]
  rfl

theorem K0.prodFstHom_comp_prodSndInclusionHom :
    (K0.prodFstHom C D).comp (K0.prodSndInclusionHom C D) = 0 := by
  apply K0.hom_ext
  intro Y
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply]
  change K0.map (CategoryTheory.Prod.fst C D)
    (K0.map (K0.prodSndInclusionFunctor C D) (K0.mk Y)) = 0
  rw [K0.map_mk, K0.map_mk]
  exact K0.mk_eq_zero_of_isZero ((Functor.isZero_iff (0 : D ⥤ C)).mp (isZero_zero _) Y)

theorem K0.prodSndHom_comp_prodFstInclusionHom :
    (K0.prodSndHom C D).comp (K0.prodFstInclusionHom C D) = 0 := by
  apply K0.hom_ext
  intro X
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply]
  change K0.map (CategoryTheory.Prod.snd C D)
    (K0.map (K0.prodFstInclusionFunctor C D) (K0.mk X)) = 0
  rw [K0.map_mk, K0.map_mk]
  exact K0.mk_eq_zero_of_isZero ((Functor.isZero_iff (0 : C ⥤ D)).mp (isZero_zero _) X)

private noncomputable def decompositionIso (X : C) (Y : D) :
    (K0.prodFstInclusionFunctor C D).obj X ⊞
      (K0.prodSndInclusionFunctor C D).obj Y ≅ (X, Y) := by
  let P := (K0.prodFstInclusionFunctor C D).obj X
  let Q := (K0.prodSndInclusionFunctor C D).obj Y
  let B := P ⊞ Q
  let hC : IsZero ((0 : D ⥤ C).obj Y) :=
    (Functor.isZero_iff (0 : D ⥤ C)).mp (isZero_zero _) Y
  let hD : IsZero ((0 : C ⥤ D).obj X) :=
    (Functor.isZero_iff (0 : C ⥤ D)).mp (isZero_zero _) X
  letI : PreservesBinaryBiproduct P Q (CategoryTheory.Prod.fst C D) :=
    preservesBinaryBiproduct_of_preservesBiproduct (CategoryTheory.Prod.fst C D) P Q
  letI : PreservesBinaryBiproduct P Q (CategoryTheory.Prod.snd C D) :=
    preservesBinaryBiproduct_of_preservesBiproduct (CategoryTheory.Prod.snd C D) P Q
  let eC : B.1 ≅ X :=
    (CategoryTheory.Prod.fst C D).mapBiprod P Q ≪≫ (isoBiprodZero hC).symm
  let eD : B.2 ≅ Y :=
    (CategoryTheory.Prod.snd C D).mapBiprod P Q ≪≫ (isoZeroBiprod hD).symm
  exact eC.prod eD

/-- The two actual zero inclusions recover every original product `K₀` class. -/
theorem K0.prodInverseHom_comp_prodForwardHom :
    (K0.prodInverseHom C D).comp (K0.prodForwardHom C D) = AddMonoidHom.id (K0 (C × D)) := by
  apply K0.hom_ext
  intro Z
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, K0.prodForwardHom_mk,
    K0.prodInverseHom_apply]
  change K0.map (K0.prodFstInclusionFunctor C D) (K0.mk Z.1) +
    K0.map (K0.prodSndInclusionFunctor C D) (K0.mk Z.2) = K0.mk Z
  rw [K0.map_mk, K0.map_mk, ← K0.mk_biprod]
  exact (K0.mk_congr_of_iso (decompositionIso C D Z.1 Z.2)).trans
    (K0.mk_congr_of_iso (CategoryTheory.prod.etaIso Z))

/-- The two original projections recover every pair of exact-category `K₀` values. -/
theorem K0.prodForwardHom_comp_prodInverseHom :
    (K0.prodForwardHom C D).comp (K0.prodInverseHom C D) = AddMonoidHom.id (K0 C × K0 D) := by
  apply AddMonoidHom.ext
  rintro ⟨a, b⟩
  apply Prod.ext
  · change K0.prodFstHom C D
      (K0.prodFstInclusionHom C D a + K0.prodSndInclusionHom C D b) = a
    rw [map_add]
    change ((K0.prodFstHom C D).comp (K0.prodFstInclusionHom C D)) a +
      ((K0.prodFstHom C D).comp (K0.prodSndInclusionHom C D)) b = a
    rw [K0.prodFstHom_comp_prodFstInclusionHom, K0.prodFstHom_comp_prodSndInclusionHom]
    simp
  · change K0.prodSndHom C D
      (K0.prodFstInclusionHom C D a + K0.prodSndInclusionHom C D b) = b
    rw [map_add]
    change ((K0.prodSndHom C D).comp (K0.prodFstInclusionHom C D)) a +
      ((K0.prodSndHom C D).comp (K0.prodSndInclusionHom C D)) b = b
    rw [K0.prodSndHom_comp_prodFstInclusionHom, K0.prodSndHom_comp_prodSndInclusionHom]
    simp

/-- The additive product formula for the original exact-category `K₀` carriers. -/
noncomputable def K0.prodEquiv : K0 (C × D) ≃+ K0 C × K0 D where
  toFun := K0.prodForwardHom C D
  invFun := K0.prodInverseHom C D
  left_inv x := DFunLike.congr_fun (K0.prodInverseHom_comp_prodForwardHom C D) x
  right_inv x := DFunLike.congr_fun (K0.prodForwardHom_comp_prodInverseHom C D) x
  map_add' := map_add _

/-- The product equivalence uses the two original projections on generators. -/
@[simp]
lemma K0.prodEquiv_mk (Z : C × D) :
    K0.prodEquiv C D (K0.mk Z) = (K0.mk Z.1, K0.mk Z.2) :=
  K0.prodForwardHom_mk C D Z

/-- The inverse product equivalence adds the two original zero-inclusion maps. -/
lemma K0.prodEquiv_symm_apply (a : K0 C) (b : K0 D) :
    (K0.prodEquiv C D).symm (a, b) =
      K0.prodFstInclusionHom C D a + K0.prodSndInclusionHom C D b :=
  rfl

/-- The inverse product equivalence recombines every original pair of object classes. -/
@[simp]
lemma K0.prodEquiv_symm_mk (X : C) (Y : D) :
    (K0.prodEquiv C D).symm (K0.mk X, K0.mk Y) = K0.mk (X, Y) := by
  apply (K0.prodEquiv C D).injective
  rw [AddEquiv.apply_symm_apply, K0.prodEquiv_mk]

end AlgebraicKTheory
