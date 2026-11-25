/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.Isomorphism

public import MathlibExt.Algebra.Category.ModuleCat.FlatScalarExtensionTorResolvedNaturality
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.CompositionNaturality
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.BifunctorBalance
public import MathlibExt.Algebra.Category.ModuleCat.LocalizationColimits
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Flat.Localization

/-!
# Flat base change and localization of Tor

Flat extension of scalars commutes with derived tensor in every degree for
arbitrary modules in a common universe larger than both ring universes.
The comparison uses the scalar-extended projective resolution and the
tensor base-change equivalence. Localization specializes this comparison
using `IsLocalization.flat`.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct ModuleCat.UniverseTensor ChangeOfRings

namespace ModuleCat.UniverseTensor

universe u v w

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S]

/-- Scalar extension distributes over the actual native tensor carriers. -/
def scalarExtensionTensorIso (f : R →+* S)
    (M X : ModuleCat.{max u v w} R) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) := tensorStructure.{u, max v w}
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} S) := tensorStructure.{v, max u w}
    letI : MonoidalCategory (ModuleCat.{max u v w} R) := monoidalCategory.{u, max v w}
    letI : MonoidalCategory (ModuleCat.{max u v w} S) := monoidalCategory.{v, max u w}
    (extendScalars.{u, v, max u v w} f).obj (M ⊗ X) ≅
      (extendScalars.{u, v, max u v w} f).obj M ⊗
        (extendScalars.{u, v, max u v w} f).obj X := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) := tensorStructure.{u, max v w}
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} S) := tensorStructure.{v, max u w}
  letI : MonoidalCategory (ModuleCat.{max u v w} R) := monoidalCategory.{u, max v w}
  letI : MonoidalCategory (ModuleCat.{max u v w} S) := monoidalCategory.{v, max u w}
  letI : Algebra R S := f.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.distribBaseChange R S M X).toModuleIso

/-- The actual tensor base-change comparison retains both coefficient maps. -/
theorem scalarExtensionTensorIso_hom_naturality (f : R →+* S)
    {M M' X X' : ModuleCat.{max u v w} R} (g : M ⟶ M') (h : X ⟶ X') :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) := tensorStructure.{u, max v w}
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} S) := tensorStructure.{v, max u w}
    letI : MonoidalCategory (ModuleCat.{max u v w} R) := monoidalCategory.{u, max v w}
    letI : MonoidalCategory (ModuleCat.{max u v w} S) := monoidalCategory.{v, max u w}
    (extendScalars.{u, v, max u v w} f).map (g ⊗ₘ h) ≫
        (scalarExtensionTensorIso R S f M' X').hom =
      (scalarExtensionTensorIso R S f M X).hom ≫
        ((extendScalars.{u, v, max u v w} f).map g ⊗ₘ
          (extendScalars.{u, v, max u v w} f).map h) := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} R) := tensorStructure.{u, max v w}
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} S) := tensorStructure.{v, max u w}
  let : MonoidalCategory (ModuleCat.{max u v w} R) := monoidalCategory.{u, max v w}
  let : MonoidalCategory (ModuleCat.{max u v w} S) := monoidalCategory.{v, max u w}
  let : Algebra R S := f.toAlgebra
  apply ModuleCat.hom_ext
  change (TensorProduct.AlgebraTensorModule.distribBaseChange R S M' X').toLinearMap ∘ₗ
      (TensorProduct.map g.hom h.hom).baseChange S =
    TensorProduct.map (g.hom.baseChange S) (h.hom.baseChange S) ∘ₗ
      (TensorProduct.AlgebraTensorModule.distribBaseChange R S M X).toLinearMap
  apply TensorProduct.AlgebraTensorModule.curry_injective
  apply LinearMap.ext
  intro a
  apply TensorProduct.curry_injective
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro x
  rfl

/-- Tensor base change as a natural isomorphism in the resolved variable. -/
def scalarExtensionTensorNatIso (f : R →+* S) (M : ModuleCat.{max u v w} R) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) := tensorStructure.{u, max v w}
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} S) := tensorStructure.{v, max u w}
    letI : MonoidalCategory (ModuleCat.{max u v w} R) := monoidalCategory.{u, max v w}
    letI : MonoidalCategory (ModuleCat.{max u v w} S) := monoidalCategory.{v, max u w}
    (tensoringLeft (ModuleCat.{max u v w} R)).obj M ⋙
        extendScalars.{u, v, max u v w} f ≅
      extendScalars.{u, v, max u v w} f ⋙
        (tensoringLeft (ModuleCat.{max u v w} S)).obj
          ((extendScalars.{u, v, max u v w} f).obj M) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) := tensorStructure.{u, max v w}
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} S) := tensorStructure.{v, max u w}
  letI : MonoidalCategory (ModuleCat.{max u v w} R) := monoidalCategory.{u, max v w}
  letI : MonoidalCategory (ModuleCat.{max u v w} S) := monoidalCategory.{v, max u w}
  refine NatIso.ofComponents (fun X => scalarExtensionTensorIso R S f M X) ?_
  intro X Y h
  have hw := scalarExtensionTensorIso_hom_naturality R S f (𝟙 M) h
  rw [(extendScalars.{u, v, max u v w} f).map_id] at hw
  change (extendScalars.{u, v, max u v w} f).map (((tensoringLeft _).obj M).map h) ≫
      (scalarExtensionTensorIso R S f M Y).hom =
    (scalarExtensionTensorIso R S f M X).hom ≫
      ((tensoringLeft _).obj ((extendScalars.{u, v, max u v w} f).obj M)).map
        ((extendScalars.{u, v, max u v w} f).map h)
  exact hw

section FlatChange

variable [Algebra R S] [Module.Flat R S]

/-- The genuine scalar-extended projective resolution compares left
derivation before and after flat scalar extension of the resolved object. -/
def flatScalarExtensionDerivedPrecompIso
    (L : ModuleCat.{max u v w} S ⥤ ModuleCat.{max u v w} S) [L.Additive] (q : ℕ) :
    (extendScalars.{u, v, max u v w} (algebraMap R S) ⋙ L).leftDerived q ≅
      extendScalars.{u, v, max u v w} (algebraMap R S) ⋙ L.leftDerived q := by
  let F : ModuleCat.{max u v w} R ⥤ ModuleCat.{max u v w} S :=
    extendScalars.{u, v, max u v w} (algebraMap R S)
  let G : ModuleCat.{max u v w} S ⥤ ModuleCat.{max u v w} R :=
    restrictScalars.{max u v w, u, v} (algebraMap R S)
  letI : G.PreservesEpimorphisms :=
    { preserves := fun g _ => (ModuleCat.epi_iff_surjective _).mpr
        ((ModuleCat.epi_iff_surjective g).mp inferInstance) }
  letI : F.PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (extendRestrictScalarsAdj.{max u v w, u, v} (algebraMap R S))
  letI : F.PreservesHomology := preservesHomology_extendScalars_of_flat.{u, v, w}
    (algebraMap R S) (by rw [RingHom.flat_algebraMap_iff]; infer_instance)
  exact Functor.leftDerivedPrecompIso F L q

/-- The genuine resolved-object comparison is natural in the additive
functor being derived. -/
theorem flatScalarExtensionDerivedPrecompIso_hom_naturality_functor
    {L₁ L₂ : ModuleCat.{max u v w} S ⥤ ModuleCat.{max u v w} S}
    [L₁.Additive] [L₂.Additive] (β : L₁ ⟶ L₂)
    (X : ModuleCat.{max u v w} R) (q : ℕ) :
    (NatTrans.leftDerived
        (Functor.whiskerLeft (extendScalars.{u, v, max u v w} (algebraMap R S)) β) q).app X ≫
        (flatScalarExtensionDerivedPrecompIso R S L₂ q).hom.app X =
      (flatScalarExtensionDerivedPrecompIso R S L₁ q).hom.app X ≫
        (NatTrans.leftDerived β q).app
          ((extendScalars.{u, v, max u v w} (algebraMap R S)).obj X) := by
  let F : ModuleCat.{max u v w} R ⥤ ModuleCat.{max u v w} S :=
    extendScalars.{u, v, max u v w} (algebraMap R S)
  let G : ModuleCat.{max u v w} S ⥤ ModuleCat.{max u v w} R :=
    restrictScalars.{max u v w, u, v} (algebraMap R S)
  let : G.PreservesEpimorphisms :=
    { preserves := fun g _ => (ModuleCat.epi_iff_surjective _).mpr
        ((ModuleCat.epi_iff_surjective g).mp inferInstance) }
  let : F.PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (extendRestrictScalarsAdj.{max u v w, u, v} (algebraMap R S))
  let : F.PreservesHomology := preservesHomology_extendScalars_of_flat.{u, v, w}
    (algebraMap R S) (by rw [RingHom.flat_algebraMap_iff]; infer_instance)
  have h := Functor.leftDerivedPrecompIso_hom_naturality_functor F β q
  exact congrArg (fun η => η.app X) h

/-- Flat scalar extension commutes with the ordered native Tor functor,
as a natural isomorphism in the second coefficient. -/
def flatScalarExtensionTorBaseChangeNatIso (M : ModuleCat.{max u v w} R) (q : ℕ) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) := tensorStructure.{u, max v w}
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} S) := tensorStructure.{v, max u w}
    letI : MonoidalCategory (ModuleCat.{max u v w} R) := monoidalCategory.{u, max v w}
    letI : MonoidalCategory (ModuleCat.{max u v w} S) := monoidalCategory.{v, max u w}
    letI : MonoidalPreadditive (ModuleCat.{max u v w} R) := monoidalPreadditive.{u, max v w}
    letI : MonoidalPreadditive (ModuleCat.{max u v w} S) := monoidalPreadditive.{v, max u w}
    (Tor (ModuleCat.{max u v w} R) q).obj M ⋙
        extendScalars.{u, v, max u v w} (algebraMap R S) ≅
      extendScalars.{u, v, max u v w} (algebraMap R S) ⋙
        (Tor (ModuleCat.{max u v w} S) q).obj
          ((extendScalars.{u, v, max u v w} (algebraMap R S)).obj M) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) := tensorStructure.{u, max v w}
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} S) := tensorStructure.{v, max u w}
  letI : MonoidalCategory (ModuleCat.{max u v w} R) := monoidalCategory.{u, max v w}
  letI : MonoidalCategory (ModuleCat.{max u v w} S) := monoidalCategory.{v, max u w}
  letI : MonoidalPreadditive (ModuleCat.{max u v w} R) := monoidalPreadditive.{u, max v w}
  letI : MonoidalPreadditive (ModuleCat.{max u v w} S) := monoidalPreadditive.{v, max u w}
  let F : ModuleCat.{max u v w} R ⥤ ModuleCat.{max u v w} S :=
    extendScalars.{u, v, max u v w} (algebraMap R S)
  letI : F.PreservesHomology := preservesHomology_extendScalars_of_flat.{u, v, w}
    (algebraMap R S) (by rw [RingHom.flat_algebraMap_iff]; infer_instance)
  let L := (tensoringLeft (ModuleCat.{max u v w} R)).obj M
  let L' := (tensoringLeft (ModuleCat.{max u v w} S)).obj (F.obj M)
  exact Functor.leftDerivedCompIsoOfPreservesHomology L F q ≪≫
    CategoryTheory.NatIso.leftDerived
      (scalarExtensionTensorNatIso R S (algebraMap R S) M) q ≪≫
      flatScalarExtensionDerivedPrecompIso R S L' q

/-- Genuine flat base change for both original native Tor coefficients. -/
def flatScalarExtensionTorBaseChangeIso (M X : ModuleCat.{max u v w} R) (q : ℕ) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) := tensorStructure.{u, max v w}
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} S) := tensorStructure.{v, max u w}
    letI : MonoidalCategory (ModuleCat.{max u v w} R) := monoidalCategory.{u, max v w}
    letI : MonoidalCategory (ModuleCat.{max u v w} S) := monoidalCategory.{v, max u w}
    letI : MonoidalPreadditive (ModuleCat.{max u v w} R) := monoidalPreadditive.{u, max v w}
    letI : MonoidalPreadditive (ModuleCat.{max u v w} S) := monoidalPreadditive.{v, max u w}
    (extendScalars.{u, v, max u v w} (algebraMap R S)).obj
        (((Tor (ModuleCat.{max u v w} R) q).obj M).obj X) ≅
      ((Tor (ModuleCat.{max u v w} S) q).obj
        ((extendScalars.{u, v, max u v w} (algebraMap R S)).obj M)).obj
          ((extendScalars.{u, v, max u v w} (algebraMap R S)).obj X) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) := tensorStructure.{u, max v w}
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} S) := tensorStructure.{v, max u w}
  letI : MonoidalCategory (ModuleCat.{max u v w} R) := monoidalCategory.{u, max v w}
  letI : MonoidalCategory (ModuleCat.{max u v w} S) := monoidalCategory.{v, max u w}
  letI : MonoidalPreadditive (ModuleCat.{max u v w} R) := monoidalPreadditive.{u, max v w}
  letI : MonoidalPreadditive (ModuleCat.{max u v w} S) := monoidalPreadditive.{v, max u w}
  exact (flatScalarExtensionTorBaseChangeNatIso R S M q).app X

/-- Native Tor base change preserves every map in the resolved coefficient. -/
theorem flatScalarExtensionTorBaseChangeIso_hom_naturality_resolved
    (M : ModuleCat.{max u v w} R) {X Y : ModuleCat.{max u v w} R}
    (h : X ⟶ Y) (q : ℕ) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) := tensorStructure.{u, max v w}
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} S) := tensorStructure.{v, max u w}
    letI : MonoidalCategory (ModuleCat.{max u v w} R) := monoidalCategory.{u, max v w}
    letI : MonoidalCategory (ModuleCat.{max u v w} S) := monoidalCategory.{v, max u w}
    letI : MonoidalPreadditive (ModuleCat.{max u v w} R) := monoidalPreadditive.{u, max v w}
    letI : MonoidalPreadditive (ModuleCat.{max u v w} S) := monoidalPreadditive.{v, max u w}
    (extendScalars.{u, v, max u v w} (algebraMap R S)).map
        (((Tor (ModuleCat.{max u v w} R) q).obj M).map h) ≫
        (flatScalarExtensionTorBaseChangeIso R S M Y q).hom =
      (flatScalarExtensionTorBaseChangeIso R S M X q).hom ≫
        ((Tor (ModuleCat.{max u v w} S) q).obj
          ((extendScalars.{u, v, max u v w} (algebraMap R S)).obj M)).map
            ((extendScalars.{u, v, max u v w} (algebraMap R S)).map h) := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} R) := tensorStructure.{u, max v w}
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} S) := tensorStructure.{v, max u w}
  let : MonoidalCategory (ModuleCat.{max u v w} R) := monoidalCategory.{u, max v w}
  let : MonoidalCategory (ModuleCat.{max u v w} S) := monoidalCategory.{v, max u w}
  let : MonoidalPreadditive (ModuleCat.{max u v w} R) := monoidalPreadditive.{u, max v w}
  let : MonoidalPreadditive (ModuleCat.{max u v w} S) := monoidalPreadditive.{v, max u w}
  exact (flatScalarExtensionTorBaseChangeNatIso R S M q).hom.naturality h

/-- Native Tor base change preserves every map in the first coefficient. -/
theorem flatScalarExtensionTorBaseChangeIso_hom_naturality_coefficient
    {M₁ M₂ : ModuleCat.{max u v w} R} (g : M₁ ⟶ M₂)
    (X : ModuleCat.{max u v w} R) (q : ℕ) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) := tensorStructure.{u, max v w}
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} S) := tensorStructure.{v, max u w}
    letI : MonoidalCategory (ModuleCat.{max u v w} R) := monoidalCategory.{u, max v w}
    letI : MonoidalCategory (ModuleCat.{max u v w} S) := monoidalCategory.{v, max u w}
    letI : MonoidalPreadditive (ModuleCat.{max u v w} R) := monoidalPreadditive.{u, max v w}
    letI : MonoidalPreadditive (ModuleCat.{max u v w} S) := monoidalPreadditive.{v, max u w}
    (extendScalars.{u, v, max u v w} (algebraMap R S)).map
        (((Tor (ModuleCat.{max u v w} R) q).map g).app X) ≫
        (flatScalarExtensionTorBaseChangeIso R S M₂ X q).hom =
      (flatScalarExtensionTorBaseChangeIso R S M₁ X q).hom ≫
        ((Tor (ModuleCat.{max u v w} S) q).map
          ((extendScalars.{u, v, max u v w} (algebraMap R S)).map g)).app
            ((extendScalars.{u, v, max u v w} (algebraMap R S)).obj X) := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} R) := tensorStructure.{u, max v w}
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} S) := tensorStructure.{v, max u w}
  let : MonoidalCategory (ModuleCat.{max u v w} R) := monoidalCategory.{u, max v w}
  let : MonoidalCategory (ModuleCat.{max u v w} S) := monoidalCategory.{v, max u w}
  let : MonoidalPreadditive (ModuleCat.{max u v w} R) := monoidalPreadditive.{u, max v w}
  let : MonoidalPreadditive (ModuleCat.{max u v w} S) := monoidalPreadditive.{v, max u w}
  let F : ModuleCat.{max u v w} R ⥤ ModuleCat.{max u v w} S :=
    extendScalars.{u, v, max u v w} (algebraMap R S)
  let : F.PreservesHomology := preservesHomology_extendScalars_of_flat.{u, v, w}
    (algebraMap R S) (by rw [RingHom.flat_algebraMap_iff]; infer_instance)
  let L₁ := (tensoringLeft (ModuleCat.{max u v w} R)).obj M₁
  let L₂ := (tensoringLeft (ModuleCat.{max u v w} R)).obj M₂
  let L₁' := (tensoringLeft (ModuleCat.{max u v w} S)).obj (F.obj M₁)
  let L₂' := (tensoringLeft (ModuleCat.{max u v w} S)).obj (F.obj M₂)
  let α : L₁ ⟶ L₂ := (tensoringLeft (ModuleCat.{max u v w} R)).map g
  let β : L₁' ⟶ L₂' := (tensoringLeft (ModuleCat.{max u v w} S)).map (F.map g)
  let e₁ := scalarExtensionTensorNatIso R S (algebraMap R S) M₁
  let e₂ := scalarExtensionTensorNatIso R S (algebraMap R S) M₂
  have he : Functor.whiskerRight α F ≫ e₂.hom = e₁.hom ≫ Functor.whiskerLeft F β := by
    apply NatTrans.ext
    funext Y
    have hw := scalarExtensionTensorIso_hom_naturality R S (algebraMap R S) g (𝟙 Y)
    rw [F.map_id] at hw
    exact hw
  let a₁ := (Functor.leftDerivedCompIsoOfPreservesHomology L₁ F q).hom.app X
  let a₂ := (Functor.leftDerivedCompIsoOfPreservesHomology L₂ F q).hom.app X
  let b₁ := (CategoryTheory.NatIso.leftDerived e₁ q).hom.app X
  let b₂ := (CategoryTheory.NatIso.leftDerived e₂ q).hom.app X
  let c₁ := (flatScalarExtensionDerivedPrecompIso R S L₁' q).hom.app X
  let c₂ := (flatScalarExtensionDerivedPrecompIso R S L₂' q).hom.app X
  let t := (NatTrans.leftDerived (Functor.whiskerRight α F) q).app X
  let t' := (NatTrans.leftDerived (Functor.whiskerLeft F β) q).app X
  have hA : F.map ((NatTrans.leftDerived α q).app X) ≫ a₂ = a₁ ≫ t :=
    congrArg (fun ε => ε.app X)
      (Functor.leftDerivedCompIsoOfPreservesHomology_hom_naturality_functor α F q)
  have hB : t ≫ b₂ = b₁ ≫ t' :=
    congrArg (fun ε => ε.app X)
      (CategoryTheory.NatIso.leftDerived_hom_naturality e₁ e₂
        (Functor.whiskerRight α F) (Functor.whiskerLeft F β) he q)
  have hC : t' ≫ c₂ = c₁ ≫ (NatTrans.leftDerived β q).app (F.obj X) :=
    flatScalarExtensionDerivedPrecompIso_hom_naturality_functor R S β X q
  change F.map ((NatTrans.leftDerived α q).app X) ≫ (a₂ ≫ b₂ ≫ c₂) =
    (a₁ ≫ b₁ ≫ c₁) ≫ (NatTrans.leftDerived β q).app (F.obj X)
  calc
    _ = a₁ ≫ t ≫ b₂ ≫ c₂ := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ b₂ ≫ c₂) hA
    _ = a₁ ≫ b₁ ≫ t' ≫ c₂ := by
      simpa only [Category.assoc] using congrArg (fun k => a₁ ≫ k ≫ c₂) hB
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun k => a₁ ≫ b₁ ≫ k) hC

end FlatChange

/-- The actual native Tor over the local ring, with both original
coefficients localized and the original coefficient order retained. -/
abbrev nativeTorAtPrime (p : Ideal R) [p.IsPrime]
    (M X : ModuleCat.{max u w} R) (q : ℕ) :
    ModuleCat.{max u w} (Localization.AtPrime p) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u w} (Localization.AtPrime p)) :=
    tensorStructure.{u, w}
  letI : MonoidalCategory (ModuleCat.{max u w} (Localization.AtPrime p)) :=
    monoidalCategory.{u, w}
  letI : MonoidalPreadditive (ModuleCat.{max u w} (Localization.AtPrime p)) :=
    monoidalPreadditive.{u, w}
  exact ((Tor (ModuleCat.{max u w} (Localization.AtPrime p)) q).obj
    (ModuleCat.of (Localization.AtPrime p) (LocalizedModule.AtPrime p M))).obj
      (ModuleCat.of (Localization.AtPrime p) (LocalizedModule.AtPrime p X))

/-- Localization commutes with the actual native derived tensor. Flatness
is earned from the localization; neither coefficient is assumed flat. -/
def localizedNativeTorIso (p : Ideal R) [p.IsPrime]
    (M X : ModuleCat.{max u w} R) (q : ℕ) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u w} R) := tensorStructure.{u, w}
    letI : MonoidalCategory (ModuleCat.{max u w} R) := monoidalCategory.{u, w}
    letI : MonoidalPreadditive (ModuleCat.{max u w} R) := monoidalPreadditive.{u, w}
    ModuleCat.of (Localization.AtPrime p)
        (LocalizedModule.AtPrime p (((Tor (ModuleCat.{max u w} R) q).obj M).obj X)) ≅
      nativeTorAtPrime R p M X q := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u w} R) := tensorStructure.{u, w}
  letI : MonoidalCategoryStruct (ModuleCat.{max u w} (Localization.AtPrime p)) :=
    tensorStructure.{u, w}
  letI : MonoidalCategory (ModuleCat.{max u w} R) := monoidalCategory.{u, w}
  letI : MonoidalCategory (ModuleCat.{max u w} (Localization.AtPrime p)) :=
    monoidalCategory.{u, w}
  letI : MonoidalPreadditive (ModuleCat.{max u w} R) := monoidalPreadditive.{u, w}
  letI : MonoidalPreadditive (ModuleCat.{max u w} (Localization.AtPrime p)) :=
    monoidalPreadditive.{u, w}
  letI : Module.Flat R (Localization.AtPrime p) := inferInstance
  let F : ModuleCat.{max u w} R ⥤ ModuleCat.{max u w} (Localization.AtPrime p) :=
    extendScalars.{u, u, max u w} (algebraMap R (Localization.AtPrime p))
  let eF (Y : ModuleCat.{max u w} R) :
      (F.obj Y : Type (max u w)) ≃ₗ[Localization.AtPrime p]
        (Localization.AtPrime p ⊗[R] Y) := by
    let : IsScalarTower R (Localization.AtPrime p)
        ((restrictScalars (algebraMap R (Localization.AtPrime p))).obj
          (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p))) :=
      IsScalarTower.restrictScalars R (Localization.AtPrime p) _
    dsimp only [F, extendScalars, ExtendScalars.obj']
    exact TensorProduct.AlgebraTensorModule.congr
      (localizationRestrictScalarsLinearEquiv p.primeCompl) (LinearEquiv.refl R Y)
  let e (Y : ModuleCat.{max u w} R) :
      ModuleCat.of (Localization.AtPrime p) (LocalizedModule.AtPrime p Y) ≅ F.obj Y :=
    ((LocalizedModule.equivTensorProduct p.primeCompl Y).trans (eF Y).symm).toModuleIso
  exact e (((Tor (ModuleCat.{max u w} R) q).obj M).obj X) ≪≫
    flatScalarExtensionTorBaseChangeIso.{u, u, w} R (Localization.AtPrime p) M X q ≪≫
    ((Tor (ModuleCat.{max u w} (Localization.AtPrime p)) q).mapIso (e M).symm).app
      (F.obj X) ≪≫
    ((Tor (ModuleCat.{max u w} (Localization.AtPrime p)) q).obj
      (ModuleCat.of (Localization.AtPrime p) (LocalizedModule.AtPrime p M))).mapIso (e X).symm

end ModuleCat.UniverseTensor
