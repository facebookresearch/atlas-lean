/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.FlatScalarExtensionTorCancellationNaturality

/-!
# Coefficient naturality of Tor cancellation

Flat scalar cancellation commutes with maps of the extended-ring
coefficient module. The comparison uses extension of the projective
resolution, its homology maps and the scalar tensor coefficient square.
Degrees, ring universes and coefficient universes are independent.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ModuleCat.UniverseTensor

namespace ModuleCat.UniverseTensor

universe u v w

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S]
  [Algebra R S] [Module.Flat R S]

/-- The original flat native Tor comparison preserves every actual
extended-ring coefficient map in every original homological degree. -/
theorem flatScalarExtensionTorCancellationIso_hom_naturality_coefficient
    {N₁ N₂ : ModuleCat.{max u v w} S} (g : N₁ ⟶ N₂)
    (X : ModuleCat.{max u v w} R) (q : ℕ) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u,max v w}
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} S) :=
      ModuleCat.UniverseTensor.tensorStructure.{v,max u w}
    letI : MonoidalCategory (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,max v w}
    letI : MonoidalCategory (ModuleCat.{max u v w} S) :=
      ModuleCat.UniverseTensor.monoidalCategory.{v,max u w}
    letI : MonoidalPreadditive (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u,max v w}
    letI : MonoidalPreadditive (ModuleCat.{max u v w} S) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{v,max u w}
    (restrictScalars.{max u v w,u,v} (algebraMap R S)).map
        (((Tor (ModuleCat.{max u v w} S) q).map g).app
          ((extendScalars.{u,v,max u v w} (algebraMap R S)).obj X)) ≫
        (flatScalarExtensionTorCancellationIso.{u,v,w} R S N₂ X q).hom =
      (flatScalarExtensionTorCancellationIso.{u,v,w} R S N₁ X q).hom ≫
        (((Tor (ModuleCat.{max u v w} R) q).map
          ((restrictScalars.{max u v w,u,v} (algebraMap R S)).map g)).app X) := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,max v w}
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} S) :=
    ModuleCat.UniverseTensor.tensorStructure.{v,max u w}
  let : MonoidalCategory (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u,max v w}
  let : MonoidalCategory (ModuleCat.{max u v w} S) :=
    ModuleCat.UniverseTensor.monoidalCategory.{v,max u w}
  let : MonoidalPreadditive (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,max v w}
  let : MonoidalPreadditive (ModuleCat.{max u v w} S) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{v,max u w}
  let F : ModuleCat.{max u v w} R ⥤ ModuleCat.{max u v w} S :=
    extendScalars.{u,v,max u v w} (algebraMap R S)
  let H : ModuleCat.{max u v w} S ⥤ ModuleCat.{max u v w} R :=
    restrictScalars.{max u v w,u,v} (algebraMap R S)
  let : F.PreservesHomology := ModuleCat.preservesHomology_extendScalars_of_flat.{u,v,w}
    (algebraMap R S) (by rw [RingHom.flat_algebraMap_iff]; infer_instance)
  let P := projectiveResolution X
  let Q := flatScalarExtensionProjectiveResolution.{u,v,w} R S P
  let L₁' := (tensoringLeft (ModuleCat.{max u v w} S)).obj N₁
  let L₂' := (tensoringLeft (ModuleCat.{max u v w} S)).obj N₂
  let L₁ := (tensoringLeft (ModuleCat.{max u v w} R)).obj (H.obj N₁)
  let L₂ := (tensoringLeft (ModuleCat.{max u v w} R)).obj (H.obj N₂)
  let α : L₁' ⟶ L₂' := (tensoringLeft (ModuleCat.{max u v w} S)).map g
  let β : L₁ ⟶ L₂ := (tensoringLeft (ModuleCat.{max u v w} R)).map (H.map g)
  let K₁ := (L₁'.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  let K₂ := (L₂'.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  let κ : K₁ ⟶ K₂ := (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app Q.complex
  let ψ := (NatTrans.mapHomologicalComplex β (ComplexShape.down ℕ)).app P.complex
  let J₁ := (L₁.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let J₂ := (L₂.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let HK₁ := (H.mapHomologicalComplex (ComplexShape.down ℕ)).obj K₁
  let HK₂ := (H.mapHomologicalComplex (ComplexShape.down ℕ)).obj K₂
  let E₁ : HK₁ ≅ J₁ := (NatIso.mapHomologicalComplex
    (scalarTensorCancellationNatIso.{u,v,w} R S (algebraMap R S) N₁)
      (ComplexShape.down ℕ)).app P.complex
  let E₂ : HK₂ ≅ J₂ := (NatIso.mapHomologicalComplex
    (scalarTensorCancellationNatIso.{u,v,w} R S (algebraMap R S) N₂)
      (ComplexShape.down ℕ)).app P.complex
  let tS : (L₁'.leftDerived q).obj (F.obj X) ⟶ (L₂'.leftDerived q).obj (F.obj X) :=
    ((Tor (ModuleCat.{max u v w} S) q).map g).app (F.obj X)
  let tR : (L₁.leftDerived q).obj X ⟶ (L₂.leftDerived q).obj X :=
    ((Tor (ModuleCat.{max u v w} R) q).map (H.map g)).app X
  let a₁ : (L₁'.leftDerived q).obj (F.obj X) ⟶ K₁.homology q :=
    (Q.isoLeftDerivedObj L₁' q).hom
  let a₂ : (L₂'.leftDerived q).obj (F.obj X) ⟶ K₂.homology q :=
    (Q.isoLeftDerivedObj L₂' q).hom
  let b₁ : H.obj (K₁.homology q) ⟶ HK₁.homology q := ((K₁.sc q).mapHomologyIso H).inv
  let b₂ : H.obj (K₂.homology q) ⟶ HK₂.homology q := ((K₂.sc q).mapHomologyIso H).inv
  let c₁ : HK₁.homology q ⟶ J₁.homology q := HomologicalComplex.homologyMap E₁.hom q
  let c₂ : HK₂.homology q ⟶ J₂.homology q := HomologicalComplex.homologyMap E₂.hom q
  let d₁ : J₁.homology q ⟶ (L₁.leftDerived q).obj X := (P.isoLeftDerivedObj L₁ q).inv
  let d₂ : J₂.homology q ⟶ (L₂.leftDerived q).obj X := (P.isoLeftDerivedObj L₂ q).inv
  have hQ : tS ≫ a₂ = a₁ ≫ HomologicalComplex.homologyMap κ q := by
    change (NatTrans.leftDerived α q).app (F.obj X) ≫ (Q.isoLeftDerivedObj L₂' q).hom = _
    rw [Q.leftDerived_app_eq α q]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have hQH : H.map tS ≫ H.map a₂ = H.map a₁ ≫ H.map (HomologicalComplex.homologyMap κ q) := by
    have h := congrArg (fun k => H.map k) hQ
    rw [H.map_comp, H.map_comp] at h
    exact h
  have hH : H.map (HomologicalComplex.homologyMap κ q) ≫ b₂ =
      b₁ ≫ HomologicalComplex.homologyMap
        ((H.mapHomologicalComplex (ComplexShape.down ℕ)).map κ) q := by
    exact ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{max u v w} S)
        (ComplexShape.down ℕ) q).map κ) H
  have hC : (H.mapHomologicalComplex (ComplexShape.down ℕ)).map κ ≫ E₂.hom = E₁.hom ≫ ψ := by
    apply HomologicalComplex.Hom.ext
    funext i
    change H.map (g ▷ F.obj (P.complex.X i)) ≫
        (scalarTensorCancellationIso.{u,v,w} R S (algebraMap R S) N₂ (P.complex.X i)).hom =
      (scalarTensorCancellationIso.{u,v,w} R S (algebraMap R S) N₁ (P.complex.X i)).hom ≫
        (H.map g ▷ P.complex.X i)
    exact scalarTensorCancellationIso_hom_naturality_coefficient.{u,v,w} R S
      (algebraMap R S) g (P.complex.X i)
  have hCH :
      HomologicalComplex.homologyMap ((H.mapHomologicalComplex (ComplexShape.down ℕ)).map κ) q ≫ c₂ =
      c₁ ≫ HomologicalComplex.homologyMap ψ q := by
    let U := HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} R) (ComplexShape.down ℕ) q
    have h := congrArg (fun k => U.map k) hC
    rw [U.map_comp, U.map_comp] at h
    exact h
  have hP : HomologicalComplex.homologyMap ψ q ≫ d₂ = d₁ ≫ tR := by
    change _ = (P.isoLeftDerivedObj L₁ q).inv ≫ (NatTrans.leftDerived β q).app X
    rw [P.leftDerived_app_eq β q]
    simp only [Iso.inv_hom_id_assoc]
    rfl
  change H.map tS ≫ (H.map a₂ ≫ b₂ ≫ c₂ ≫ d₂) = (H.map a₁ ≫ b₁ ≫ c₁ ≫ d₁) ≫ tR
  calc
    _ = H.map a₁ ≫ H.map (HomologicalComplex.homologyMap κ q) ≫ b₂ ≫ c₂ ≫ d₂ := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ b₂ ≫ c₂ ≫ d₂) hQH
    _ = H.map a₁ ≫ b₁ ≫
        HomologicalComplex.homologyMap ((H.mapHomologicalComplex (ComplexShape.down ℕ)).map κ) q ≫
        c₂ ≫ d₂ := by
      simpa only [Category.assoc] using congrArg (fun k => H.map a₁ ≫ k ≫ c₂ ≫ d₂) hH
    _ = H.map a₁ ≫ b₁ ≫ c₁ ≫ HomologicalComplex.homologyMap ψ q ≫ d₂ := by
      simpa only [Category.assoc] using congrArg (fun k => H.map a₁ ≫ b₁ ≫ k ≫ d₂) hCH
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun k => H.map a₁ ≫ b₁ ≫ c₁ ≫ k) hP

/-- The actual inverse of the original flat Tor cancellation retains
the same coefficient map in every original degree. -/
theorem flatScalarExtensionTorCancellationIso_inv_naturality_coefficient
    {N₁ N₂ : ModuleCat.{max u v w} S} (g : N₁ ⟶ N₂)
    (X : ModuleCat.{max u v w} R) (q : ℕ) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u,max v w}
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} S) :=
      ModuleCat.UniverseTensor.tensorStructure.{v,max u w}
    letI : MonoidalCategory (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,max v w}
    letI : MonoidalCategory (ModuleCat.{max u v w} S) :=
      ModuleCat.UniverseTensor.monoidalCategory.{v,max u w}
    letI : MonoidalPreadditive (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u,max v w}
    letI : MonoidalPreadditive (ModuleCat.{max u v w} S) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{v,max u w}
    (((Tor (ModuleCat.{max u v w} R) q).map
        ((restrictScalars.{max u v w,u,v} (algebraMap R S)).map g)).app X) ≫
        (flatScalarExtensionTorCancellationIso.{u,v,w} R S N₂ X q).inv =
      (flatScalarExtensionTorCancellationIso.{u,v,w} R S N₁ X q).inv ≫
        (restrictScalars.{max u v w,u,v} (algebraMap R S)).map
          (((Tor (ModuleCat.{max u v w} S) q).map g).app
            ((extendScalars.{u,v,max u v w} (algebraMap R S)).obj X)) := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,max v w}
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} S) :=
    ModuleCat.UniverseTensor.tensorStructure.{v,max u w}
  let : MonoidalCategory (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u,max v w}
  let : MonoidalCategory (ModuleCat.{max u v w} S) :=
    ModuleCat.UniverseTensor.monoidalCategory.{v,max u w}
  let : MonoidalPreadditive (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,max v w}
  let : MonoidalPreadditive (ModuleCat.{max u v w} S) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{v,max u w}
  rw [← cancel_mono (flatScalarExtensionTorCancellationIso.{u,v,w} R S N₂ X q).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [flatScalarExtensionTorCancellationIso_hom_naturality_coefficient.{u,v,w} R S g X q,
    Iso.inv_hom_id_assoc]

end ModuleCat.UniverseTensor
