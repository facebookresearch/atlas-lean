/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.FlatScalarExtensionTorBaseChangeUniverse
public import MathlibExt.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# Computation and coherence of the actual flat native Tor comparison

The existing base-change comparison is computed on the original projective
resolution. Its tensor chain map and homology comparison retain the actual
scalar-extension functor. No replacement Tor object or supplied comparison
is used.
-/

public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ModuleCat.UniverseTensor ChangeOfRings
open scoped CategoryTheory.Prod

namespace ModuleCat.UniverseTensor

universe u v w

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S]

/-- The canonical scalar tensor comparison retains the actual scalar and two coefficients. -/
theorem scalarExtensionTensorIso_hom_tmul (f : R →+* S)
    (M X : ModuleCat.{max u v w} R) (s : S) (m : M) (x : X) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) := tensorStructure.{u, max v w}
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} S) := tensorStructure.{v, max u w}
    letI : MonoidalCategory (ModuleCat.{max u v w} R) := monoidalCategory.{u, max v w}
    letI : MonoidalCategory (ModuleCat.{max u v w} S) := monoidalCategory.{v, max u w}
    letI : Algebra R S := f.toAlgebra
    (scalarExtensionTensorIso R S f M X).hom (s ⊗ₜ[R, f] (m ⊗ₜ[R] x)) =
      (s ⊗ₜ[R, f] m) ⊗ₜ[S] ((1 : S) ⊗ₜ[R, f] x) := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} R) := tensorStructure.{u, max v w}
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} S) := tensorStructure.{v, max u w}
  let : MonoidalCategory (ModuleCat.{max u v w} R) := monoidalCategory.{u, max v w}
  let : MonoidalCategory (ModuleCat.{max u v w} S) := monoidalCategory.{v, max u w}
  let : Algebra R S := f.toAlgebra
  unfold scalarExtensionTensorIso
  rfl

variable [Algebra R S] [Module.Flat R S]

/-- The canonical flat Tor base-change hom has its actual source-resolution computation. -/
theorem flatScalarExtensionTorBaseChangeIso_hom_computation
    (M X : ModuleCat.{max u v w} R) (q : ℕ) :
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
    let P := projectiveResolution X
    let Q := flatScalarExtensionProjectiveResolution.{u, v, w} R S P
    let L := (tensoringLeft (ModuleCat.{max u v w} R)).obj M
    let L' := (tensoringLeft (ModuleCat.{max u v w} S)).obj (F.obj M)
    let K := (L.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
    let c := (NatIso.mapHomologicalComplex
      (scalarExtensionTensorNatIso R S (algebraMap R S) M) (ComplexShape.down ℕ)).app P.complex
    (flatScalarExtensionTorBaseChangeIso.{u, v, w} R S M X q).hom =
      F.map (P.isoLeftDerivedObj L q).hom ≫
        ((K.sc q).mapHomologyIso F).inv ≫ HomologicalComplex.homologyMap c.hom q ≫
          (Q.isoLeftDerivedObj L' q).inv := by
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
  let P := projectiveResolution X
  let Q := flatScalarExtensionProjectiveResolution.{u, v, w} R S P
  let L := (tensoringLeft (ModuleCat.{max u v w} R)).obj M
  let L' := (tensoringLeft (ModuleCat.{max u v w} S)).obj (F.obj M)
  let α := scalarExtensionTensorNatIso R S (algebraMap R S) M
  let a := F.map (P.isoLeftDerivedObj L q).hom
  let b := ((HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) q F).app
    ((L.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)).inv
  let c := P.isoLeftDerivedObj (L ⋙ F) q
  let d := P.isoLeftDerivedObj (F ⋙ L') q
  let t := HomologicalComplex.homologyMap
    ((NatTrans.mapHomologicalComplex α.hom (ComplexShape.down ℕ)).app P.complex) q
  let e := (Q.isoLeftDerivedObj L' q).inv
  let G : ModuleCat.{max u v w} S ⥤ ModuleCat.{max u v w} R :=
    restrictScalars.{max u v w, u, v} (algebraMap R S)
  let : G.PreservesEpimorphisms :=
    { preserves := fun g _ => (ModuleCat.epi_iff_surjective _).mpr
        ((ModuleCat.epi_iff_surjective g).mp inferInstance) }
  let : F.PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (extendRestrictScalarsAdj.{max u v w, u, v} (algebraMap R S))
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} S)
    (ComplexShape.down ℕ) q
  let χ := (Functor.mapHomologicalComplexCompIso (F := F) (G := L')
    (Iso.refl (F ⋙ L')) (ComplexShape.down ℕ)).app P.complex
  have hχ : χ.inv =
      𝟙 (((F ⋙ L').mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) := by
    apply HomologicalComplex.hom_ext
    intro i
    rfl
  have hpre : (flatScalarExtensionDerivedPrecompIso R S L' q).hom.app X =
      d.hom ≫ e := by
    have h : (flatScalarExtensionDerivedPrecompIso R S L' q).hom.app X =
        d.hom ≫ H.map χ.inv ≫ e :=
      Functor.leftDerivedPrecompIso_hom_app F L' q P
    exact h.trans (by
      rw [hχ, H.map_id]
      exact congrArg (fun f => f ≫ e) (Category.comp_id d.hom))
  have hd : (NatTrans.leftDerived α.hom q).app X = c.hom ≫ t ≫ d.inv := by
    exact ProjectiveResolution.leftDerived_app_eq α.hom P q
  dsimp only [flatScalarExtensionTorBaseChangeIso, flatScalarExtensionTorBaseChangeNatIso,
    Iso.app_hom, Iso.trans_hom, NatTrans.comp_app, Iso.app, Iso.trans, NatIso.ofComponents.app]
  rw [hpre]
  change a ≫ b ≫ c.inv ≫ (NatTrans.leftDerived α.hom q).app X ≫ d.hom ≫ e = a ≫ b ≫ t ≫ e
  rw [hd]
  have hc : c.inv ≫ (c.hom ≫ t ≫ d.inv) = t ≫ d.inv :=
    ((Category.assoc c.inv c.hom (t ≫ d.inv)).symm.trans
      (congrArg (fun k => k ≫ (t ≫ d.inv)) c.inv_hom_id)).trans (Category.id_comp _)
  have hd' : (t ≫ d.inv) ≫ d.hom = t :=
    (Category.assoc t d.inv d.hom).trans
      ((congrArg (fun k => t ≫ k) d.inv_hom_id).trans (Category.comp_id _))
  calc
    _ = a ≫ b ≫ (t ≫ d.inv) ≫ d.hom ≫ e :=
      congrArg (fun k => a ≫ b ≫ k ≫ d.hom ≫ e) hc
    _ = a ≫ b ≫ ((t ≫ d.inv) ≫ d.hom) ≫ e :=
      congrArg (fun k => a ≫ b ≫ k) (Category.assoc (t ≫ d.inv) d.hom e).symm
    _ = _ := congrArg (fun k => a ≫ b ≫ k ≫ e) hd'

/-- The actual tensor-complex and homology comparisons retain a lift between source resolutions. -/
theorem flatScalarExtensionTorComputation_lift
    (M X : ModuleCat.{max u v w} R) (q : ℕ)
    (P P' : ProjectiveResolution X) (φ : P.complex ⟶ P'.complex)
    (hφ : φ.f 0 ≫ P'.π.f 0 = P.π.f 0) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) := tensorStructure.{u, max v w}
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} S) := tensorStructure.{v, max u w}
    letI : MonoidalCategory (ModuleCat.{max u v w} R) := monoidalCategory.{u, max v w}
    letI : MonoidalCategory (ModuleCat.{max u v w} S) := monoidalCategory.{v, max u w}
    let F : ModuleCat.{max u v w} R ⥤ ModuleCat.{max u v w} S :=
      extendScalars.{u, v, max u v w} (algebraMap R S)
    letI : F.PreservesHomology := preservesHomology_extendScalars_of_flat.{u, v, w}
      (algebraMap R S) (by rw [RingHom.flat_algebraMap_iff]; infer_instance)
    let L := (tensoringLeft (ModuleCat.{max u v w} R)).obj M
    let L' := (tensoringLeft (ModuleCat.{max u v w} S)).obj (F.obj M)
    let Q := flatScalarExtensionProjectiveResolution.{u, v, w} R S P
    let Q' := flatScalarExtensionProjectiveResolution.{u, v, w} R S P'
    let K := (L.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
    let K' := (L.mapHomologicalComplex (ComplexShape.down ℕ)).obj P'.complex
    let μ := (L.mapHomologicalComplex (ComplexShape.down ℕ)).map φ
    let c := (NatIso.mapHomologicalComplex
      (scalarExtensionTensorNatIso R S (algebraMap R S) M) (ComplexShape.down ℕ)).app P.complex
    let c' := (NatIso.mapHomologicalComplex
      (scalarExtensionTensorNatIso R S (algebraMap R S) M) (ComplexShape.down ℕ)).app P'.complex
    F.map (HomologicalComplex.homologyMap μ q) ≫ ((K'.sc q).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap c'.hom q ≫ (Q'.isoLeftDerivedObj L' q).inv =
      ((K.sc q).mapHomologyIso F).inv ≫ HomologicalComplex.homologyMap c.hom q ≫
        (Q.isoLeftDerivedObj L' q).inv := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} R) := tensorStructure.{u, max v w}
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} S) := tensorStructure.{v, max u w}
  let : MonoidalCategory (ModuleCat.{max u v w} R) := monoidalCategory.{u, max v w}
  let : MonoidalCategory (ModuleCat.{max u v w} S) := monoidalCategory.{v, max u w}
  let F : ModuleCat.{max u v w} R ⥤ ModuleCat.{max u v w} S :=
    extendScalars.{u, v, max u v w} (algebraMap R S)
  let : F.PreservesHomology := preservesHomology_extendScalars_of_flat.{u, v, w}
    (algebraMap R S) (by rw [RingHom.flat_algebraMap_iff]; infer_instance)
  let L := (tensoringLeft (ModuleCat.{max u v w} R)).obj M
  let L' := (tensoringLeft (ModuleCat.{max u v w} S)).obj (F.obj M)
  let Q := flatScalarExtensionProjectiveResolution.{u, v, w} R S P
  let Q' := flatScalarExtensionProjectiveResolution.{u, v, w} R S P'
  let K := (L.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let K' := (L.mapHomologicalComplex (ComplexShape.down ℕ)).obj P'.complex
  let μ := (L.mapHomologicalComplex (ComplexShape.down ℕ)).map φ
  let θ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ
  let ν := (L'.mapHomologicalComplex (ComplexShape.down ℕ)).map θ
  let c := (NatIso.mapHomologicalComplex
    (scalarExtensionTensorNatIso R S (algebraMap R S) M) (ComplexShape.down ℕ)).app P.complex
  let c' := (NatIso.mapHomologicalComplex
    (scalarExtensionTensorNatIso R S (algebraMap R S) M) (ComplexShape.down ℕ)).app P'.complex
  have hφ' : φ ≫ P'.π = P.π ≫ (ChainComplex.single₀ (ModuleCat.{max u v w} R)).map (𝟙 X) := by
    let f : ProjectiveResolution.Hom P P' (𝟙 X) :=
      { hom := φ, hom_f_zero_comp_π_f_zero := by
          rw [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, Category.comp_id]
          exact hφ }
    exact f.hom_comp_π
  have hθ : θ.f 0 ≫ Q'.π.f 0 = Q.π.f 0 ≫ F.map (𝟙 X) := by
    let A := (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).hom.app X
    have ht : θ ≫ Q'.π = Q.π ≫
        (ChainComplex.single₀ (ModuleCat.{max u v w} S)).map (F.map (𝟙 X)) := by
      change (F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ ≫
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map P'.π ≫ A) =
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π ≫ A) ≫ _
      rw [← Category.assoc, ← Functor.map_comp, hφ']
      rw [CategoryTheory.Functor.map_id, Category.comp_id, CategoryTheory.Functor.map_id,
        CategoryTheory.Functor.map_id]
      exact (Category.comp_id ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π ≫ A)).symm
    have h := congrArg (fun k => k.f 0) ht
    change θ.f 0 ≫ Q'.π.f 0 = Q.π.f 0 ≫ F.map (𝟙 X) at h
    exact h
  have hH : F.map (HomologicalComplex.homologyMap μ q) ≫ ((K'.sc q).mapHomologyIso F).inv =
      ((K.sc q).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map μ) q := by
    exact ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{max u v w} R)
        (ComplexShape.down ℕ) q).map μ) F
  have hC : (F.mapHomologicalComplex (ComplexShape.down ℕ)).map μ ≫ c'.hom = c.hom ≫ ν := by
    exact (NatIso.mapHomologicalComplex
      (scalarExtensionTensorNatIso R S (algebraMap R S) M) (ComplexShape.down ℕ)).hom.naturality φ
  have hCH : HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map μ) q ≫
        HomologicalComplex.homologyMap c'.hom q =
      HomologicalComplex.homologyMap c.hom q ≫ HomologicalComplex.homologyMap ν q := by
    let H := HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} S) (ComplexShape.down ℕ) q
    have h := congrArg (fun k => H.map k) hC
    rw [H.map_comp, H.map_comp] at h
    exact h
  have hQ : HomologicalComplex.homologyMap ν q ≫ (Q'.isoLeftDerivedObj L' q).inv =
      (Q.isoLeftDerivedObj L' q).inv := by
    have h := ProjectiveResolution.isoLeftDerivedObj_inv_naturality
      (F.map (𝟙 X)) Q Q' θ hθ L' q
    change (Q.isoLeftDerivedObj L' q).inv ≫ (L'.leftDerived q).map (F.map (𝟙 X)) =
      HomologicalComplex.homologyMap ν q ≫ (Q'.isoLeftDerivedObj L' q).inv at h
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id] at h
    exact h.symm
  calc
    _ = ((K.sc q).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map μ) q ≫
          HomologicalComplex.homologyMap c'.hom q ≫ (Q'.isoLeftDerivedObj L' q).inv := by
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ HomologicalComplex.homologyMap c'.hom q ≫
          (Q'.isoLeftDerivedObj L' q).inv) hH)
    _ = ((K.sc q).mapHomologyIso F).inv ≫
        (HomologicalComplex.homologyMap c.hom q ≫ HomologicalComplex.homologyMap ν q) ≫
          (Q'.isoLeftDerivedObj L' q).inv := by
      exact congrArg (fun k => ((K.sc q).mapHomologyIso F).inv ≫ k ≫
        (Q'.isoLeftDerivedObj L' q).inv) hCH
    _ = ((K.sc q).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap c.hom q ≫
          (HomologicalComplex.homologyMap ν q ≫ (Q'.isoLeftDerivedObj L' q).inv) :=
      (Category.assoc _ _ _).trans (congrArg (fun k => ((K.sc q).mapHomologyIso F).inv ≫ k)
        (Category.assoc _ _ _))
    _ = _ := congrArg (fun k => ((K.sc q).mapHomologyIso F).inv ≫
      HomologicalComplex.homologyMap c.hom q ≫ k) hQ

/-- The existing flat native Tor comparison is computed on any actual projective source resolution. -/
theorem flatScalarExtensionTorBaseChangeIso_hom_computation_of_resolution
    (M X : ModuleCat.{max u v w} R) (q : ℕ) (P : ProjectiveResolution X) :
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
    let Q := flatScalarExtensionProjectiveResolution.{u, v, w} R S P
    let L := (tensoringLeft (ModuleCat.{max u v w} R)).obj M
    let L' := (tensoringLeft (ModuleCat.{max u v w} S)).obj (F.obj M)
    let K := (L.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
    let c := (NatIso.mapHomologicalComplex
      (scalarExtensionTensorNatIso R S (algebraMap R S) M) (ComplexShape.down ℕ)).app P.complex
    (flatScalarExtensionTorBaseChangeIso.{u, v, w} R S M X q).hom =
      F.map (P.isoLeftDerivedObj L q).hom ≫ ((K.sc q).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap c.hom q ≫ (Q.isoLeftDerivedObj L' q).inv := by
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
  let P₀ := projectiveResolution X
  let Q₀ := flatScalarExtensionProjectiveResolution.{u, v, w} R S P₀
  let Q := flatScalarExtensionProjectiveResolution.{u, v, w} R S P
  let L := (tensoringLeft (ModuleCat.{max u v w} R)).obj M
  let L' := (tensoringLeft (ModuleCat.{max u v w} S)).obj (F.obj M)
  let K₀ := (L.mapHomologicalComplex (ComplexShape.down ℕ)).obj P₀.complex
  let K := (L.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let c₀ := (NatIso.mapHomologicalComplex
    (scalarExtensionTensorNatIso R S (algebraMap R S) M) (ComplexShape.down ℕ)).app P₀.complex
  let c := (NatIso.mapHomologicalComplex
    (scalarExtensionTensorNatIso R S (algebraMap R S) M) (ComplexShape.down ℕ)).app P.complex
  let φ := ProjectiveResolution.lift (𝟙 X) P₀ P
  let μ := (L.mapHomologicalComplex (ComplexShape.down ℕ)).map φ
  have hφ : φ.f 0 ≫ P.π.f 0 = P₀.π.f 0 := by
    have h := ProjectiveResolution.lift_commutes_zero (𝟙 X) P₀ P
    exact h.trans (Category.comp_id _)
  have hP : (P₀.isoLeftDerivedObj L q).hom ≫ HomologicalComplex.homologyMap μ q =
      (P.isoLeftDerivedObj L q).hom := by
    have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality
      (𝟙 X) P₀ P φ (ProjectiveResolution.lift_commutes_zero (𝟙 X) P₀ P) L q
    change (L.leftDerived q).map (𝟙 X) ≫ (P.isoLeftDerivedObj L q).hom =
      (P₀.isoLeftDerivedObj L q).hom ≫ HomologicalComplex.homologyMap μ q at h
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact h.symm
  have hFP : F.map (P₀.isoLeftDerivedObj L q).hom ≫ F.map (HomologicalComplex.homologyMap μ q) =
      F.map (P.isoLeftDerivedObj L q).hom :=
    (F.map_comp _ _).symm.trans (congrArg (fun m => F.map m) hP)
  have hTail := flatScalarExtensionTorComputation_lift.{u, v, w} R S M X q P₀ P φ hφ
  have hOriginal := flatScalarExtensionTorBaseChangeIso_hom_computation.{u, v, w} R S M X q
  change (flatScalarExtensionTorBaseChangeIso R S M X q).hom =
      F.map (P.isoLeftDerivedObj L q).hom ≫ ((K.sc q).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap c.hom q ≫ (Q.isoLeftDerivedObj L' q).inv
  let a₀ := F.map (P₀.isoLeftDerivedObj L q).hom
  let a := F.map (P.isoLeftDerivedObj L q).hom
  let h := F.map (HomologicalComplex.homologyMap μ q)
  let b₀ := ((K₀.sc q).mapHomologyIso F).inv ≫
    HomologicalComplex.homologyMap c₀.hom q ≫ (Q₀.isoLeftDerivedObj L' q).inv
  let b := ((K.sc q).mapHomologyIso F).inv ≫
    HomologicalComplex.homologyMap c.hom q ≫ (Q.isoLeftDerivedObj L' q).inv
  have h₀ : (flatScalarExtensionTorBaseChangeIso R S M X q).hom = a₀ ≫ b₀ := hOriginal
  have h₁ : h ≫ b = b₀ := hTail
  have h₂ : a₀ ≫ h = a := hFP
  change (flatScalarExtensionTorBaseChangeIso R S M X q).hom = a ≫ b
  exact h₀.trans ((congrArg (fun m => a₀ ≫ m) h₁.symm).trans
    (((Category.assoc a₀ h b).symm).trans (congrArg (fun m => m ≫ b) h₂)))

section ScalarComposition
universe u₀
variable (R₀ S₀ T₀ : Type u₀) [CommRing R₀] [CommRing S₀] [CommRing T₀]

/-- Scalar tensor base change agrees with two successive actual scalar extensions. -/
theorem scalarExtensionTensorIso_hom_trans
    (f : R₀ →+* S₀) (g : S₀ →+* T₀) (M X : ModuleCat.{u₀} R₀) :
    letI : MonoidalCategoryStruct (ModuleCat.{u₀} R₀) := tensorStructure.{u₀, 0}
    letI : MonoidalCategoryStruct (ModuleCat.{u₀} S₀) := tensorStructure.{u₀, 0}
    letI : MonoidalCategoryStruct (ModuleCat.{u₀} T₀) := tensorStructure.{u₀, 0}
    letI : MonoidalCategory (ModuleCat.{u₀} R₀) := monoidalCategory.{u₀, 0}
    letI : MonoidalCategory (ModuleCat.{u₀} S₀) := monoidalCategory.{u₀, 0}
    letI : MonoidalCategory (ModuleCat.{u₀} T₀) := monoidalCategory.{u₀, 0}
    (extendScalarsComp f g).hom.app (M ⊗ X) ≫
      (extendScalars g).map (scalarExtensionTensorIso R₀ S₀ f M X).hom ≫
        (scalarExtensionTensorIso S₀ T₀ g ((extendScalars f).obj M) ((extendScalars f).obj X)).hom =
      (scalarExtensionTensorIso R₀ T₀ (g.comp f) M X).hom ≫
        (((tensoringLeft (ModuleCat.{u₀} T₀)).map ((extendScalarsComp f g).hom.app M)).app
            ((extendScalars (g.comp f)).obj X) ≫
          ((tensoringLeft (ModuleCat.{u₀} T₀)).obj
            ((extendScalars g).obj ((extendScalars f).obj M))).map
              ((extendScalarsComp f g).hom.app X)) := by
  let : MonoidalCategoryStruct (ModuleCat.{u₀} R₀) := tensorStructure.{u₀, 0}
  let : MonoidalCategoryStruct (ModuleCat.{u₀} S₀) := tensorStructure.{u₀, 0}
  let : MonoidalCategoryStruct (ModuleCat.{u₀} T₀) := tensorStructure.{u₀, 0}
  let : MonoidalCategory (ModuleCat.{u₀} R₀) := monoidalCategory.{u₀, 0}
  let : MonoidalCategory (ModuleCat.{u₀} S₀) := monoidalCategory.{u₀, 0}
  let : MonoidalCategory (ModuleCat.{u₀} T₀) := monoidalCategory.{u₀, 0}
  let : Algebra R₀ S₀ := f.toAlgebra
  let : Algebra S₀ T₀ := g.toAlgebra
  let : Algebra R₀ T₀ := (g.comp f).toAlgebra
  let N : ModuleCat.{u₀} T₀ :=
    ((tensoringLeft (ModuleCat.{u₀} T₀)).obj ((extendScalars g).obj ((extendScalars f).obj M))).obj
      ((extendScalars g).obj ((extendScalars f).obj X))
  let : Module R₀ N := Module.compHom N (g.comp f)
  let : IsScalarTower R₀ T₀ N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let K : ModuleCat.{u₀} T₀ := (extendScalars (g.comp f)).obj (M ⊗ X)
  let : Module R₀ K := Module.compHom K (g.comp f)
  let : IsScalarTower R₀ T₀ K := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let lhs : K ⟶ N := (extendScalarsComp f g).hom.app (M ⊗ X) ≫
    (extendScalars g).map (scalarExtensionTensorIso R₀ S₀ f M X).hom ≫
      (scalarExtensionTensorIso S₀ T₀ g ((extendScalars f).obj M) ((extendScalars f).obj X)).hom
  let rhs : K ⟶ N := (scalarExtensionTensorIso R₀ T₀ (g.comp f) M X).hom ≫
    (((tensoringLeft (ModuleCat.{u₀} T₀)).map ((extendScalarsComp f g).hom.app M)).app
      ((extendScalars (g.comp f)).obj X) ≫
      ((tensoringLeft (ModuleCat.{u₀} T₀)).obj ((extendScalars g).obj ((extendScalars f).obj M))).map
        ((extendScalarsComp f g).hom.app X))
  have hcomp (N : ModuleCat.{u₀} R₀) (n : N) (t : T₀) :
      (extendScalarsComp f g).hom.app N (t ⊗ₜ[R₀, g.comp f] n) =
        t ⊗ₜ[S₀, g] ((1 : S₀) ⊗ₜ[R₀, f] n) := by
    have h := ((extendScalarsComp f g).hom.app N).hom.map_smul t
      ((1 : T₀) ⊗ₜ[R₀, g.comp f] n)
    have hs := congrArg (fun y : (extendScalars g).obj ((extendScalars f).obj N) => t • y)
      (extendScalarsComp_hom_app_one_tmul f g N n)
    have hsource : t • ((1 : T₀) ⊗ₜ[R₀, g.comp f] n) = t ⊗ₜ[R₀, g.comp f] n := by
      change t • ((1 : T₀) ⊗ₜ[R₀] n) = _
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have htarget : t • ((1 : T₀) ⊗ₜ[S₀, g] ((1 : S₀) ⊗ₜ[R₀, f] n)) =
        t ⊗ₜ[S₀, g] ((1 : S₀) ⊗ₜ[R₀, f] n) := by
      change t • ((1 : T₀) ⊗ₜ[S₀] ((1 : S₀) ⊗ₜ[R₀] n)) = _
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact (congrArg (fun m => ((extendScalarsComp f g).hom.app N) m) hsource).symm.trans
      ((h.trans hs).trans htarget)
  apply ModuleCat.hom_ext
  change lhs.hom = rhs.hom
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' =>
      exact (lhs.hom.map_add z z').trans
        ((congrArg₂ (· + ·) hz hz').trans (rhs.hom.map_add z z').symm)
  | tmul t y =>
      induction y using TensorProduct.inductionOn with
      | add y y' hy hy' =>
          rw [TensorProduct.tmul_add]
          exact (lhs.hom.map_add _ _).trans
            ((congrArg₂ (· + ·) hy hy').trans (rhs.hom.map_add _ _).symm)
      | tmul m x =>
          change T₀ at t
          change (scalarExtensionTensorIso S₀ T₀ g ((extendScalars f).obj M) ((extendScalars f).obj X)).hom
            ((extendScalars g).map (scalarExtensionTensorIso R₀ S₀ f M X).hom
              ((extendScalarsComp f g).hom.app (M ⊗ X) (t ⊗ₜ[R₀, g.comp f] (m ⊗ₜ[R₀] x)))) = _
          have ha := hcomp (M ⊗ X) (m ⊗ₜ[R₀] x) t
          have hb := congrArg (fun y =>
            (scalarExtensionTensorIso S₀ T₀ g ((extendScalars f).obj M) ((extendScalars f).obj X)).hom
              ((extendScalars g).map (scalarExtensionTensorIso R₀ S₀ f M X).hom y)) ha
          apply hb.trans
          erw [ExtendScalars.map_tmul]
          have hfirst := scalarExtensionTensorIso_hom_tmul R₀ S₀ f M X 1 m x
          have hsecond := scalarExtensionTensorIso_hom_tmul S₀ T₀ g
            ((extendScalars f).obj M) ((extendScalars f).obj X) t
              ((1 : S₀) ⊗ₜ[R₀, f] m) ((1 : S₀) ⊗ₜ[R₀, f] x)
          have hleft := (congrArg (fun y =>
            (scalarExtensionTensorIso S₀ T₀ g ((extendScalars f).obj M) ((extendScalars f).obj X)).hom
              (t ⊗ₜ[S₀, g] y)) hfirst).trans hsecond
          apply hleft.trans
          symm
          change ((tensoringLeft (ModuleCat.{u₀} T₀)).obj
              ((extendScalars g).obj ((extendScalars f).obj M))).map
              ((extendScalarsComp f g).hom.app X)
            ((((tensoringLeft (ModuleCat.{u₀} T₀)).map ((extendScalarsComp f g).hom.app M)).app
                ((extendScalars (g.comp f)).obj X))
              ((scalarExtensionTensorIso R₀ T₀ (g.comp f) M X).hom
                (t ⊗ₜ[R₀, g.comp f] (m ⊗ₜ[R₀] x)))) = _
          have hr := scalarExtensionTensorIso_hom_tmul R₀ T₀ (g.comp f) M X t m x
          erw [hr]
          change ((extendScalarsComp f g).hom.app M (t ⊗ₜ[R₀, g.comp f] m)) ⊗ₜ[T₀]
            ((extendScalarsComp f g).hom.app X ((1 : T₀) ⊗ₜ[R₀, g.comp f] x)) = _
          exact congrArg₂ (fun a b => a ⊗ₜ[T₀] b) (hcomp M m t) (hcomp X x 1)

end ScalarComposition

section FlatScalarTower

universe u₀
variable (R₀ S₀ T₀ : Type u₀) [CommRing R₀] [CommRing S₀] [CommRing T₀]

/-- Scalar-extension association gives the actual lift between direct and iterated extended resolutions. -/
theorem flatScalarExtensionProjectiveResolution_assoc_augmentation
    (f : R₀ →+* S₀) (g : S₀ →+* T₀) (hf : f.Flat) (hg : g.Flat)
    {X : ModuleCat.{u₀} R₀} (P : ProjectiveResolution X) :
    letI : Algebra R₀ S₀ := f.toAlgebra
    letI : Algebra S₀ T₀ := g.toAlgebra
    letI : Algebra R₀ T₀ := (g.comp f).toAlgebra
    letI : Module.Flat R₀ S₀ := RingHom.flat_algebraMap_iff.mp hf
    letI : Module.Flat S₀ T₀ := RingHom.flat_algebraMap_iff.mp hg
    letI : Module.Flat R₀ T₀ := RingHom.flat_algebraMap_iff.mp (hf.comp hg)
    let Q := flatScalarExtensionProjectiveResolution.{u₀, u₀, 0} R₀ S₀ P
    let V := flatScalarExtensionProjectiveResolution.{u₀, u₀, 0} S₀ T₀ Q
    let W := flatScalarExtensionProjectiveResolution.{u₀, u₀, 0} R₀ T₀ P
    let θ := (NatIso.mapHomologicalComplex (extendScalarsComp f g) (ComplexShape.down ℕ)).hom.app P.complex
    θ.f 0 ≫ V.π.f 0 = W.π.f 0 ≫ (extendScalarsComp f g).hom.app X := by
  let : Algebra R₀ S₀ := f.toAlgebra
  let : Algebra S₀ T₀ := g.toAlgebra
  let : Algebra R₀ T₀ := (g.comp f).toAlgebra
  let : Module.Flat R₀ S₀ := RingHom.flat_algebraMap_iff.mp hf
  let : Module.Flat S₀ T₀ := RingHom.flat_algebraMap_iff.mp hg
  let : Module.Flat R₀ T₀ := RingHom.flat_algebraMap_iff.mp (hf.comp hg)
  let F := extendScalars f
  let G := extendScalars g
  let H := extendScalars (g.comp f)
  let Q := flatScalarExtensionProjectiveResolution.{u₀, u₀, 0} R₀ S₀ P
  let V := flatScalarExtensionProjectiveResolution.{u₀, u₀, 0} S₀ T₀ Q
  let W := flatScalarExtensionProjectiveResolution.{u₀, u₀, 0} R₀ T₀ P
  let a := extendScalarsComp f g
  let θ := (NatIso.mapHomologicalComplex a (ComplexShape.down ℕ)).hom.app P.complex
  let p₀ : P.complex.X 0 ⟶ X := P.π.f 0
  have hnat : a.hom.app (P.complex.X 0) ≫ G.map (F.map p₀) = H.map p₀ ≫ a.hom.app X :=
    (a.hom.naturality p₀).symm
  have hF : ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).hom.app X).f 0 =
      𝟙 (F.obj X) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  have hG : ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.down ℕ) 0).hom.app
      (F.obj X)).f 0 = 𝟙 (G.obj (F.obj X)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  have hH : ((HomologicalComplex.singleMapHomologicalComplex H (ComplexShape.down ℕ) 0).hom.app X).f 0 =
      𝟙 (H.obj X) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  change a.hom.app (P.complex.X 0) ≫
      (G.map (F.map p₀ ≫
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).hom.app X).f 0) ≫
          ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.down ℕ) 0).hom.app
            (F.obj X)).f 0) =
    (H.map p₀ ≫ ((HomologicalComplex.singleMapHomologicalComplex H (ComplexShape.down ℕ) 0).hom.app X).f 0) ≫
      a.hom.app X
  have hleft : G.map (F.map p₀ ≫ 𝟙 (F.obj X)) ≫ 𝟙 (G.obj (F.obj X)) = G.map (F.map p₀) :=
    (Category.comp_id _).trans (congrArg (fun m => G.map m) (Category.comp_id _))
  have hright : H.map p₀ ≫ 𝟙 (H.obj X) = H.map p₀ := Category.comp_id _
  rw [hF, hG, hH]
  exact (congrArg (fun m => a.hom.app (P.complex.X 0) ≫ m) hleft).trans
    (hnat.trans (congrArg (fun m => m ≫ a.hom.app X) hright).symm)

/-- The actual flat native Tor comparison agrees with two successive scalar extensions. -/
theorem flatScalarExtensionTorBaseChangeIso_hom_trans
    (f : R₀ →+* S₀) (g : S₀ →+* T₀) (hf : f.Flat) (hg : g.Flat)
    (M X : ModuleCat.{u₀} R₀) (q : ℕ) :
    letI : MonoidalCategoryStruct (ModuleCat.{u₀} R₀) := tensorStructure.{u₀, 0}
    letI : MonoidalCategoryStruct (ModuleCat.{u₀} S₀) := tensorStructure.{u₀, 0}
    letI : MonoidalCategoryStruct (ModuleCat.{u₀} T₀) := tensorStructure.{u₀, 0}
    letI : MonoidalCategory (ModuleCat.{u₀} R₀) := monoidalCategory.{u₀, 0}
    letI : MonoidalCategory (ModuleCat.{u₀} S₀) := monoidalCategory.{u₀, 0}
    letI : MonoidalCategory (ModuleCat.{u₀} T₀) := monoidalCategory.{u₀, 0}
    letI : MonoidalPreadditive (ModuleCat.{u₀} R₀) := monoidalPreadditive.{u₀, 0}
    letI : MonoidalPreadditive (ModuleCat.{u₀} S₀) := monoidalPreadditive.{u₀, 0}
    letI : MonoidalPreadditive (ModuleCat.{u₀} T₀) := monoidalPreadditive.{u₀, 0}
    letI : Algebra R₀ S₀ := f.toAlgebra
    letI : Algebra S₀ T₀ := g.toAlgebra
    letI : Algebra R₀ T₀ := (g.comp f).toAlgebra
    letI : Module.Flat R₀ S₀ := RingHom.flat_algebraMap_iff.mp hf
    letI : Module.Flat S₀ T₀ := RingHom.flat_algebraMap_iff.mp hg
    letI : Module.Flat R₀ T₀ := RingHom.flat_algebraMap_iff.mp (hf.comp hg)
    let F := extendScalars f
    let G := extendScalars g
    let H := extendScalars (g.comp f)
    (extendScalarsComp f g).hom.app (((Tor (ModuleCat.{u₀} R₀) q).obj M).obj X) ≫
      G.map (flatScalarExtensionTorBaseChangeIso R₀ S₀ M X q).hom ≫
        (flatScalarExtensionTorBaseChangeIso S₀ T₀ (F.obj M) (F.obj X) q).hom =
      (flatScalarExtensionTorBaseChangeIso R₀ T₀ M X q).hom ≫
        ((Tor (ModuleCat.{u₀} T₀) q).obj (H.obj M)).map ((extendScalarsComp f g).hom.app X) ≫
          ((Tor (ModuleCat.{u₀} T₀) q).map ((extendScalarsComp f g).hom.app M)).app (G.obj (F.obj X)) := by
  let : MonoidalCategoryStruct (ModuleCat.{u₀} R₀) := tensorStructure.{u₀, 0}
  let : MonoidalCategoryStruct (ModuleCat.{u₀} S₀) := tensorStructure.{u₀, 0}
  let : MonoidalCategoryStruct (ModuleCat.{u₀} T₀) := tensorStructure.{u₀, 0}
  let : MonoidalCategory (ModuleCat.{u₀} R₀) := monoidalCategory.{u₀, 0}
  let : MonoidalCategory (ModuleCat.{u₀} S₀) := monoidalCategory.{u₀, 0}
  let : MonoidalCategory (ModuleCat.{u₀} T₀) := monoidalCategory.{u₀, 0}
  let : MonoidalPreadditive (ModuleCat.{u₀} R₀) := monoidalPreadditive.{u₀, 0}
  let : MonoidalPreadditive (ModuleCat.{u₀} S₀) := monoidalPreadditive.{u₀, 0}
  let : MonoidalPreadditive (ModuleCat.{u₀} T₀) := monoidalPreadditive.{u₀, 0}
  let : Algebra R₀ S₀ := f.toAlgebra
  let : Algebra S₀ T₀ := g.toAlgebra
  let : Algebra R₀ T₀ := (g.comp f).toAlgebra
  let : Module.Flat R₀ S₀ := RingHom.flat_algebraMap_iff.mp hf
  let : Module.Flat S₀ T₀ := RingHom.flat_algebraMap_iff.mp hg
  let : Module.Flat R₀ T₀ := RingHom.flat_algebraMap_iff.mp (hf.comp hg)
  let F := extendScalars f
  let G := extendScalars g
  let H := extendScalars (g.comp f)
  let : F.PreservesHomology := preservesHomology_extendScalars_of_flat f hf
  let : G.PreservesHomology := preservesHomology_extendScalars_of_flat g hg
  let : H.PreservesHomology := preservesHomology_extendScalars_of_flat (g.comp f) (hf.comp hg)
  let : (F ⋙ G).PreservesHomology := by
    apply Functor.preservesHomology_of_map_exact
    intro C hC
    exact (hC.map F).map G
  let a := extendScalarsComp f g
  let P := projectiveResolution X
  let Q := flatScalarExtensionProjectiveResolution R₀ S₀ P
  let V := flatScalarExtensionProjectiveResolution S₀ T₀ Q
  let W := flatScalarExtensionProjectiveResolution R₀ T₀ P
  let L := (tensoringLeft (ModuleCat.{u₀} R₀)).obj M
  let Lₛ := (tensoringLeft (ModuleCat.{u₀} S₀)).obj (F.obj M)
  let Lₕ := (tensoringLeft (ModuleCat.{u₀} T₀)).obj (H.obj M)
  let Lₜ := (tensoringLeft (ModuleCat.{u₀} T₀)).obj (G.obj (F.obj M))
  let K := (L.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let J := (Lₛ.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  let D := (Lₕ.mapHomologicalComplex (ComplexShape.down ℕ)).obj W.complex
  let E := (Lₜ.mapHomologicalComplex (ComplexShape.down ℕ)).obj V.complex
  let c₁ : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ≅ J :=
    (NatIso.mapHomologicalComplex (scalarExtensionTensorNatIso R₀ S₀ f M)
      (ComplexShape.down ℕ)).app P.complex
  let c₂ : (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj J ≅ E :=
    (NatIso.mapHomologicalComplex (scalarExtensionTensorNatIso S₀ T₀ g (F.obj M))
      (ComplexShape.down ℕ)).app Q.complex
  let c₃ : (H.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ≅ D :=
    (NatIso.mapHomologicalComplex (scalarExtensionTensorNatIso R₀ T₀ (g.comp f) M)
      (ComplexShape.down ℕ)).app P.complex
  let θ := (NatIso.mapHomologicalComplex a (ComplexShape.down ℕ)).hom.app P.complex
  let κ : D ⟶ E := (Lₕ.mapHomologicalComplex (ComplexShape.down ℕ)).map θ ≫
    (NatTrans.mapHomologicalComplex ((tensoringLeft (ModuleCat.{u₀} T₀)).map (a.hom.app M))
      (ComplexShape.down ℕ)).app V.complex
  let ZR := HomologicalComplex.homologyFunctor (ModuleCat.{u₀} R₀) (ComplexShape.down ℕ) q
  let ZS := HomologicalComplex.homologyFunctor (ModuleCat.{u₀} S₀) (ComplexShape.down ℕ) q
  let Z := HomologicalComplex.homologyFunctor (ModuleCat.{u₀} T₀) (ComplexShape.down ℕ) q
  let θK := (NatIso.mapHomologicalComplex a (ComplexShape.down ℕ)).hom.app K
  let T := ((Tor (ModuleCat.{u₀} R₀) q).obj M).obj X
  let TS := ((Tor (ModuleCat.{u₀} S₀) q).obj (F.obj M)).obj (F.obj X)
  let TH := ((Tor (ModuleCat.{u₀} T₀) q).obj (H.obj M)).obj (H.obj X)
  let TT := ((Tor (ModuleCat.{u₀} T₀) q).obj (G.obj (F.obj M))).obj (G.obj (F.obj X))
  let β₁ : F.obj T ≅ TS := flatScalarExtensionTorBaseChangeIso R₀ S₀ M X q
  let β₂ : G.obj TS ≅ TT := flatScalarExtensionTorBaseChangeIso S₀ T₀ (F.obj M) (F.obj X) q
  let β₃ : H.obj T ≅ TH := flatScalarExtensionTorBaseChangeIso R₀ T₀ M X q
  let eQ : TS ≅ ZS.obj J := Q.isoLeftDerivedObj Lₛ q
  let eW : TH ≅ Z.obj D := W.isoLeftDerivedObj Lₕ q
  let eV : TT ≅ Z.obj E := V.isoLeftDerivedObj Lₜ q
  let aR : T ⟶ ZR.obj K := (P.isoLeftDerivedObj L q).hom
  let b₁ : F.obj (ZR.obj K) ⟶ ZS.obj ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) :=
    (HomologicalComplex.mapHomologyFunctorIso q F).inv.app K
  let b₂ : G.obj (ZS.obj J) ⟶ Z.obj ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj J) :=
    (HomologicalComplex.mapHomologyFunctorIso q G).inv.app J
  let b₂' := (HomologicalComplex.mapHomologyFunctorIso q G).inv.app
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K)
  let b₃ : H.obj (ZR.obj K) ⟶ Z.obj ((H.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) :=
    (HomologicalComplex.mapHomologyFunctorIso q H).inv.app K
  let bFG := (HomologicalComplex.mapHomologyFunctorIso q (F ⋙ G)).inv.app K
  let c₁H := ZS.map c₁.hom
  let c₂H := Z.map c₂.hom
  let c₃H := Z.map c₃.hom
  let d := (G.mapHomologicalComplex (ComplexShape.down ℕ)).map c₁.hom
  have hθ : θ.f 0 ≫ V.π.f 0 = W.π.f 0 ≫ a.hom.app X :=
    flatScalarExtensionProjectiveResolution_assoc_augmentation R₀ S₀ T₀ f g hf hg P
  let Φ : ProjectiveResolution.Hom W V (a.hom.app X) :=
    { hom := θ, hom_f_zero_comp_π_f_zero := by
        rw [ChainComplex.single₀_map_f_zero]
        exact hθ }
  let τ : TH ⟶ TT := ((Tor (ModuleCat.{u₀} T₀) q).obj (H.obj M)).map (a.hom.app X) ≫
    ((Tor (ModuleCat.{u₀} T₀) q).map (a.hom.app M)).app (G.obj (F.obj X))
  have hTor : τ = eW.hom ≫ Z.map κ ≫ eV.inv := by
    exact Functor.LeftDerivedBalance.deriveSecond_map_computation
      (tensoringLeft (ModuleCat.{u₀} T₀)) q (a.hom.app M) (a.hom.app X) W V θ Φ.hom_comp_π
  have hChain : θK ≫ d ≫ c₂.hom = c₃.hom ≫ κ := by
    apply HomologicalComplex.Hom.ext
    funext n
    have h := scalarExtensionTensorIso_hom_trans R₀ S₀ T₀ f g M (P.complex.X n)
    have hn := ((tensoringLeft (ModuleCat.{u₀} T₀)).map (a.hom.app M)).naturality
      (a.hom.app (P.complex.X n))
    exact h.trans (congrArg (fun m => (scalarExtensionTensorIso R₀ T₀ (g.comp f) M (P.complex.X n)).hom ≫ m)
      hn.symm)
  have hChainH : Z.map θK ≫ Z.map d ≫ c₂H = c₃H ≫ Z.map κ := by
    have h : Z.map (θK ≫ d ≫ c₂.hom) = Z.map (c₃.hom ≫ κ) := congrArg (fun m => Z.map m) hChain
    exact ((Z.map_comp θK (d ≫ c₂.hom)).trans
      (congrArg (fun m => Z.map θK ≫ m) (Z.map_comp d c₂.hom))).symm.trans
        (h.trans (Z.map_comp c₃.hom κ))
  have hG : G.map c₁H ≫ b₂ = b₂' ≫ Z.map d := by
    exact (HomologicalComplex.mapHomologyFunctorIso q G).inv.naturality c₁.hom
  have hComp : G.map b₁ ≫ b₂' = bFG := by
    exact (ShortComplex.mapHomologyIso_comp_inv (K.sc q) F G).symm
  have hNat : a.hom.app (ZR.obj K) ≫ bFG = b₃ ≫ Z.map θK := by
    exact NatTrans.app_homology_comp_mapHomologyIso_inv a.hom (K.sc q)
  have hβ₁ : β₁.hom = F.map aR ≫ b₁ ≫ c₁H ≫ eQ.inv :=
    flatScalarExtensionTorBaseChangeIso_hom_computation R₀ S₀ M X q
  have hβ₂ : β₂.hom = G.map eQ.hom ≫ b₂ ≫ c₂H ≫ eV.inv :=
    flatScalarExtensionTorBaseChangeIso_hom_computation_of_resolution S₀ T₀
      (F.obj M) (F.obj X) q Q
  have hβ₃ : β₃.hom = H.map aR ≫ b₃ ≫ c₃H ≫ eW.inv :=
    flatScalarExtensionTorBaseChangeIso_hom_computation R₀ T₀ M X q
  have hGF : G.map β₁.hom = G.map (F.map aR) ≫ G.map b₁ ≫ G.map c₁H ≫ G.map eQ.inv := by
    have h := congrArg (fun m => G.map m) hβ₁
    have hm := (G.map_comp (F.map aR) (b₁ ≫ c₁H ≫ eQ.inv)).trans
      (congrArg (fun m => G.map (F.map aR) ≫ m)
        ((G.map_comp b₁ (c₁H ≫ eQ.inv)).trans
          (congrArg (fun m => G.map b₁ ≫ m) (G.map_comp c₁H eQ.inv))))
    exact h.trans hm
  let t : H.obj T ⟶ G.obj (F.obj T) := a.hom.app T
  let u := G.map (F.map aR)
  let v := G.map c₁H
  let aK := a.hom.app (ZR.obj K)
  have hPrefix : t ≫ u = H.map aR ≫ aK := (a.hom.naturality aR).symm
  have hCancel : G.map eQ.inv ≫ (G.map eQ.hom ≫ b₂ ≫ c₂H ≫ eV.inv) = b₂ ≫ c₂H ≫ eV.inv :=
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun m => m ≫ (b₂ ≫ c₂H ≫ eV.inv)) (G.mapIso eQ).inv_hom_id)).trans
        (Category.id_comp _)
  have hStep : t ≫ G.map β₁.hom ≫ β₂.hom = t ≫ u ≫ G.map b₁ ≫ v ≫ b₂ ≫ c₂H ≫ eV.inv := by
    have h := congrArg₂ (fun x y => t ≫ x ≫ y) hGF hβ₂
    apply h.trans
    simp only [Category.assoc]
    exact congrArg (fun m => t ≫ u ≫ G.map b₁ ≫ v ≫ m) hCancel
  have hTail : aK ≫ G.map b₁ ≫ v ≫ b₂ ≫ c₂H = b₃ ≫ c₃H ≫ Z.map κ := by
    have h₁ := congrArg (fun m => aK ≫ G.map b₁ ≫ m ≫ c₂H) hG
    have h₂ := congrArg (fun m => aK ≫ m ≫ Z.map d ≫ c₂H) hComp
    have h₃ := congrArg (fun m => m ≫ Z.map d ≫ c₂H) hNat
    have h₄ := congrArg (fun m => b₃ ≫ m) hChainH
    calc
      _ = aK ≫ G.map b₁ ≫ (v ≫ b₂) ≫ c₂H := by simp only [Category.assoc]
      _ = aK ≫ G.map b₁ ≫ (b₂' ≫ Z.map d) ≫ c₂H := h₁
      _ = (aK ≫ bFG) ≫ Z.map d ≫ c₂H := by
        simpa only [Category.assoc] using h₂
      _ = (b₃ ≫ Z.map θK) ≫ Z.map d ≫ c₂H := h₃
      _ = _ := by simpa only [Category.assoc] using h₄
  have hLeft : t ≫ G.map β₁.hom ≫ β₂.hom = H.map aR ≫ b₃ ≫ c₃H ≫ Z.map κ ≫ eV.inv := by
    have hp := congrArg (fun m => m ≫ G.map b₁ ≫ v ≫ b₂ ≫ c₂H ≫ eV.inv) hPrefix
    have ht := congrArg (fun m => H.map aR ≫ m ≫ eV.inv) hTail
    apply hStep.trans
    calc
      _ = (t ≫ u) ≫ G.map b₁ ≫ v ≫ b₂ ≫ c₂H ≫ eV.inv := by simp only [Category.assoc]
      _ = (H.map aR ≫ aK) ≫ G.map b₁ ≫ v ≫ b₂ ≫ c₂H ≫ eV.inv := hp
      _ = H.map aR ≫ (aK ≫ G.map b₁ ≫ v ≫ b₂ ≫ c₂H) ≫ eV.inv := by simp only [Category.assoc]
      _ = _ := ht
  have hRight : β₃.hom ≫ τ = H.map aR ≫ b₃ ≫ c₃H ≫ Z.map κ ≫ eV.inv := by
    have h := congrArg₂ (fun x y => x ≫ y) hβ₃ hTor
    apply h.trans
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change t ≫ G.map β₁.hom ≫ β₂.hom = β₃.hom ≫ τ
  exact hLeft.trans hRight.symm

/-- Equal actual flat ring maps give the same native Tor comparison under canonical scalar transport. -/
theorem flatScalarExtensionTorBaseChangeIso_hom_congr
    (f f' : R₀ →+* S₀) (hf : f.Flat) (hf' : f'.Flat) (h : f = f')
    (M X : ModuleCat.{u₀} R₀) (q : ℕ) :
    letI : MonoidalCategoryStruct (ModuleCat.{u₀} R₀) := tensorStructure.{u₀, 0}
    letI : MonoidalCategoryStruct (ModuleCat.{u₀} S₀) := tensorStructure.{u₀, 0}
    letI : MonoidalCategory (ModuleCat.{u₀} R₀) := monoidalCategory.{u₀, 0}
    letI : MonoidalCategory (ModuleCat.{u₀} S₀) := monoidalCategory.{u₀, 0}
    letI : MonoidalPreadditive (ModuleCat.{u₀} R₀) := monoidalPreadditive.{u₀, 0}
    letI : MonoidalPreadditive (ModuleCat.{u₀} S₀) := monoidalPreadditive.{u₀, 0}
    let A := ((Tor (ModuleCat.{u₀} R₀) q).obj M).obj X
    let β₀ : (extendScalars f).obj A ≅
        ((Tor (ModuleCat.{u₀} S₀) q).obj ((extendScalars f).obj M)).obj ((extendScalars f).obj X) := by
      letI : Algebra R₀ S₀ := f.toAlgebra
      letI : Module.Flat R₀ S₀ := RingHom.flat_algebraMap_iff.mp hf
      exact flatScalarExtensionTorBaseChangeIso R₀ S₀ M X q
    let β₁ : (extendScalars f').obj A ≅
        ((Tor (ModuleCat.{u₀} S₀) q).obj ((extendScalars f').obj M)).obj ((extendScalars f').obj X) := by
      letI : Algebra R₀ S₀ := f'.toAlgebra
      letI : Module.Flat R₀ S₀ := RingHom.flat_algebraMap_iff.mp hf'
      exact flatScalarExtensionTorBaseChangeIso R₀ S₀ M X q
    let eM := eqToHom (congrArg (fun k => (extendScalars k).obj M) h)
    let eX := eqToHom (congrArg (fun k => (extendScalars k).obj X) h)
    let eA := eqToHom (congrArg (fun k => (extendScalars k).obj A) h)
    β₀.hom ≫ ((Tor (ModuleCat.{u₀} S₀) q).map eM).app ((extendScalars f).obj X) ≫
      ((Tor (ModuleCat.{u₀} S₀) q).obj ((extendScalars f').obj M)).map eX = eA ≫ β₁.hom := by
  subst f'
  let : MonoidalCategoryStruct (ModuleCat.{u₀} R₀) := tensorStructure.{u₀, 0}
  let : MonoidalCategoryStruct (ModuleCat.{u₀} S₀) := tensorStructure.{u₀, 0}
  let : MonoidalCategory (ModuleCat.{u₀} R₀) := monoidalCategory.{u₀, 0}
  let : MonoidalCategory (ModuleCat.{u₀} S₀) := monoidalCategory.{u₀, 0}
  let : MonoidalPreadditive (ModuleCat.{u₀} R₀) := monoidalPreadditive.{u₀, 0}
  let : MonoidalPreadditive (ModuleCat.{u₀} S₀) := monoidalPreadditive.{u₀, 0}
  let : Algebra R₀ S₀ := f.toAlgebra
  let : Module.Flat R₀ S₀ := RingHom.flat_algebraMap_iff.mp hf
  let F := extendScalars f
  let A := ((Tor (ModuleCat.{u₀} R₀) q).obj M).obj X
  let b : F.obj A ⟶ ((Tor (ModuleCat.{u₀} S₀) q).obj (F.obj M)).obj (F.obj X) :=
    (flatScalarExtensionTorBaseChangeIso R₀ S₀ M X q).hom
  change b ≫ ((Tor (ModuleCat.{u₀} S₀) q).map (𝟙 (F.obj M))).app (F.obj X) ≫
    ((Tor (ModuleCat.{u₀} S₀) q).obj (F.obj M)).map (𝟙 (F.obj X)) = 𝟙 (F.obj A) ≫ b
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id]

/-- Canonical scalar transport retains the actual maps in both Tor coefficients. -/
theorem flatScalarExtensionTorBaseChangeIso_hom_congr_coefficients
    (f f' : R₀ →+* S₀) (hf : f.Flat) (hf' : f'.Flat) (h : f = f')
    (M X : ModuleCat.{u₀} R₀) (N Y : ModuleCat.{u₀} S₀)
    (α : (extendScalars f').obj M ⟶ N) (ξ : (extendScalars f').obj X ⟶ Y) (q : ℕ) :
    letI : MonoidalCategoryStruct (ModuleCat.{u₀} R₀) := tensorStructure.{u₀, 0}
    letI : MonoidalCategoryStruct (ModuleCat.{u₀} S₀) := tensorStructure.{u₀, 0}
    letI : MonoidalCategory (ModuleCat.{u₀} R₀) := monoidalCategory.{u₀, 0}
    letI : MonoidalCategory (ModuleCat.{u₀} S₀) := monoidalCategory.{u₀, 0}
    letI : MonoidalPreadditive (ModuleCat.{u₀} R₀) := monoidalPreadditive.{u₀, 0}
    letI : MonoidalPreadditive (ModuleCat.{u₀} S₀) := monoidalPreadditive.{u₀, 0}
    let A := ((Tor (ModuleCat.{u₀} R₀) q).obj M).obj X
    let β₀ : (extendScalars f).obj A ≅
        ((Tor (ModuleCat.{u₀} S₀) q).obj ((extendScalars f).obj M)).obj ((extendScalars f).obj X) := by
      letI : Algebra R₀ S₀ := f.toAlgebra
      letI : Module.Flat R₀ S₀ := RingHom.flat_algebraMap_iff.mp hf
      exact flatScalarExtensionTorBaseChangeIso R₀ S₀ M X q
    let β₁ : (extendScalars f').obj A ≅
        ((Tor (ModuleCat.{u₀} S₀) q).obj ((extendScalars f').obj M)).obj ((extendScalars f').obj X) := by
      letI : Algebra R₀ S₀ := f'.toAlgebra
      letI : Module.Flat R₀ S₀ := RingHom.flat_algebraMap_iff.mp hf'
      exact flatScalarExtensionTorBaseChangeIso R₀ S₀ M X q
    let eM := eqToHom (congrArg (fun k => (extendScalars k).obj M) h)
    let eX := eqToHom (congrArg (fun k => (extendScalars k).obj X) h)
    let eA := eqToHom (congrArg (fun k => (extendScalars k).obj A) h)
    β₀.hom ≫ ((Tor (ModuleCat.{u₀} S₀) q).map (eM ≫ α)).app ((extendScalars f).obj X) ≫
      ((Tor (ModuleCat.{u₀} S₀) q).obj N).map (eX ≫ ξ) =
    eA ≫ β₁.hom ≫ ((Tor (ModuleCat.{u₀} S₀) q).map α).app ((extendScalars f').obj X) ≫
      ((Tor (ModuleCat.{u₀} S₀) q).obj N).map ξ := by
  subst f'
  let : MonoidalCategoryStruct (ModuleCat.{u₀} R₀) := tensorStructure.{u₀, 0}
  let : MonoidalCategoryStruct (ModuleCat.{u₀} S₀) := tensorStructure.{u₀, 0}
  let : MonoidalCategory (ModuleCat.{u₀} R₀) := monoidalCategory.{u₀, 0}
  let : MonoidalCategory (ModuleCat.{u₀} S₀) := monoidalCategory.{u₀, 0}
  let : MonoidalPreadditive (ModuleCat.{u₀} R₀) := monoidalPreadditive.{u₀, 0}
  let : MonoidalPreadditive (ModuleCat.{u₀} S₀) := monoidalPreadditive.{u₀, 0}
  let : Algebra R₀ S₀ := f.toAlgebra
  let : Module.Flat R₀ S₀ := RingHom.flat_algebraMap_iff.mp hf
  let F := extendScalars f
  let A := ((Tor (ModuleCat.{u₀} R₀) q).obj M).obj X
  let b : F.obj A ⟶ ((Tor (ModuleCat.{u₀} S₀) q).obj (F.obj M)).obj (F.obj X) :=
    (flatScalarExtensionTorBaseChangeIso R₀ S₀ M X q).hom
  change b ≫ ((Tor (ModuleCat.{u₀} S₀) q).map (𝟙 (F.obj M) ≫ α)).app (F.obj X) ≫
    ((Tor (ModuleCat.{u₀} S₀) q).obj N).map (𝟙 (F.obj X) ≫ ξ) =
    𝟙 (F.obj A) ≫ b ≫ ((Tor (ModuleCat.{u₀} S₀) q).map α).app (F.obj X) ≫
      ((Tor (ModuleCat.{u₀} S₀) q).obj N).map ξ
  simp only [Category.id_comp]

/-- The scalar cocycle retains arbitrary actual maps in both original Tor coefficients. -/
theorem flatScalarExtensionTorBaseChangeIso_hom_trans_coefficients
    (f : R₀ →+* S₀) (g : S₀ →+* T₀) (hf : f.Flat) (hg : g.Flat)
    (M X : ModuleCat.{u₀} R₀) (N Y : ModuleCat.{u₀} S₀) (P Z : ModuleCat.{u₀} T₀)
    (α : (extendScalars f).obj M ⟶ N) (ξ : (extendScalars f).obj X ⟶ Y)
    (β : (extendScalars g).obj N ⟶ P) (ζ : (extendScalars g).obj Y ⟶ Z) (q : ℕ) :
    letI : MonoidalCategoryStruct (ModuleCat.{u₀} R₀) := tensorStructure.{u₀, 0}
    letI : MonoidalCategoryStruct (ModuleCat.{u₀} S₀) := tensorStructure.{u₀, 0}
    letI : MonoidalCategoryStruct (ModuleCat.{u₀} T₀) := tensorStructure.{u₀, 0}
    letI : MonoidalCategory (ModuleCat.{u₀} R₀) := monoidalCategory.{u₀, 0}
    letI : MonoidalCategory (ModuleCat.{u₀} S₀) := monoidalCategory.{u₀, 0}
    letI : MonoidalCategory (ModuleCat.{u₀} T₀) := monoidalCategory.{u₀, 0}
    letI : MonoidalPreadditive (ModuleCat.{u₀} R₀) := monoidalPreadditive.{u₀, 0}
    letI : MonoidalPreadditive (ModuleCat.{u₀} S₀) := monoidalPreadditive.{u₀, 0}
    letI : MonoidalPreadditive (ModuleCat.{u₀} T₀) := monoidalPreadditive.{u₀, 0}
    letI : Algebra R₀ S₀ := f.toAlgebra
    letI : Algebra S₀ T₀ := g.toAlgebra
    letI : Algebra R₀ T₀ := (g.comp f).toAlgebra
    letI : Module.Flat R₀ S₀ := RingHom.flat_algebraMap_iff.mp hf
    letI : Module.Flat S₀ T₀ := RingHom.flat_algebraMap_iff.mp hg
    letI : Module.Flat R₀ T₀ := RingHom.flat_algebraMap_iff.mp (hf.comp hg)
    let F := extendScalars f
    let G := extendScalars g
    let H := extendScalars (g.comp f)
    let a := extendScalarsComp f g
    a.hom.app (((Tor (ModuleCat.{u₀} R₀) q).obj M).obj X) ≫
      G.map ((flatScalarExtensionTorBaseChangeIso R₀ S₀ M X q).hom ≫
        ((Tor (ModuleCat.{u₀} S₀) q).map α).app (F.obj X) ≫
          ((Tor (ModuleCat.{u₀} S₀) q).obj N).map ξ) ≫
      (flatScalarExtensionTorBaseChangeIso S₀ T₀ N Y q).hom ≫
        ((Tor (ModuleCat.{u₀} T₀) q).map β).app (G.obj Y) ≫
          ((Tor (ModuleCat.{u₀} T₀) q).obj P).map ζ =
    (flatScalarExtensionTorBaseChangeIso R₀ T₀ M X q).hom ≫
      ((Tor (ModuleCat.{u₀} T₀) q).map (a.hom.app M ≫ G.map α ≫ β)).app (H.obj X) ≫
        ((Tor (ModuleCat.{u₀} T₀) q).obj P).map (a.hom.app X ≫ G.map ξ ≫ ζ) := by
  let : MonoidalCategoryStruct (ModuleCat.{u₀} R₀) := tensorStructure.{u₀, 0}
  let : MonoidalCategoryStruct (ModuleCat.{u₀} S₀) := tensorStructure.{u₀, 0}
  let : MonoidalCategoryStruct (ModuleCat.{u₀} T₀) := tensorStructure.{u₀, 0}
  let : MonoidalCategory (ModuleCat.{u₀} R₀) := monoidalCategory.{u₀, 0}
  let : MonoidalCategory (ModuleCat.{u₀} S₀) := monoidalCategory.{u₀, 0}
  let : MonoidalCategory (ModuleCat.{u₀} T₀) := monoidalCategory.{u₀, 0}
  let : MonoidalPreadditive (ModuleCat.{u₀} R₀) := monoidalPreadditive.{u₀, 0}
  let : MonoidalPreadditive (ModuleCat.{u₀} S₀) := monoidalPreadditive.{u₀, 0}
  let : MonoidalPreadditive (ModuleCat.{u₀} T₀) := monoidalPreadditive.{u₀, 0}
  let : Algebra R₀ S₀ := f.toAlgebra
  let : Algebra S₀ T₀ := g.toAlgebra
  let : Algebra R₀ T₀ := (g.comp f).toAlgebra
  let : Module.Flat R₀ S₀ := RingHom.flat_algebraMap_iff.mp hf
  let : Module.Flat S₀ T₀ := RingHom.flat_algebraMap_iff.mp hg
  let : Module.Flat R₀ T₀ := RingHom.flat_algebraMap_iff.mp (hf.comp hg)
  let F := extendScalars f
  let G := extendScalars g
  let H := extendScalars (g.comp f)
  let a := extendScalarsComp f g
  let TS := Tor (ModuleCat.{u₀} S₀) q
  let TT := Tor (ModuleCat.{u₀} T₀) q
  let BS : ModuleCat.{u₀} S₀ × ModuleCat.{u₀} S₀ ⥤ ModuleCat.{u₀} S₀ := Functor.uncurry.obj TS
  let BT : ModuleCat.{u₀} T₀ × ModuleCat.{u₀} T₀ ⥤ ModuleCat.{u₀} T₀ := Functor.uncurry.obj TT
  let A := ((Tor (ModuleCat.{u₀} R₀) q).obj M).obj X
  let t : H.obj A ⟶ G.obj (F.obj A) := a.hom.app A
  let b₁ : F.obj A ⟶ BS.obj (F.obj M, F.obj X) :=
    (flatScalarExtensionTorBaseChangeIso R₀ S₀ M X q).hom
  let bA : G.obj (BS.obj (F.obj M, F.obj X)) ⟶ BT.obj (G.obj (F.obj M), G.obj (F.obj X)) :=
    (flatScalarExtensionTorBaseChangeIso S₀ T₀ (F.obj M) (F.obj X) q).hom
  let bN : G.obj (BS.obj (N, F.obj X)) ⟶ BT.obj (G.obj N, G.obj (F.obj X)) :=
    (flatScalarExtensionTorBaseChangeIso S₀ T₀ N (F.obj X) q).hom
  let b₂ : G.obj (BS.obj (N, Y)) ⟶ BT.obj (G.obj N, G.obj Y) :=
    (flatScalarExtensionTorBaseChangeIso S₀ T₀ N Y q).hom
  let b₃ : H.obj A ⟶ BT.obj (H.obj M, H.obj X) :=
    (flatScalarExtensionTorBaseChangeIso R₀ T₀ M X q).hom
  let cS : BS.obj (F.obj M, F.obj X) ⟶ BS.obj (N, F.obj X) := (TS.map α).app (F.obj X)
  let dS : BS.obj (N, F.obj X) ⟶ BS.obj (N, Y) := (TS.obj N).map ξ
  let cT : BT.obj (G.obj (F.obj M), G.obj (F.obj X)) ⟶ BT.obj (G.obj N, G.obj (F.obj X)) :=
    (TT.map (G.map α)).app (G.obj (F.obj X))
  let dT : BT.obj (G.obj N, G.obj (F.obj X)) ⟶ BT.obj (G.obj N, G.obj Y) :=
    (TT.obj (G.obj N)).map (G.map ξ)
  let μS : BS.obj (F.obj M, F.obj X) ⟶ BS.obj (N, Y) := BS.map (α, ξ)
  let μT : BT.obj (G.obj (F.obj M), G.obj (F.obj X)) ⟶ BT.obj (G.obj N, G.obj Y) :=
    BT.map (G.map α, G.map ξ)
  let μa : BT.obj (H.obj M, H.obj X) ⟶ BT.obj (G.obj (F.obj M), G.obj (F.obj X)) :=
    BT.map (a.hom.app M, a.hom.app X)
  let ν₂ : BT.obj (G.obj N, G.obj Y) ⟶ BT.obj (P, Z) := BT.map (β, ζ)
  let ν : BT.obj (H.obj M, H.obj X) ⟶ BT.obj (P, Z) :=
    BT.map (a.hom.app M ≫ G.map α ≫ β, a.hom.app X ≫ G.map ξ ≫ ζ)
  have hC : G.map cS ≫ bN = bA ≫ cT :=
    flatScalarExtensionTorBaseChangeIso_hom_naturality_coefficient S₀ T₀ α (F.obj X) q
  have hD : G.map dS ≫ b₂ = bN ≫ dT :=
    flatScalarExtensionTorBaseChangeIso_hom_naturality_resolved S₀ T₀ N ξ q
  have hNat : G.map μS ≫ b₂ = bA ≫ μT := by
    have hm : G.map μS = G.map cS ≫ G.map dS := G.map_comp cS dS
    calc
      _ = (G.map cS ≫ G.map dS) ≫ b₂ := congrArg (fun k => k ≫ b₂) hm
      _ = G.map cS ≫ (bN ≫ dT) :=
        (Category.assoc _ _ _).trans (congrArg (fun k => G.map cS ≫ k) hD)
      _ = (bA ≫ cT) ≫ dT :=
        (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ dT) hC)
      _ = _ := Category.assoc _ _ _
  have hCocycle : t ≫ G.map b₁ ≫ bA = b₃ ≫ μa := by
    have h := flatScalarExtensionTorBaseChangeIso_hom_trans R₀ S₀ T₀ f g hf hg M X q
    let r := (TT.obj (H.obj M)).map (a.hom.app X)
    let c := (TT.map (a.hom.app M)).app (G.obj (F.obj X))
    have hs : r ≫ c = μa := (TT.map (a.hom.app M)).naturality (a.hom.app X)
    exact h.trans (congrArg (fun k => b₃ ≫ k) hs)
  have hMaps : μa ≫ μT ≫ ν₂ = ν := by
    let aPair : (H.obj M, H.obj X) ⟶ (G.obj (F.obj M), G.obj (F.obj X)) :=
      (a.hom.app M, a.hom.app X)
    let bPair : (G.obj (F.obj M), G.obj (F.obj X)) ⟶ (G.obj N, G.obj Y) := (G.map α, G.map ξ)
    let cPair : (G.obj N, G.obj Y) ⟶ (P, Z) := (β, ζ)
    let dPair : (H.obj M, H.obj X) ⟶ (P, Z) :=
      (a.hom.app M ≫ G.map α ≫ β, a.hom.app X ≫ G.map ξ ≫ ζ)
    have hp : aPair ≫ bPair ≫ cPair = dPair := rfl
    have hm := (BT.map_comp aPair (bPair ≫ cPair)).trans
      (congrArg (fun k => BT.map aPair ≫ k) (BT.map_comp bPair cPair))
    exact hm.symm.trans (congrArg (fun k => BT.map k) hp)
  change t ≫ G.map (b₁ ≫ μS) ≫ b₂ ≫ ν₂ = b₃ ≫ ν
  have hm := congrArg (fun k => t ≫ k ≫ b₂ ≫ ν₂) (G.map_comp b₁ μS)
  calc
    _ = t ≫ G.map b₁ ≫ G.map μS ≫ b₂ ≫ ν₂ := by
      simpa only [Category.assoc] using hm
    _ = (t ≫ G.map b₁ ≫ bA) ≫ μT ≫ ν₂ := by
      simpa only [Category.assoc] using congrArg (fun k => t ≫ G.map b₁ ≫ k ≫ ν₂) hNat
    _ = (b₃ ≫ μa) ≫ μT ≫ ν₂ := congrArg (fun k => k ≫ μT ≫ ν₂) hCocycle
    _ = b₃ ≫ ν := by
      simpa only [Category.assoc] using congrArg (fun k => b₃ ≫ k) hMaps

end FlatScalarTower

section ScalarIdentity

universe u₀
variable (R₀ : Type u₀) [CommRing R₀]

/-- The original scalar tensor comparison along the ring identity has its actual identity value. -/
theorem scalarExtensionTensorIso_hom_id (M X : ModuleCat.{u₀} R₀) :
    letI : MonoidalCategoryStruct (ModuleCat.{u₀} R₀) := tensorStructure.{u₀, 0}
    letI : MonoidalCategory (ModuleCat.{u₀} R₀) := monoidalCategory.{u₀, 0}
    let F := extendScalars (RingHom.id R₀)
    (scalarExtensionTensorIso R₀ R₀ (RingHom.id R₀) M X).hom ≫
      ((tensoringLeft (ModuleCat.{u₀} R₀)).obj (F.obj M)).map ((extendScalarsId R₀).hom.app X) ≫
        ((tensoringLeft (ModuleCat.{u₀} R₀)).map ((extendScalarsId R₀).hom.app M)).app X =
      (extendScalarsId R₀).hom.app (M ⊗ X) := by
  let : MonoidalCategoryStruct (ModuleCat.{u₀} R₀) := tensorStructure.{u₀, 0}
  let : MonoidalCategory (ModuleCat.{u₀} R₀) := monoidalCategory.{u₀, 0}
  let : Algebra R₀ R₀ := (RingHom.id R₀).toAlgebra
  let F := extendScalars (RingHom.id R₀)
  let e := extendScalarsId R₀
  let lhs : F.obj (M ⊗ X) ⟶ M ⊗ X :=
    (scalarExtensionTensorIso R₀ R₀ (RingHom.id R₀) M X).hom ≫
      ((tensoringLeft (ModuleCat.{u₀} R₀)).obj (F.obj M)).map (e.hom.app X) ≫
        ((tensoringLeft (ModuleCat.{u₀} R₀)).map (e.hom.app M)).app X
  have hid (N : ModuleCat.{u₀} R₀) (n : N) (r : R₀) :
      e.hom.app N (r ⊗ₜ[R₀, RingHom.id R₀] n) = r • n := by
    have hs : r • ((1 : R₀) ⊗ₜ[R₀, RingHom.id R₀] n) = r ⊗ₜ[R₀, RingHom.id R₀] n := by
      change r • ((1 : R₀) ⊗ₜ[R₀] n) = _
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h := (e.hom.app N).hom.map_smul r ((1 : R₀) ⊗ₜ[R₀, RingHom.id R₀] n)
    exact (congrArg (fun y => e.hom.app N y) hs).symm.trans
      (h.trans (congrArg (fun y : N => r • y) (extendScalarsId_hom_app_one_tmul N n)))
  apply ModuleCat.hom_ext
  change lhs.hom = (e.hom.app (M ⊗ X)).hom
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' =>
      exact (lhs.hom.map_add z z').trans
        ((congrArg₂ (· + ·) hz hz').trans ((e.hom.app (M ⊗ X)).hom.map_add z z').symm)
  | tmul r y =>
      induction y using TensorProduct.inductionOn with
      | add y y' hy hy' =>
          rw [TensorProduct.tmul_add]
          exact (lhs.hom.map_add _ _).trans
            ((congrArg₂ (· + ·) hy hy').trans ((e.hom.app (M ⊗ X)).hom.map_add _ _).symm)
      | tmul m x =>
          change R₀ at r
          change (((tensoringLeft (ModuleCat.{u₀} R₀)).map (e.hom.app M)).app X)
            ((((tensoringLeft (ModuleCat.{u₀} R₀)).obj (F.obj M)).map (e.hom.app X))
              ((scalarExtensionTensorIso R₀ R₀ (RingHom.id R₀) M X).hom
                (r ⊗ₜ[R₀, RingHom.id R₀] (m ⊗ₜ[R₀] x)))) = _
          erw [scalarExtensionTensorIso_hom_tmul]
          change (e.hom.app M (r ⊗ₜ[R₀, RingHom.id R₀] m)) ⊗ₜ[R₀]
              (e.hom.app X ((1 : R₀) ⊗ₜ[R₀, RingHom.id R₀] x)) =
            e.hom.app (M ⊗ X) (r ⊗ₜ[R₀, RingHom.id R₀] (m ⊗ₜ[R₀] x))
          have hvalues := congrArg₂ (fun a b => a ⊗ₜ[R₀] b) (hid M m r) (hid X x 1)
          have hscalar : (r • m) ⊗ₜ[R₀] ((1 : R₀) • x) = r • (m ⊗ₜ[R₀] x) := by
            rw [one_smul, TensorProduct.smul_tmul']
          exact hvalues.trans (hscalar.trans (hid (M ⊗ X) (m ⊗ₜ[R₀] x) r).symm)

/-- The actual identity scalar comparison lifts the original resolution augmentation. -/
theorem flatScalarExtensionProjectiveResolution_id_augmentation
    {X : ModuleCat.{u₀} R₀} (P : ProjectiveResolution X) :
    letI : Algebra R₀ R₀ := (RingHom.id R₀).toAlgebra
    letI : Module.Flat R₀ R₀ := RingHom.flat_algebraMap_iff.mp (RingHom.Flat.id R₀)
    let Q := flatScalarExtensionProjectiveResolution.{u₀, u₀, 0} R₀ R₀ P
    let θ := (NatIso.mapHomologicalComplex (extendScalarsId R₀) (ComplexShape.down ℕ)).hom.app P.complex
    θ.f 0 ≫ P.π.f 0 = Q.π.f 0 ≫ (extendScalarsId R₀).hom.app X := by
  let : Algebra R₀ R₀ := (RingHom.id R₀).toAlgebra
  let : Module.Flat R₀ R₀ := RingHom.flat_algebraMap_iff.mp (RingHom.Flat.id R₀)
  let F := extendScalars (RingHom.id R₀)
  let e := extendScalarsId R₀
  let Q := flatScalarExtensionProjectiveResolution.{u₀, u₀, 0} R₀ R₀ P
  let p₀ : P.complex.X 0 ⟶ X := P.π.f 0
  have hnat : e.hom.app (P.complex.X 0) ≫ p₀ = F.map p₀ ≫ e.hom.app X :=
    (e.hom.naturality p₀).symm
  let A : F.obj X ⟶ F.obj X :=
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).hom.app X).f 0
  have hF : A = 𝟙 (F.obj X) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  change e.hom.app (P.complex.X 0) ≫ p₀ =
    (F.map p₀ ≫ A) ≫ e.hom.app X
  have h := congrArg (fun k : F.obj X ⟶ F.obj X => (F.map p₀ ≫ k) ≫ e.hom.app X) hF
  exact hnat.trans (h.trans (congrArg (fun k => k ≫ e.hom.app X) (Category.comp_id (F.map p₀)))).symm

/-- Flat native Tor base change along the identity is the actual identity scalar comparison. -/
theorem flatScalarExtensionTorBaseChangeIso_hom_id (M X : ModuleCat.{u₀} R₀) (q : ℕ) :
    letI : MonoidalCategoryStruct (ModuleCat.{u₀} R₀) := tensorStructure.{u₀, 0}
    letI : MonoidalCategory (ModuleCat.{u₀} R₀) := monoidalCategory.{u₀, 0}
    letI : MonoidalPreadditive (ModuleCat.{u₀} R₀) := monoidalPreadditive.{u₀, 0}
    letI : Algebra R₀ R₀ := (RingHom.id R₀).toAlgebra
    letI : Module.Flat R₀ R₀ := RingHom.flat_algebraMap_iff.mp (RingHom.Flat.id R₀)
    let F := extendScalars (RingHom.id R₀)
    (flatScalarExtensionTorBaseChangeIso R₀ R₀ M X q).hom ≫
      ((Tor (ModuleCat.{u₀} R₀) q).obj (F.obj M)).map ((extendScalarsId R₀).hom.app X) ≫
        ((Tor (ModuleCat.{u₀} R₀) q).map ((extendScalarsId R₀).hom.app M)).app X =
      (extendScalarsId R₀).hom.app (((Tor (ModuleCat.{u₀} R₀) q).obj M).obj X) := by
  let : MonoidalCategoryStruct (ModuleCat.{u₀} R₀) := tensorStructure.{u₀, 0}
  let : MonoidalCategory (ModuleCat.{u₀} R₀) := monoidalCategory.{u₀, 0}
  let : MonoidalPreadditive (ModuleCat.{u₀} R₀) := monoidalPreadditive.{u₀, 0}
  let : Algebra R₀ R₀ := (RingHom.id R₀).toAlgebra
  let : Module.Flat R₀ R₀ := RingHom.flat_algebraMap_iff.mp (RingHom.Flat.id R₀)
  let F := extendScalars (RingHom.id R₀)
  let : F.PreservesHomology := preservesHomology_extendScalars_of_flat (RingHom.id R₀) (RingHom.Flat.id R₀)
  let e := extendScalarsId R₀
  let P := projectiveResolution X
  let Q := flatScalarExtensionProjectiveResolution R₀ R₀ P
  let L := (tensoringLeft (ModuleCat.{u₀} R₀)).obj M
  let L' := (tensoringLeft (ModuleCat.{u₀} R₀)).obj (F.obj M)
  let K := (L.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let J := (L'.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  let Z := HomologicalComplex.homologyFunctor (ModuleCat.{u₀} R₀) (ComplexShape.down ℕ) q
  let T := ((Tor (ModuleCat.{u₀} R₀) q).obj M).obj X
  let T' := ((Tor (ModuleCat.{u₀} R₀) q).obj (F.obj M)).obj (F.obj X)
  let β : F.obj T ≅ T' := flatScalarExtensionTorBaseChangeIso R₀ R₀ M X q
  let eP : T ≅ Z.obj K := P.isoLeftDerivedObj L q
  let eQ : T' ≅ Z.obj J := Q.isoLeftDerivedObj L' q
  let aR : T ⟶ Z.obj K := eP.hom
  let b : F.obj (Z.obj K) ⟶ Z.obj ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) :=
    (HomologicalComplex.mapHomologyFunctorIso q F).inv.app K
  let c : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ≅ J :=
    (NatIso.mapHomologicalComplex (scalarExtensionTensorNatIso R₀ R₀ (RingHom.id R₀) M)
      (ComplexShape.down ℕ)).app P.complex
  let θ := (NatIso.mapHomologicalComplex e (ComplexShape.down ℕ)).hom.app P.complex
  let θK := (NatIso.mapHomologicalComplex e (ComplexShape.down ℕ)).hom.app K
  let κ : J ⟶ K := (L'.mapHomologicalComplex (ComplexShape.down ℕ)).map θ ≫
    (NatTrans.mapHomologicalComplex ((tensoringLeft (ModuleCat.{u₀} R₀)).map (e.hom.app M))
      (ComplexShape.down ℕ)).app P.complex
  let τ : T' ⟶ T := ((Tor (ModuleCat.{u₀} R₀) q).obj (F.obj M)).map (e.hom.app X) ≫
    ((Tor (ModuleCat.{u₀} R₀) q).map (e.hom.app M)).app X
  have hθ : θ.f 0 ≫ P.π.f 0 = Q.π.f 0 ≫ e.hom.app X :=
    flatScalarExtensionProjectiveResolution_id_augmentation R₀ P
  let Φ : ProjectiveResolution.Hom Q P (e.hom.app X) :=
    { hom := θ, hom_f_zero_comp_π_f_zero := by
        rw [ChainComplex.single₀_map_f_zero]
        exact hθ }
  have hTor : τ = eQ.hom ≫ Z.map κ ≫ eP.inv := by
    exact Functor.LeftDerivedBalance.deriveSecond_map_computation
      (tensoringLeft (ModuleCat.{u₀} R₀)) q (e.hom.app M) (e.hom.app X) Q P θ Φ.hom_comp_π
  have hChain : c.hom ≫ κ = θK := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact scalarExtensionTensorIso_hom_id R₀ M (P.complex.X n)
  have hChainH : Z.map c.hom ≫ Z.map κ = Z.map θK :=
    (Z.map_comp c.hom κ).symm.trans (congrArg (fun k => Z.map k) hChain)
  let bId : Z.obj K ⟶ Z.obj K :=
    (HomologicalComplex.mapHomologyFunctorIso q (𝟭 (ModuleCat.{u₀} R₀))).inv.app K
  have hId : bId = 𝟙 (Z.obj K) := by
    let i := (K.sc q).mapHomologyIso (𝟭 (ModuleCat.{u₀} R₀))
    have hi : i.inv ≫ i.inv = i.inv :=
      (ShortComplex.mapHomologyIso_comp_inv (K.sc q) (𝟭 (ModuleCat.{u₀} R₀)) (𝟭 (ModuleCat.{u₀} R₀))).symm
    exact (cancel_mono i.inv).mp (hi.trans (Category.id_comp i.inv).symm)
  have hNat : b ≫ Z.map θK = e.hom.app (Z.obj K) := by
    have h : e.hom.app (Z.obj K) ≫ bId = b ≫ Z.map θK :=
      NatTrans.app_homology_comp_mapHomologyIso_inv e.hom (K.sc q)
    exact h.symm.trans ((congrArg (fun k : Z.obj K ⟶ Z.obj K => e.hom.app (Z.obj K) ≫ k) hId).trans
      (Category.comp_id _))
  have hβ : β.hom = F.map aR ≫ b ≫ Z.map c.hom ≫ eQ.inv :=
    flatScalarExtensionTorBaseChangeIso_hom_computation R₀ R₀ M X q
  have hPrefix : F.map aR ≫ e.hom.app (Z.obj K) = e.hom.app T ≫ aR := e.hom.naturality aR
  have hStep : β.hom ≫ τ = F.map aR ≫ b ≫ Z.map c.hom ≫ Z.map κ ≫ eP.inv := by
    have h := congrArg₂ (fun x y => x ≫ y) hβ hTor
    apply h.trans
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change β.hom ≫ τ = e.hom.app T
  calc
    _ = F.map aR ≫ b ≫ Z.map c.hom ≫ Z.map κ ≫ eP.inv := hStep
    _ = F.map aR ≫ b ≫ (Z.map c.hom ≫ Z.map κ) ≫ eP.inv := by simp only [Category.assoc]
    _ = F.map aR ≫ (b ≫ Z.map θK) ≫ eP.inv := by
      exact (congrArg (fun k => F.map aR ≫ b ≫ k ≫ eP.inv) hChainH).trans
        (by simp only [Category.assoc])
    _ = (e.hom.app T ≫ aR) ≫ eP.inv := by
      exact (congrArg (fun k => F.map aR ≫ k ≫ eP.inv) hNat).trans
        (congrArg (fun k => k ≫ eP.inv) hPrefix)
    _ = _ := by simp only [aR, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end ScalarIdentity

end ModuleCat.UniverseTensor
