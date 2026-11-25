/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.FlatScalarExtensionTorCancellationUniverse
public import MathlibExt.Algebra.Category.ModuleCat.FlatScalarExtensionTorNaturality
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Resolved-variable naturality of the original native Tor comparison

The actual original resolution lift remains compatible with augmentation
after the genuine flat scalar extension. This derived square supplies the
original native Tor computation maps. No augmentation square, naturality
equation, new resolution, comparison isomorphism or derived functor is assumed.
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

/-- The actual scalar extension of the original resolution lift has its
genuine augmentation square in the extended-ring complex category. -/
theorem flatScalarExtensionProjectiveResolution_map_lift_comp_π
    {X Y : ModuleCat.{max u v w} R} (h : X ⟶ Y)
    (PX : ProjectiveResolution X) (PY : ProjectiveResolution Y) :
    let F : ModuleCat.{max u v w} R ⥤ ModuleCat.{max u v w} S :=
      extendScalars.{u,v,max u v w} (algebraMap R S)
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (ProjectiveResolution.lift h PX PY)) ≫
        (flatScalarExtensionProjectiveResolution.{u,v,w} R S PY).π =
      (flatScalarExtensionProjectiveResolution.{u,v,w} R S PX).π ≫
        (ChainComplex.single₀ (ModuleCat.{max u v w} S)).map (F.map h) := by
  let F : ModuleCat.{max u v w} R ⥤ ModuleCat.{max u v w} S :=
    extendScalars.{u,v,max u v w} (algebraMap R S)
  let : F.PreservesHomology := ModuleCat.preservesHomology_extendScalars_of_flat.{u,v,w}
    (algebraMap R S) (by rw [RingHom.flat_algebraMap_iff]; infer_instance)
  let D := F.mapHomologicalComplex (ComplexShape.down ℕ)
  let φ := ProjectiveResolution.lift h PX PY
  let aX := (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).hom.app X
  let aY := (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).hom.app Y
  have hn : D.map ((ChainComplex.single₀ (ModuleCat.{max u v w} R)).map h) ≫ aY =
      aX ≫ (ChainComplex.single₀ (ModuleCat.{max u v w} S)).map (F.map h) := by
    exact (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).hom.naturality h
  change D.map φ ≫ (D.map PY.π ≫ aY) =
    (D.map PX.π ≫ aX) ≫ (ChainComplex.single₀ (ModuleCat.{max u v w} S)).map (F.map h)
  calc
    _ = D.map (φ ≫ PY.π) ≫ aY := by
      rw [D.map_comp]
      exact (Category.assoc _ _ _).symm
    _ = D.map (PX.π ≫ (ChainComplex.single₀ (ModuleCat.{max u v w} R)).map h) ≫ aY := by
      rw [ProjectiveResolution.lift_commutes]
    _ = D.map PX.π ≫ D.map ((ChainComplex.single₀ (ModuleCat.{max u v w} R)).map h) ≫ aY := by
      rw [D.map_comp, Category.assoc]
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun k => D.map PX.π ≫ k) hn

/-- The existing original flat native Tor cancellation preserves every
actual map in its resolved module variable, in every degree and universe. -/
theorem flatScalarExtensionTorCancellationIso_hom_naturality_resolved
    {X Y : ModuleCat.{max u v w} R} (h : X ⟶ Y)
    (N : ModuleCat.{max u v w} S) (q : ℕ) :
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
        (((Tor (ModuleCat.{max u v w} S) q).obj N).map
          ((extendScalars.{u,v,max u v w} (algebraMap R S)).map h)) ≫
        (flatScalarExtensionTorCancellationIso.{u,v,w} R S N Y q).hom =
      (flatScalarExtensionTorCancellationIso.{u,v,w} R S N X q).hom ≫
        (((Tor (ModuleCat.{max u v w} R) q).obj
          ((restrictScalars.{max u v w,u,v} (algebraMap R S)).obj N)).map h) := by
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
  let PX := projectiveResolution X
  let PY := projectiveResolution Y
  let QX := flatScalarExtensionProjectiveResolution.{u,v,w} R S PX
  let QY := flatScalarExtensionProjectiveResolution.{u,v,w} R S PY
  let φ : PX.complex ⟶ PY.complex := ProjectiveResolution.lift h PX PY
  let θ : QX.complex ⟶ QY.complex := (F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ
  have hθ : θ.f 0 ≫ QY.π.f 0 = QX.π.f 0 ≫ F.map h := by
    have hw : θ ≫ QY.π = QX.π ≫ (ChainComplex.single₀ (ModuleCat.{max u v w} S)).map (F.map h) :=
      flatScalarExtensionProjectiveResolution_map_lift_comp_π.{u,v,w} R S h PX PY
    have hzero := congrArg
      (fun k : QX.complex ⟶ (ChainComplex.single₀ (ModuleCat.{max u v w} S)).obj (F.obj Y) => k.f 0) hw
    simp only [HomologicalComplex.comp_f, ChainComplex.single₀_map_f_zero] at hzero
    exact hzero
  let L' := (tensoringLeft (ModuleCat.{max u v w} S)).obj N
  let L := (tensoringLeft (ModuleCat.{max u v w} R)).obj (H.obj N)
  let KX := (L'.mapHomologicalComplex (ComplexShape.down ℕ)).obj QX.complex
  let KY := (L'.mapHomologicalComplex (ComplexShape.down ℕ)).obj QY.complex
  let JX := (L.mapHomologicalComplex (ComplexShape.down ℕ)).obj PX.complex
  let JY := (L.mapHomologicalComplex (ComplexShape.down ℕ)).obj PY.complex
  let HKX := (H.mapHomologicalComplex (ComplexShape.down ℕ)).obj KX
  let HKY := (H.mapHomologicalComplex (ComplexShape.down ℕ)).obj KY
  let κ : KX ⟶ KY := (L'.mapHomologicalComplex (ComplexShape.down ℕ)).map θ
  let ψ : JX ⟶ JY := (L.mapHomologicalComplex (ComplexShape.down ℕ)).map φ
  let EX : HKX ≅ JX := (NatIso.mapHomologicalComplex
    (scalarTensorCancellationNatIso.{u,v,w} R S (algebraMap R S) N)
      (ComplexShape.down ℕ)).app PX.complex
  let EY : HKY ≅ JY := (NatIso.mapHomologicalComplex
    (scalarTensorCancellationNatIso.{u,v,w} R S (algebraMap R S) N)
      (ComplexShape.down ℕ)).app PY.complex
  let tS : (L'.leftDerived q).obj (F.obj X) ⟶ (L'.leftDerived q).obj (F.obj Y) :=
    ((Tor (ModuleCat.{max u v w} S) q).obj N).map (F.map h)
  let tR : (L.leftDerived q).obj X ⟶ (L.leftDerived q).obj Y :=
    ((Tor (ModuleCat.{max u v w} R) q).obj (H.obj N)).map h
  let aX : (L'.leftDerived q).obj (F.obj X) ⟶ KX.homology q := (QX.isoLeftDerivedObj L' q).hom
  let aY : (L'.leftDerived q).obj (F.obj Y) ⟶ KY.homology q := (QY.isoLeftDerivedObj L' q).hom
  let bX : H.obj (KX.homology q) ⟶ HKX.homology q := ((KX.sc q).mapHomologyIso H).inv
  let bY : H.obj (KY.homology q) ⟶ HKY.homology q := ((KY.sc q).mapHomologyIso H).inv
  let cX : HKX.homology q ⟶ JX.homology q := HomologicalComplex.homologyMap EX.hom q
  let cY : HKY.homology q ⟶ JY.homology q := HomologicalComplex.homologyMap EY.hom q
  let dX : JX.homology q ⟶ (L.leftDerived q).obj X := (PX.isoLeftDerivedObj L q).inv
  let dY : JY.homology q ⟶ (L.leftDerived q).obj Y := (PY.isoLeftDerivedObj L q).inv
  have hQ : tS ≫ aY = aX ≫ HomologicalComplex.homologyMap κ q := by
    exact ProjectiveResolution.isoLeftDerivedObj_hom_naturality (F.map h) QX QY θ hθ L' q
  have hQH : H.map tS ≫ H.map aY = H.map aX ≫ H.map (HomologicalComplex.homologyMap κ q) := by
    have hmap := congrArg (fun k => H.map k) hQ
    rw [H.map_comp, H.map_comp] at hmap
    exact hmap
  have hH : H.map (HomologicalComplex.homologyMap κ q) ≫ bY =
      bX ≫ HomologicalComplex.homologyMap
        ((H.mapHomologicalComplex (ComplexShape.down ℕ)).map κ) q := by
    exact ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{max u v w} S)
        (ComplexShape.down ℕ) q).map κ) H
  have hC : (H.mapHomologicalComplex (ComplexShape.down ℕ)).map κ ≫ EY.hom = EX.hom ≫ ψ := by
    exact (NatIso.mapHomologicalComplex
      (scalarTensorCancellationNatIso.{u,v,w} R S (algebraMap R S) N)
        (ComplexShape.down ℕ)).hom.naturality φ
  have hCH :
      HomologicalComplex.homologyMap ((H.mapHomologicalComplex (ComplexShape.down ℕ)).map κ) q ≫ cY =
      cX ≫ HomologicalComplex.homologyMap ψ q := by
    let U := HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} R) (ComplexShape.down ℕ) q
    have hmap := congrArg (fun k => U.map k) hC
    rw [U.map_comp, U.map_comp] at hmap
    exact hmap
  have hP : HomologicalComplex.homologyMap ψ q ≫ dY = dX ≫ tR := by
    exact (ProjectiveResolution.isoLeftDerivedObj_inv_naturality h PX PY φ
      (ProjectiveResolution.lift_commutes_zero h PX PY) L q).symm
  change H.map tS ≫ (H.map aY ≫ bY ≫ cY ≫ dY) = (H.map aX ≫ bX ≫ cX ≫ dX) ≫ tR
  calc
    _ = H.map aX ≫ H.map (HomologicalComplex.homologyMap κ q) ≫ bY ≫ cY ≫ dY := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ bY ≫ cY ≫ dY) hQH
    _ = H.map aX ≫ bX ≫
        HomologicalComplex.homologyMap ((H.mapHomologicalComplex (ComplexShape.down ℕ)).map κ) q ≫
        cY ≫ dY := by
      simpa only [Category.assoc] using congrArg (fun k => H.map aX ≫ k ≫ cY ≫ dY) hH
    _ = H.map aX ≫ bX ≫ cX ≫ HomologicalComplex.homologyMap ψ q ≫ dY := by
      simpa only [Category.assoc] using congrArg (fun k => H.map aX ≫ bX ≫ k ≫ dY) hCH
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun k => H.map aX ≫ bX ≫ cX ≫ k) hP

/-- The actual inverse original Tor cancellation preserves the same
resolved-variable map in every original degree. -/
theorem flatScalarExtensionTorCancellationIso_inv_naturality_resolved
    {X Y : ModuleCat.{max u v w} R} (h : X ⟶ Y)
    (N : ModuleCat.{max u v w} S) (q : ℕ) :
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
    (((Tor (ModuleCat.{max u v w} R) q).obj
        ((restrictScalars.{max u v w,u,v} (algebraMap R S)).obj N)).map h) ≫
        (flatScalarExtensionTorCancellationIso.{u,v,w} R S N Y q).inv =
      (flatScalarExtensionTorCancellationIso.{u,v,w} R S N X q).inv ≫
        (restrictScalars.{max u v w,u,v} (algebraMap R S)).map
          (((Tor (ModuleCat.{max u v w} S) q).obj N).map
            ((extendScalars.{u,v,max u v w} (algebraMap R S)).map h)) := by
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
  rw [← cancel_mono (flatScalarExtensionTorCancellationIso.{u,v,w} R S N Y q).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [flatScalarExtensionTorCancellationIso_hom_naturality_resolved.{u,v,w} R S h N q,
    Iso.inv_hom_id_assoc]

end ModuleCat.UniverseTensor
