/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CellFamilyAttachment
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CWComplex
public import MathlibExt.Topology.CWComplex.SubcomplexModelCofibration
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantCube
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationQuillenEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.RealizedMonoCofibration
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.AlgebraicTopology.ModelCategory.Instances
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.ContinuousWhitehead

/-!
# A simplicial model of an actual classical cell family

The attaching and characteristic maps are the adjoints of the original
classical maps through the same matched disk-boundary arrow isomorphism.
The literal simplicial pushout maps to the original singular cell-family space.
For a cofibrant source, its realization comparison is a weak
homotopy equivalence by the cofibrant pushout comparison theorem.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open AlgebraicTopology Topology Topology.CWComplex
open scoped Simplicial SSet.modelCategoryQuillen TopCat.modelCategory

universe u

open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen TopCat.modelCategory

namespace OriginalCellFamilyModelConstruction

private abbrev actualMap (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :=
  TopCat.toSSet.map (CellFamilyAttachment.inclusion X n att)

private theorem realizedAdjunct_counit {K : SSet.{u}} {Y : TopCat.{u}}
    (a : SSet.toTop.obj K ⟶ Y) :
    SSet.toTop.map (sSetTopAdj.homEquiv K Y a) ≫ sSetTopAdj.counit.app Y = a := by
  have h := (sSetTopAdj.homEquiv K Y).symm_apply_apply a
  rw [Adjunction.homEquiv_counit] at h
  exact h

private def originalDiskAdjunct
    (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) (p : I) :
    (Δ[n + 1] : SSet.{u}) ⟶ TopCat.toSSet.obj (CellFamilyAttachment.space X n att) :=
  sSetTopAdj.homEquiv _ _
    ((SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.right ≫ CellFamilyAttachment.cell X n
      att p)

private def originalBoundaryAdjunct
    (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) (p : I) :
    (SSet.boundary.{u} (n + 1)).toSSet ⟶ TopCat.toSSet.obj X :=
  sSetTopAdj.homEquiv _ _
    ((SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.left ≫ att p)

private theorem originalAdjunct_square
    (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) (p : I) :
    originalBoundaryAdjunct X n I att p ≫ actualMap X n I att =
      (SSet.boundary.{u} (n + 1)).ι ≫ originalDiskAdjunct X n I att p := by
  have h : SSet.toTop.map (SSet.boundary.{u} (n + 1)).ι ≫
      ((SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.right ≫ CellFamilyAttachment.cell X n
        att p) =
    ((SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.left ≫ att p) ≫
      CellFamilyAttachment.inclusion X n att := by
    calc
      SSet.toTop.map (SSet.boundary.{u} (n + 1)).ι ≫
          ((SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.right ≫ CellFamilyAttachment.cell
            X n att p) =
        (SSet.toTop.map (SSet.boundary.{u} (n + 1)).ι ≫ (SSet.boundary.toClassicalCellDiskArrowIso
          (n + 1)).hom.right) ≫
          CellFamilyAttachment.cell X n att p := (Category.assoc _ _ _).symm
      _ = ((SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.left ≫ (classicalCellDiskPair.{u}
        (n + 1)).map) ≫
          CellFamilyAttachment.cell X n att p := by
            exact congrArg (fun t => t ≫ CellFamilyAttachment.cell X n att p) (Arrow.w
              (SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom).symm
      _ = (SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.left ≫
          ((classicalCellDiskPair.{u} (n + 1)).map ≫ CellFamilyAttachment.cell X n att p) :=
        Category.assoc _ _ _
      _ = (SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.left ≫
          (att p ≫ CellFamilyAttachment.inclusion X n att) :=
        congrArg (fun t => (SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.left ≫ t)
          (CellFamilyAttachment.boundary_gluing X n att p).symm
      _ = ((SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.left ≫ att p) ≫
          CellFamilyAttachment.inclusion X n att := (Category.assoc _ _ _).symm
  exact (sSetTopAdj.homEquiv_naturality_left_square (SSet.boundary.{u} (n + 1)).ι
    ((SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.right ≫ CellFamilyAttachment.cell X n
      att p)
    ((SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.left ≫ att p)
    (CellFamilyAttachment.inclusion X n att) h).symm


private abbrev originalCellModelBoundaries
    (n : ℕ) (I : Type u) : SSet.{u} :=
  ∐ fun _ : I => (SSet.boundary.{u} (n + 1)).toSSet

private abbrev originalCellModelDisks
    (n : ℕ) (I : Type u) : SSet.{u} :=
  ∐ fun _ : I => (Δ[n + 1] : SSet.{u})

private def originalCellModelBoundarySum
    (n : ℕ) (I : Type u) :
    originalCellModelBoundaries n I ⟶ originalCellModelDisks n I :=
  CategoryTheory.Limits.Sigma.map (fun _ : I => (SSet.boundary.{u} (n + 1)).ι)

private def originalCellModelAttaching
    (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    originalCellModelBoundaries n I ⟶ TopCat.toSSet.obj X :=
  CategoryTheory.Limits.Sigma.desc (fun p : I => originalBoundaryAdjunct X n I att p)

private def originalCellModelDiskMates
    (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    originalCellModelDisks n I ⟶ TopCat.toSSet.obj (CellFamilyAttachment.space X n att) :=
  CategoryTheory.Limits.Sigma.desc (fun p : I => originalDiskAdjunct X n I att p)

private theorem originalCellModelAdjunctSquare
    (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    originalCellModelBoundarySum n I ≫ originalCellModelDiskMates X n I att =
      originalCellModelAttaching X n I att ≫ actualMap X n I att := by
  apply CategoryTheory.Limits.Sigma.hom_ext
  intro p
  let b : (SSet.boundary.{u} (n + 1)).toSSet ⟶ originalCellModelBoundaries n I :=
    CategoryTheory.Limits.Sigma.ι (fun _ : I => (SSet.boundary.{u} (n + 1)).toSSet) p
  let d : (Δ[n + 1] : SSet.{u}) ⟶ originalCellModelDisks n I :=
    CategoryTheory.Limits.Sigma.ι (fun _ : I => (Δ[n + 1] : SSet.{u})) p
  have hBoundary : b ≫ originalCellModelBoundarySum n I = (SSet.boundary.{u} (n + 1)).ι ≫ d :=
    CategoryTheory.Limits.Sigma.ι_map (fun _ : I => (SSet.boundary.{u} (n + 1)).ι) p
  have hDisk : d ≫ originalCellModelDiskMates X n I att = originalDiskAdjunct X n I att p :=
    CategoryTheory.Limits.Sigma.ι_comp_desc (fun q : I => originalDiskAdjunct X n I att q) p
  have hAttach : b ≫ originalCellModelAttaching X n I att = originalBoundaryAdjunct X n I att p :=
    CategoryTheory.Limits.Sigma.ι_comp_desc (fun q : I => originalBoundaryAdjunct X n I att q) p
  calc
    b ≫ (originalCellModelBoundarySum n I ≫ originalCellModelDiskMates X n I att) =
      (b ≫ originalCellModelBoundarySum n I) ≫ originalCellModelDiskMates X n I att :=
        (Category.assoc _ _ _).symm
    _ = ((SSet.boundary.{u} (n + 1)).ι ≫ d) ≫ originalCellModelDiskMates X n I att :=
      congrArg (fun t => t ≫ originalCellModelDiskMates X n I att) hBoundary
    _ = (SSet.boundary.{u} (n + 1)).ι ≫ (d ≫ originalCellModelDiskMates X n I att) :=
      Category.assoc _ _ _
    _ = (SSet.boundary.{u} (n + 1)).ι ≫ originalDiskAdjunct X n I att p :=
      congrArg (fun t => (SSet.boundary.{u} (n + 1)).ι ≫ t) hDisk
    _ = originalBoundaryAdjunct X n I att p ≫ actualMap X n I att :=
      (originalAdjunct_square X n I att p).symm
    _ = (b ≫ originalCellModelAttaching X n I att) ≫ actualMap X n I att :=
      congrArg (fun t => t ≫ actualMap X n I att) hAttach.symm
    _ = b ≫ (originalCellModelAttaching X n I att ≫ actualMap X n I att) :=
      Category.assoc _ _ _

private def originalCellModel
    (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) : SSet.{u} :=
  pushout (originalCellModelBoundarySum n I) (originalCellModelAttaching X n I att)

private def originalCellModelOldInclusion
    (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    TopCat.toSSet.obj X ⟶ originalCellModel X n I att :=
  pushout.inr _ _

private def originalCellModelNewDisks
    (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    originalCellModelDisks n I ⟶ originalCellModel X n I att :=
  pushout.inl _ _

private theorem originalCellModelIsPushout
    (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    IsPushout (originalCellModelBoundarySum n I) (originalCellModelAttaching X n I att)
      (originalCellModelNewDisks X n I att) (originalCellModelOldInclusion X n I att) :=
  IsPushout.of_hasPushout _ _

private def originalCellModelToSingular
    (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    originalCellModel X n I att ⟶ TopCat.toSSet.obj (CellFamilyAttachment.space X n att) :=
  pushout.desc (originalCellModelDiskMates X n I att) (actualMap X n I att)
    (originalCellModelAdjunctSquare X n I att)

private theorem originalCellModelToSingular_old
    (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    originalCellModelOldInclusion X n I att ≫ originalCellModelToSingular X n I att = actualMap X n
      I att :=
  pushout.inr_desc _ _ _

private theorem originalCellModelToSingular_disks
    (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    originalCellModelNewDisks X n I att ≫ originalCellModelToSingular X n I att =
      originalCellModelDiskMates X n I att :=
  pushout.inl_desc _ _ _

private def originalCellModelRealizationMap
    (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    SSet.toTop.obj (originalCellModel X n I att) ⟶ CellFamilyAttachment.space X n att :=
  SSet.toTop.map (originalCellModelToSingular X n I att) ≫
    sSetTopAdj.counit.app (CellFamilyAttachment.space X n att)

private theorem originalCellModelRealizationMap_old
    (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    SSet.toTop.map (originalCellModelOldInclusion X n I att) ≫ originalCellModelRealizationMap X n I
      att =
      sSetTopAdj.counit.app X ≫ CellFamilyAttachment.inclusion X n att := by
  have hOld := originalCellModelToSingular_old X n I att
  have hCounit : SSet.toTop.map (actualMap X n I att) ≫
      sSetTopAdj.counit.app (CellFamilyAttachment.space X n att) =
        sSetTopAdj.counit.app X ≫ CellFamilyAttachment.inclusion X n att :=
    sSetTopAdj.counit.naturality (CellFamilyAttachment.inclusion X n att)
  calc
    SSet.toTop.map (originalCellModelOldInclusion X n I att) ≫ originalCellModelRealizationMap X n I
      att =
      (SSet.toTop.map (originalCellModelOldInclusion X n I att) ≫
        SSet.toTop.map (originalCellModelToSingular X n I att)) ≫
          sSetTopAdj.counit.app (CellFamilyAttachment.space X n att) := (Category.assoc _ _ _).symm
    _ = SSet.toTop.map
        (originalCellModelOldInclusion X n I att ≫ originalCellModelToSingular X n I att) ≫
          sSetTopAdj.counit.app (CellFamilyAttachment.space X n att) :=
      congrArg (fun t => t ≫ sSetTopAdj.counit.app (CellFamilyAttachment.space X n att))
        (SSet.toTop.map_comp _ _).symm
    _ = SSet.toTop.map (actualMap X n I att) ≫ sSetTopAdj.counit.app (CellFamilyAttachment.space X n
      att) :=
      congrArg (fun t => SSet.toTop.map t ≫ sSetTopAdj.counit.app (CellFamilyAttachment.space X n
        att)) hOld
    _ = sSetTopAdj.counit.app X ≫ CellFamilyAttachment.inclusion X n att := hCounit

private theorem originalCellModelRealizationMap_disk
    (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) (p : I) :
    SSet.toTop.map ((CategoryTheory.Limits.Sigma.ι (fun _ : I => (Δ[n + 1] : SSet.{u})) p) ≫
      originalCellModelNewDisks X n I att) ≫ originalCellModelRealizationMap X n I att =
        (SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.right ≫ CellFamilyAttachment.cell X
          n att p
          := by
  let d : (Δ[n + 1] : SSet.{u}) ⟶ originalCellModelDisks n I :=
    CategoryTheory.Limits.Sigma.ι (fun _ : I => (Δ[n + 1] : SSet.{u})) p
  have hNew : (d ≫ originalCellModelNewDisks X n I att) ≫ originalCellModelToSingular X n I att =
      originalDiskAdjunct X n I att p :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun t => d ≫ t) (originalCellModelToSingular_disks X n I att)).trans
        (CategoryTheory.Limits.Sigma.ι_comp_desc (fun q : I => originalDiskAdjunct X n I att q) p))
  have hAdjunct : SSet.toTop.map (originalDiskAdjunct X n I att p) ≫
      sSetTopAdj.counit.app (CellFamilyAttachment.space X n att) =
        (SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.right ≫ CellFamilyAttachment.cell X
          n att p :=
    realizedAdjunct_counit ((SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.right ≫
      CellFamilyAttachment.cell X n att p)
  calc
    SSet.toTop.map (d ≫ originalCellModelNewDisks X n I att) ≫ originalCellModelRealizationMap X n I
      att =
      (SSet.toTop.map (d ≫ originalCellModelNewDisks X n I att) ≫
        SSet.toTop.map (originalCellModelToSingular X n I att)) ≫
          sSetTopAdj.counit.app (CellFamilyAttachment.space X n att) :=
      (Category.assoc _ _ _).symm
    _ = SSet.toTop.map ((d ≫ originalCellModelNewDisks X n I att) ≫
          originalCellModelToSingular X n I att) ≫
        sSetTopAdj.counit.app (CellFamilyAttachment.space X n att) :=
      congrArg (fun t => t ≫ sSetTopAdj.counit.app (CellFamilyAttachment.space X n att))
        (SSet.toTop.map_comp _ _).symm
    _ = SSet.toTop.map (originalDiskAdjunct X n I att p) ≫
          sSetTopAdj.counit.app (CellFamilyAttachment.space X n att) :=
      congrArg (fun t => SSet.toTop.map t ≫ sSetTopAdj.counit.app (CellFamilyAttachment.space X n
        att)) hNew
    _ = (SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.right ≫ CellFamilyAttachment.cell X
      n att p := hAdjunct

private theorem originalCellModelBoundarySum_cofibration
    (n : ℕ) (I : Type u) :
    Cofibration (originalCellModelBoundarySum n I) := by
  have hCell : Cofibration (SSet.boundary.{u} (n + 1)).ι := by
    apply (cofibration_iff _).mpr
    change Mono (SSet.boundary.{u} (n + 1)).ι
    infer_instance
  let : ∀ p : I, Cofibration (SSet.boundary.{u} (n + 1)).ι := fun _ => hCell
  exact (inferInstance : Cofibration (CategoryTheory.Limits.Sigma.map (fun _ : I =>
    (SSet.boundary.{u} (n + 1)).ι)))

private theorem originalCellModelOldInclusion_cofibration
    (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    Cofibration (originalCellModelOldInclusion X n I att) := by
  apply (cofibration_iff _).mpr
  exact (cofibrations SSet.{u}).of_isPushout (originalCellModelIsPushout X n I att).flip
    ((cofibration_iff _).mp (originalCellModelBoundarySum_cofibration n I))

private theorem originalClassicalCW_isCofibrant
    (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)] :
    IsCofibrant X := by
  let A : Topology.CWComplex.Subcomplex (Set.univ : Set X) :=
    Topology.CWComplex.skeletonLT (Set.univ : Set X) (0 : ℕ∞)
  let S : TopCat.{u} := TopCat.of (A : Set X)
  let : IsEmpty S := ⟨fun z => by
    have hz : z.val ∈ (A : Set X) := z.property
    have hEmpty : (A : Set X) = ∅ :=
      Topology.CWComplex.skeletonLT_zero_eq_empty
    have hFalse : z.val ∈ (∅ : Set X) :=
      Eq.mp (congrArg (fun E : Set X => z.val ∈ E) hEmpty) hz
    exact hFalse⟩
  have hS : IsInitial S := IsInitial.ofUniqueHom
    (fun Z => TopCat.ofHom ⟨isEmptyElim, by
      rw [continuous_iff_continuousAt]
      intro z
      exact isEmptyElim z⟩)
    (fun Z f => by
      apply TopCat.ext
      intro z
      exact isEmptyElim z)
  let j : S ⟶ X := Topology.CWComplex.subcomplexInclusion A
  have hj : Cofibration j := by
    apply (cofibration_iff _).mpr
    change TopCat.realizedBoundaryInclusions.rlp.llp j
    exact Topology.CWComplex.subcomplexInclusion_mem_realizedBoundaryLLP X A
  exact (isCofibrant_iff_of_isInitial j hS).mpr hj

private def originalRealizedFamilyIso (I : Type u) (A : SSet.{u}) (B : TopCat.{u})
    (e : SSet.toTop.obj A ≅ B) :
    SSet.toTop.obj (∐ fun _ : I => A) ≅ TopCat.of (Σ _ : I, B) := by
  letI : SSet.toTop.{u}.IsLeftAdjoint := sSetTopAdj.isLeftAdjoint
  let e₁ := PreservesCoproduct.iso SSet.toTop (fun _ : I => A)
  let e₂ := CategoryTheory.Limits.Sigma.mapIso (fun _ : I => e)
  let e₃ : (∐ fun _ : I => B) ≅ TopCat.of (Σ _ : I, B) :=
    (coproductIsCoproduct (fun _ : I => B)).coconePointUniqueUpToIso
      (TopCat.sigmaCofanIsColimit.{u, u} (fun _ : I => B))
  exact e₁ ≪≫ e₂ ≪≫ e₃

private theorem originalRealizedFamilyIso_iota (I : Type u) (A : SSet.{u}) (B : TopCat.{u})
    (e : SSet.toTop.obj A ≅ B) (i : I) :
    SSet.toTop.map (CategoryTheory.Limits.Sigma.ι (fun _ : I => A) i) ≫ (originalRealizedFamilyIso I
      A B e).hom =
      e.hom ≫ TopCat.sigmaι (fun _ : I => B) i := by
  let : SSet.toTop.{u}.IsLeftAdjoint := sSetTopAdj.isLeftAdjoint
  let e₁ := PreservesCoproduct.iso SSet.toTop (fun _ : I => A)
  let e₂ := CategoryTheory.Limits.Sigma.mapIso (fun _ : I => e)
  let e₃ : (∐ fun _ : I => B) ≅ TopCat.of (Σ _ : I, B) :=
    (coproductIsCoproduct (fun _ : I => B)).coconePointUniqueUpToIso
      (TopCat.sigmaCofanIsColimit.{u, u} (fun _ : I => B))
  have h₁ : SSet.toTop.map (CategoryTheory.Limits.Sigma.ι (fun _ : I => A) i) ≫ e₁.hom =
      CategoryTheory.Limits.Sigma.ι (fun _ : I => SSet.toTop.obj A) i :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (isColimitOfHasCoproductOfPreservesColimit SSet.toTop (fun _ : I => A))
      (colimit.isColimit (Discrete.functor (fun _ : I => SSet.toTop.obj A))) ⟨i⟩
  have h₂ : CategoryTheory.Limits.Sigma.ι (fun _ : I => SSet.toTop.obj A) i ≫ e₂.hom =
      e.hom ≫ CategoryTheory.Limits.Sigma.ι (fun _ : I => B) i :=
    CategoryTheory.Limits.Sigma.ι_mapIso_hom (fun _ : I => e) i
  have h₃ : CategoryTheory.Limits.Sigma.ι (fun _ : I => B) i ≫ e₃.hom =
      TopCat.sigmaι (fun _ : I => B) i :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (coproductIsCoproduct (fun _ : I => B))
      (TopCat.sigmaCofanIsColimit.{u, u} (fun _ : I => B)) ⟨i⟩
  calc
    SSet.toTop.map (CategoryTheory.Limits.Sigma.ι (fun _ : I => A) i) ≫ (originalRealizedFamilyIso I
      A B e).hom =
      (SSet.toTop.map (CategoryTheory.Limits.Sigma.ι (fun _ : I => A) i) ≫ e₁.hom) ≫ (e₂.hom ≫
        e₃.hom) :=
      (Category.assoc _ _ _).symm
    _ = CategoryTheory.Limits.Sigma.ι (fun _ : I => SSet.toTop.obj A) i ≫ (e₂.hom ≫ e₃.hom) :=
      congrArg (fun t => t ≫ (e₂.hom ≫ e₃.hom)) h₁
    _ = (CategoryTheory.Limits.Sigma.ι (fun _ : I => SSet.toTop.obj A) i ≫ e₂.hom) ≫ e₃.hom :=
      (Category.assoc _ _ _).symm
    _ = (e.hom ≫ CategoryTheory.Limits.Sigma.ι (fun _ : I => B) i) ≫ e₃.hom :=
      congrArg (fun t => t ≫ e₃.hom) h₂
    _ = e.hom ≫ (CategoryTheory.Limits.Sigma.ι (fun _ : I => B) i ≫ e₃.hom) := Category.assoc _ _ _
    _ = e.hom ≫ TopCat.sigmaι (fun _ : I => B) i := congrArg (fun t => e.hom ≫ t) h₃

private def originalCellModelBoundaryIso
    (n : ℕ) (I : Type u) :
    SSet.toTop.obj (originalCellModelBoundaries n I) ≅ CellFamilyAttachment.boundaries I n :=
  originalRealizedFamilyIso I (SSet.boundary.{u} (n + 1)).toSSet
    (classicalCellDiskPair.{u} (n + 1)).snd (Arrow.leftFunc.mapIso
      (SSet.boundary.toClassicalCellDiskArrowIso (n + 1)))

private def originalCellModelDisksIso
    (n : ℕ) (I : Type u) :
    SSet.toTop.obj (originalCellModelDisks n I) ≅ CellFamilyAttachment.disks I n :=
  originalRealizedFamilyIso I (Δ[n + 1] : SSet.{u})
    (classicalCellDiskPair.{u} (n + 1)).fst (Arrow.rightFunc.mapIso
      (SSet.boundary.toClassicalCellDiskArrowIso (n + 1)))

private theorem originalCellModelRealizedBoundarySquare
    (n : ℕ) (I : Type u) :
    SSet.toTop.map (originalCellModelBoundarySum n I) ≫ (originalCellModelDisksIso n I).hom =
      (originalCellModelBoundaryIso n I).hom ≫ CellFamilyAttachment.boundaryToDisks I n := by
  let : SSet.toTop.{u}.IsLeftAdjoint := sSetTopAdj.isLeftAdjoint
  apply (isColimitOfHasCoproductOfPreservesColimit SSet.toTop
    (fun _ : I => (SSet.boundary.{u} (n + 1)).toSSet)).hom_ext
  intro ⟨p⟩
  let B0 : SSet.{u} := (SSet.boundary.{u} (n + 1)).toSSet
  let D0 : SSet.{u} := Δ[n + 1]
  let U : TopCat.{u} := SSet.toTop.obj B0
  let V : TopCat.{u} := SSet.toTop.obj D0
  let BU : TopCat.{u} := (classicalCellDiskPair.{u} (n + 1)).snd
  let DV : TopCat.{u} := (classicalCellDiskPair.{u} (n + 1)).fst
  let BC : TopCat.{u} := CellFamilyAttachment.boundaries I n
  let DC : TopCat.{u} := CellFamilyAttachment.disks I n
  let T := originalCellModelBoundaries n I
  let D := originalCellModelDisks n I
  let b : B0 ⟶ T := CategoryTheory.Limits.Sigma.ι (fun _ : I => B0) p
  let d : D0 ⟶ D := CategoryTheory.Limits.Sigma.ι (fun _ : I => D0) p
  let rδ : U ⟶ V := SSet.toTop.map (SSet.boundary.{u} (n + 1)).ι
  let rb : U ⟶ SSet.toTop.obj T := SSet.toTop.map b
  let rd : V ⟶ SSet.toTop.obj D := SSet.toTop.map d
  let rj : SSet.toTop.obj T ⟶ SSet.toTop.obj D :=
    SSet.toTop.map (originalCellModelBoundarySum n I)
  let EB : SSet.toTop.obj T ⟶ BC := (originalCellModelBoundaryIso n I).hom
  let ED : SSet.toTop.obj D ⟶ DC := (originalCellModelDisksIso n I).hom
  let e : Arrow.mk (SSet.toTop.map (SSet.boundary.{u} (n + 1)).ι) ≅
      Arrow.mk (classicalCellDiskPair.{u} (n + 1)).map :=
    SSet.boundary.toClassicalCellDiskArrowIso.{u} (n + 1)
  let eb : U ⟶ BU := e.hom.left
  let ed : V ⟶ DV := e.hom.right
  let cb : BU ⟶ BC := TopCat.sigmaι (fun _ : I => BU) p
  let cd : DV ⟶ DC := TopCat.sigmaι (fun _ : I => DV) p
  let j : BC ⟶ DC := CellFamilyAttachment.boundaryToDisks I n
  let f : BU ⟶ DV := (classicalCellDiskPair.{u} (n + 1)).map
  have hSum : b ≫ originalCellModelBoundarySum n I = (SSet.boundary.{u} (n + 1)).ι ≫ d :=
    CategoryTheory.Limits.Sigma.ι_map (fun _ : I => (SSet.boundary.{u} (n + 1)).ι) p
  have hDisk : rd ≫ ED = ed ≫ cd :=
    originalRealizedFamilyIso_iota I D0 DV (Arrow.rightFunc.mapIso e) p
  have hBoundary : rb ≫ EB = eb ≫ cb :=
    originalRealizedFamilyIso_iota I B0 BU (Arrow.leftFunc.mapIso e) p
  have hClassical : cb ≫ j = f ≫ cd := by
    apply TopCat.ext
    intro z
    rfl
  have hMatch : rδ ≫ ed = eb ≫ f := (Arrow.w e.hom).symm
  have h1 : rb ≫ (rj ≫ ED) = SSet.toTop.map (b ≫ originalCellModelBoundarySum n I) ≫ ED :=
    (Category.assoc rb rj ED).symm.trans
      (congrArg (fun h : U ⟶ SSet.toTop.obj D => h ≫ ED)
        (SSet.toTop.map_comp b (originalCellModelBoundarySum n I)).symm)
  have h2 : SSet.toTop.map (b ≫ originalCellModelBoundarySum n I) ≫ ED =
      SSet.toTop.map ((SSet.boundary.{u} (n + 1)).ι ≫ d) ≫ ED :=
    congrArg (fun h : B0 ⟶ D => SSet.toTop.map h ≫ ED) hSum
  have h3 : SSet.toTop.map ((SSet.boundary.{u} (n + 1)).ι ≫ d) ≫ ED = rδ ≫ (rd ≫ ED) :=
    (congrArg (fun h : U ⟶ SSet.toTop.obj D => h ≫ ED)
      (SSet.toTop.map_comp (SSet.boundary.{u} (n + 1)).ι d)).trans (Category.assoc rδ rd ED)
  have h4 : rδ ≫ (rd ≫ ED) = rδ ≫ (ed ≫ cd) :=
    congrArg (fun h : V ⟶ DC => rδ ≫ h) hDisk
  have h5 : rδ ≫ (ed ≫ cd) = (eb ≫ f) ≫ cd :=
    (Category.assoc rδ ed cd).symm.trans
      (congrArg (fun h : U ⟶ DV => h ≫ cd) hMatch)
  have h6 : (eb ≫ f) ≫ cd = eb ≫ (cb ≫ j) :=
    (Category.assoc eb f cd).trans (congrArg (fun h : BU ⟶ DC => eb ≫ h) hClassical.symm)
  have h7 : eb ≫ (cb ≫ j) = (rb ≫ EB) ≫ j :=
    (Category.assoc eb cb j).symm.trans
      (congrArg (fun h : U ⟶ BC => h ≫ j) hBoundary.symm)
  have h8 : (rb ≫ EB) ≫ j = rb ≫ (EB ≫ j) := Category.assoc rb EB j
  change rb ≫ (rj ≫ ED) = rb ≫ (EB ≫ j)
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans h8))))))

private theorem originalCellModelRealizedAttachingSquare
    (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    SSet.toTop.map (originalCellModelAttaching X n I att) ≫ sSetTopAdj.counit.app X =
      (originalCellModelBoundaryIso n I).hom ≫
        CellFamilyAttachment.attachingMap X n att := by
  let : SSet.toTop.{u}.IsLeftAdjoint := sSetTopAdj.isLeftAdjoint
  apply (isColimitOfHasCoproductOfPreservesColimit SSet.toTop
    (fun _ : I => (SSet.boundary.{u} (n + 1)).toSSet)).hom_ext
  intro ⟨p⟩
  let b := CategoryTheory.Limits.Sigma.ι (fun _ : I => (SSet.boundary.{u} (n + 1)).toSSet) p
  have hMate : b ≫ originalCellModelAttaching X n I att = originalBoundaryAdjunct X n I att p :=
    CategoryTheory.Limits.Sigma.ι_comp_desc (fun q : I => originalBoundaryAdjunct X n I att q) p
  have hAdjunct : SSet.toTop.map (originalBoundaryAdjunct X n I att p) ≫ sSetTopAdj.counit.app X =
      (SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.left ≫ att p :=
    realizedAdjunct_counit ((SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.left ≫ att p)
  have hBoundary : SSet.toTop.map b ≫ (originalCellModelBoundaryIso n I).hom =
      (SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.left ≫ TopCat.sigmaι
        (fun _ : I => (classicalCellDiskPair.{u} (n + 1)).snd) p :=
    originalRealizedFamilyIso_iota I (SSet.boundary.{u} (n + 1)).toSSet
      (classicalCellDiskPair.{u} (n + 1)).snd (Arrow.leftFunc.mapIso
        (SSet.boundary.toClassicalCellDiskArrowIso (n + 1))) p
  have hOriginal : TopCat.sigmaι (fun _ : I => (classicalCellDiskPair.{u} (n + 1)).snd) p ≫
      CellFamilyAttachment.attachingMap X n att =
        att p := by
    apply TopCat.ext
    intro z
    exact CellFamilyAttachment.attachingMap_apply X n att p z
  calc
    SSet.toTop.map b ≫ (SSet.toTop.map (originalCellModelAttaching X n I att) ≫
        sSetTopAdj.counit.app X) = SSet.toTop.map (b ≫ originalCellModelAttaching X n I att) ≫
          sSetTopAdj.counit.app X := by rw [SSet.toTop.map_comp, Category.assoc]
    _ = SSet.toTop.map (originalBoundaryAdjunct X n I att p) ≫ sSetTopAdj.counit.app X :=
      congrArg (fun t => SSet.toTop.map t ≫ sSetTopAdj.counit.app X) hMate
    _ = (SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.left ≫ att p := hAdjunct
    _ = (SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.left ≫ (TopCat.sigmaι
        (fun _ : I => (classicalCellDiskPair.{u} (n + 1)).snd) p ≫
          CellFamilyAttachment.attachingMap X n att) :=
      congrArg (fun t => (SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.left ≫ t)
        hOriginal.symm
    _ = (SSet.toTop.map b ≫ (originalCellModelBoundaryIso n I).hom) ≫
        CellFamilyAttachment.attachingMap X n att :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫ CellFamilyAttachment.attachingMap X n att) hBoundary.symm)
    _ = SSet.toTop.map b ≫ ((originalCellModelBoundaryIso n I).hom ≫
        CellFamilyAttachment.attachingMap X n att) :=
      Category.assoc _ _ _

private theorem originalCellModelRealizedDisksSquare
    (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    SSet.toTop.map (originalCellModelNewDisks X n I att) ≫ originalCellModelRealizationMap X n I att
      =
      (originalCellModelDisksIso n I).hom ≫
        CellFamilyAttachment.diskInclusion X n att := by
  let : SSet.toTop.{u}.IsLeftAdjoint := sSetTopAdj.isLeftAdjoint
  apply (isColimitOfHasCoproductOfPreservesColimit SSet.toTop
    (fun _ : I => (Δ[n + 1] : SSet.{u}))).hom_ext
  intro ⟨p⟩
  let D0 : SSet.{u} := Δ[n + 1]
  let V : TopCat.{u} := SSet.toTop.obj D0
  let DV : TopCat.{u} := (classicalCellDiskPair.{u} (n + 1)).fst
  let DC : TopCat.{u} := CellFamilyAttachment.disks I n
  let Y : TopCat.{u} := CellFamilyAttachment.space X n att
  let D := originalCellModelDisks n I
  let K := originalCellModel X n I att
  let d : D0 ⟶ D := CategoryTheory.Limits.Sigma.ι (fun _ : I => D0) p
  let rd : V ⟶ SSet.toTop.obj D := SSet.toTop.map d
  let rnew : SSet.toTop.obj D ⟶ SSet.toTop.obj K :=
    SSet.toTop.map (originalCellModelNewDisks X n I att)
  let out : SSet.toTop.obj K ⟶ Y := originalCellModelRealizationMap X n I att
  let ED : SSet.toTop.obj D ⟶ DC := (originalCellModelDisksIso n I).hom
  let e : Arrow.mk (SSet.toTop.map (SSet.boundary.{u} (n + 1)).ι) ≅
      Arrow.mk (classicalCellDiskPair.{u} (n + 1)).map :=
    SSet.boundary.toClassicalCellDiskArrowIso.{u} (n + 1)
  let ed : V ⟶ DV := e.hom.right
  let cd : DV ⟶ DC := TopCat.sigmaι (fun _ : I => DV) p
  let i : DC ⟶ Y := CellFamilyAttachment.diskInclusion X n att
  let cell : DV ⟶ Y := CellFamilyAttachment.cell X n att p
  have hDisk : rd ≫ ED = ed ≫ cd :=
    originalRealizedFamilyIso_iota I D0 DV (Arrow.rightFunc.mapIso e) p
  have hCell : cell = cd ≫ i := rfl
  have h1 : rd ≫ (rnew ≫ out) =
      SSet.toTop.map (d ≫ originalCellModelNewDisks X n I att) ≫ out :=
    (Category.assoc rd rnew out).symm.trans
      (congrArg (fun h : V ⟶ SSet.toTop.obj K => h ≫ out)
        (SSet.toTop.map_comp d (originalCellModelNewDisks X n I att)).symm)
  have h2 : SSet.toTop.map (d ≫ originalCellModelNewDisks X n I att) ≫ out = ed ≫ cell :=
    originalCellModelRealizationMap_disk X n I att p
  have h3 : ed ≫ cell = ed ≫ (cd ≫ i) :=
    congrArg (fun h : DV ⟶ Y => ed ≫ h) hCell
  have h4 : ed ≫ (cd ≫ i) = (rd ≫ ED) ≫ i :=
    (Category.assoc ed cd i).symm.trans
      (congrArg (fun h : V ⟶ DC => h ≫ i) hDisk.symm)
  have h5 : (rd ≫ ED) ≫ i = rd ≫ (ED ≫ i) := Category.assoc rd ED i
  change rd ≫ (rnew ≫ out) = rd ≫ (ED ≫ i)
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

private theorem originalCellModelRealizationMap_weak
    (X : TopCat.{u}) [IsCofibrant X]
    (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    TopCat.weakHomotopyEquivalences (originalCellModelRealizationMap X n I att) := by
  let : SSet.toTop.{u}.IsLeftAdjoint := sSetTopAdj.isLeftAdjoint
  let A := SSet.toTop.obj (originalCellModelBoundaries n I)
  let B := SSet.toTop.obj (originalCellModelDisks n I)
  let Z := SSet.toTop.obj (TopCat.toSSet.obj X)
  let i : A ⟶ B := SSet.toTop.map (originalCellModelBoundarySum n I)
  let g : A ⟶ Z := SSet.toTop.map (originalCellModelAttaching X n I att)
  let p := SSet.toTop.map (originalCellModelNewDisks X n I att)
  let q := SSet.toTop.map (originalCellModelOldInclusion X n I att)
  let i' := CellFamilyAttachment.boundaryToDisks I n
  let g' := CellFamilyAttachment.attachingMap X n att
  let p' := CellFamilyAttachment.diskInclusion X n att
  let q' := CellFamilyAttachment.inclusion X n att
  let a := originalCellModelBoundaryIso n I
  let b := originalCellModelDisksIso n I
  let c := sSetTopAdj.counit.app X
  let d := originalCellModelRealizationMap X n I att
  have sq : IsPushout i g p q := (originalCellModelIsPushout X n I att).map SSet.toTop
  have sq' : IsPushout i' g' p' q' :=
    CellFamilyAttachment.isPushout X n att
  have hMono : Mono (originalCellModelBoundarySum n I) := by
    have h := (cofibration_iff _).mp (originalCellModelBoundarySum_cofibration n I)
    change Mono (originalCellModelBoundarySum n I) at h
    exact h
  let : Mono (originalCellModelBoundarySum n I) := hMono
  let : Cofibration i := by
    apply (cofibration_iff _).mpr
    change TopCat.realizedBoundaryInclusions.rlp.llp i
    exact SSet.toTop_map_mem_realizedBoundaryLLP (originalCellModelBoundarySum n I)
  have eArrow : Arrow.mk i ≅ Arrow.mk i' :=
    Arrow.isoMk' i i' a b (originalCellModelRealizedBoundarySquare n I).symm
  have hTopCof : cofibrations TopCat.{u} i :=
    (cofibration_iff i).mp (inferInstance : Cofibration i)
  let : Cofibration i' := (cofibration_iff i').mpr
    (((cofibrations TopCat.{u}).arrow_mk_iso_iff eArrow).mp hTopCof)
  let : IsCofibrant A := SSet.RealizationCWUpgrade.realization_isCofibrant
    (originalCellModelBoundaries n I)
  let : Cofibration a.hom := inferInstance
  let : IsCofibrant (CellFamilyAttachment.boundaries I n) := isCofibrant_of_cofibration a.hom
  let : IsCofibrant Z := SSet.RealizationCWUpgrade.realization_isCofibrant (TopCat.toSSet.obj X)
  let : WeakEquivalence a.hom := inferInstance
  let : WeakEquivalence b.hom := inferInstance
  let : WeakEquivalence c := by
    apply (weakEquivalence_iff _).mpr
    change TopCat.weakHomotopyEquivalences c
    exact SSet.modelCategoryQuillen.counit_mem_weakHomotopyEquivalences X
  have hD : WeakEquivalence d := weakEquivalence_map_of_isPushouts_of_cofibrant sq sq'
    (originalCellModelRealizedBoundarySquare n I)
    (originalCellModelRealizedAttachingSquare X n I att)
    (originalCellModelRealizedDisksSquare X n I att)
    (originalCellModelRealizationMap_old X n I att)
  exact (weakEquivalence_iff _).mp hD

private theorem originalCellModelToSingular_weak
    (X : TopCat.{u}) [IsCofibrant X]
    (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    SSet.realizationWeakEquivalences (originalCellModelToSingular X n I att) := by
  let K := originalCellModel X n I att
  let Y := CellFamilyAttachment.space X n att
  let c : K ⟶ TopCat.toSSet.obj Y := originalCellModelToSingular X n I att
  let d : SSet.toTop.obj K ⟶ Y := originalCellModelRealizationMap X n I att
  let : SSet.KanComplex (TopCat.toSSet.obj (SSet.toTop.obj K)) := TopCat.toSSet_obj_kanComplex _
  let : SSet.KanComplex (TopCat.toSSet.obj Y) := TopCat.toSSet_obj_kanComplex _
  have hTop : TopCat.weakHomotopyEquivalences d := originalCellModelRealizationMap_weak X n I att
  have hSing : SSet.realizationWeakEquivalences (TopCat.toSSet.map d) :=
    (SSet.KanComplex.W_iff_realizationWeakEquivalence (TopCat.toSSet.map d)).mp
      ((TopCat.mem_weakHomotopyEquivalences_iff d).mp hTop)
  have hUnit : SSet.realizationWeakEquivalences (sSetTopAdj.unit.app K) :=
    SSet.modelCategoryQuillen.unit_mem_realizationWeakEquivalences K
  have hMate : c = sSetTopAdj.unit.app K ≫ TopCat.toSSet.map d := by
    have hCounit : (sSetTopAdj.homEquiv K Y).symm c = d := rfl
    have hAdjoint : c = (sSetTopAdj.homEquiv K Y) d :=
      ((sSetTopAdj.homEquiv K Y).apply_symm_apply c).symm.trans
        (congrArg (sSetTopAdj.homEquiv K Y) hCounit)
    exact hAdjoint.trans (sSetTopAdj.homEquiv_unit K Y d)
  have hComposition : SSet.realizationWeakEquivalences
      (sSetTopAdj.unit.app K ≫ TopCat.toSSet.map d) :=
    SSet.realizationWeakEquivalences.comp_mem _ _ hUnit hSing
  change SSet.realizationWeakEquivalences c
  exact Eq.mp (congrArg (fun f : K ⟶ TopCat.toSSet.obj Y =>
    SSet.realizationWeakEquivalences f) hMate.symm) hComposition

end OriginalCellFamilyModelConstruction

public section

namespace AlgebraicTopology.CellFamilySimplicialModel

/-- One entire simplicial boundary for each member of the original family. -/
abbrev boundaries (n : ℕ) (I : Type u) : SSet.{u} :=
  ∐ fun _ : I => (SSet.boundary.{u} (n + 1)).toSSet

/-- One entire standard simplex for each member of the original family. -/
abbrev disks (n : ℕ) (I : Type u) : SSet.{u} :=
  ∐ fun _ : I => (Δ[n + 1] : SSet.{u})

/-- The literal coproduct of the standard boundary inclusions. -/
def boundarySum (n : ℕ) (I : Type u) :
    boundaries n I ⟶ disks n I :=
  CategoryTheory.Limits.Sigma.map (fun _ : I => (SSet.boundary.{u} (n + 1)).ι)

/-- The adjoints of the original attaching maps through the same matched boundary map. -/
def attaching (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    boundaries n I ⟶ TopCat.toSSet.obj X := by
  exact OriginalCellFamilyModelConstruction.originalCellModelAttaching X n I att

/-- The adjoints of all original whole characteristic disks through the same matched disk map. -/
def diskMates (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    disks n I ⟶ TopCat.toSSet.obj (CellFamilyAttachment.space X n att) := by
  exact OriginalCellFamilyModelConstruction.originalCellModelDiskMates X n I att

/-- The literal simplicial pushout of the original attaching-map adjoints. -/
abbrev model (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) : SSet.{u} :=
  pushout (boundarySum n I) (attaching X n I att)

/-- The actual old singular-space inclusion into that pushout. -/
def oldInclusion (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    TopCat.toSSet.obj X ⟶ model X n I att := pushout.inr _ _

/-- The actual whole family of new closed disks in that pushout. -/
def newDisks (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    disks n I ⟶ model X n I att := pushout.inl _ _

/-- The adjoints retain the entire original boundary-gluing square. -/
theorem adjunctSquare (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    boundarySum n I ≫ diskMates X n I att =
      attaching X n I att ≫ TopCat.toSSet.map (CellFamilyAttachment.inclusion X n att) := by
  exact OriginalCellFamilyModelConstruction.originalCellModelAdjunctSquare X n I att

/-- The map to the singular set of the same original cell-family attachment. -/
def toSingular (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    model X n I att ⟶ TopCat.toSSet.obj (CellFamilyAttachment.space X n att) :=
  pushout.desc (diskMates X n I att) (TopCat.toSSet.map (CellFamilyAttachment.inclusion X n att))
    (adjunctSquare X n I att)

/-- Its realization followed by the actual original singular counit. -/
def realizationMap (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    SSet.toTop.obj (model X n I att) ⟶ CellFamilyAttachment.space X n att :=
  SSet.toTop.map (toSingular X n I att) ≫ sSetTopAdj.counit.app (CellFamilyAttachment.space X n att)

/-- The returned model has the actual ordinary simplicial pushout square. -/
theorem isPushout (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    IsPushout (boundarySum n I) (attaching X n I att) (newDisks X n I att) (oldInclusion X n I att)
      := by
  exact IsPushout.of_hasPushout _ _

/-- The old space retains the actual singular map of the original inclusion. -/
theorem toSingular_old (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    oldInclusion X n I att ≫ toSingular X n I att =
      TopCat.toSSet.map (CellFamilyAttachment.inclusion X n att) := by
  exact pushout.inr_desc _ _ _

/-- Every whole new disk retains its original characteristic-map adjoint. -/
theorem toSingular_disks (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    newDisks X n I att ≫ toSingular X n I att = diskMates X n I att := by
  exact pushout.inl_desc _ _ _

/-- The old realization leg is the original counit followed by the original inclusion. -/
theorem realizationMap_old (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    SSet.toTop.map (oldInclusion X n I att) ≫ realizationMap X n I att =
      sSetTopAdj.counit.app X ≫ CellFamilyAttachment.inclusion X n att := by
  exact OriginalCellFamilyModelConstruction.originalCellModelRealizationMap_old X n I att

/-- The whole original closed disk is retained through the same matched parameterization. -/
theorem realizationMap_disk (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) (p : I) :
    SSet.toTop.map (CategoryTheory.Limits.Sigma.ι (fun _ : I => (Δ[n + 1] : SSet.{u})) p ≫
        newDisks X n I att) ≫ realizationMap X n I att =
      (SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.right ≫
        CellFamilyAttachment.cell X n att p := by
  exact OriginalCellFamilyModelConstruction.originalCellModelRealizationMap_disk X n I att p

/-- The actual old-space inclusion is monic in the simplicial model. -/
theorem oldInclusion_mono (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) : Mono (oldInclusion X n I att) := by
  have h := (cofibration_iff _).mp
    (OriginalCellFamilyModelConstruction.originalCellModelOldInclusion_cofibration X n I att)
  change Mono (oldInclusion X n I att) at h
  exact h

/-- The actual realization comparison is weak for every cofibrant source. -/
theorem realizationMap_weak (X : TopCat.{u}) [IsCofibrant X] (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    TopCat.weakHomotopyEquivalences (realizationMap X n I att) := by
  exact OriginalCellFamilyModelConstruction.originalCellModelRealizationMap_weak X n I att

/-- The actual simplicial comparison is weak on all components of the original attachment. -/
theorem toSingular_weak (X : TopCat.{u}) [IsCofibrant X] (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    SSet.realizationWeakEquivalences (toSingular X n I att) := by
  exact OriginalCellFamilyModelConstruction.originalCellModelToSingular_weak X n I att

/-- The boundary-family map is exactly the literal coproduct of boundary inclusions. -/
theorem boundarySum_eq (n : ℕ) (I : Type u) :
    boundarySum n I =
      CategoryTheory.Limits.Sigma.map (fun _ : I => (SSet.boundary.{u} (n + 1)).ι) := by
  rfl

/-- Every actual attaching leg is the original matched-boundary adjoint. -/
theorem attaching_ι (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) (p : I) :
    CategoryTheory.Limits.Sigma.ι (fun _ : I => (SSet.boundary.{u} (n + 1)).toSSet) p ≫
        attaching X n I att =
      sSetTopAdj.homEquiv (SSet.boundary.{u} (n + 1)).toSSet X
        ((SSet.boundary.toClassicalCellDiskArrowIso.{u} (n + 1)).hom.left ≫
          att p) := by
  exact CategoryTheory.Limits.Sigma.ι_comp_desc
    (fun q : I => OriginalCellFamilyModelConstruction.originalBoundaryAdjunct X n I att q) p

/-- Every actual characteristic leg is the original whole matched-disk adjoint. -/
theorem diskMates_ι (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) (p : I) :
    CategoryTheory.Limits.Sigma.ι (fun _ : I => (Δ[n + 1] : SSet.{u})) p ≫ diskMates X n I att =
      sSetTopAdj.homEquiv (Δ[n + 1] : SSet.{u}) (CellFamilyAttachment.space X n att)
        ((SSet.boundary.toClassicalCellDiskArrowIso.{u} (n + 1)).hom.right ≫
          CellFamilyAttachment.cell X n att p) := by
  exact CategoryTheory.Limits.Sigma.ι_comp_desc
    (fun q : I => OriginalCellFamilyModelConstruction.originalDiskAdjunct X n I att q) p

/-- The realization comparison uses the same simplicial map and the actual original counit. -/
theorem realizationMap_eq (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    realizationMap X n I att =
      SSet.toTop.map (toSingular X n I att) ≫
        sSetTopAdj.counit.app (CellFamilyAttachment.space X n att) := by
  rfl

/-- The given Hausdorff classical CW structure derives cofibrancy of the
literal original space; no model or comparison witness is supplied. -/
theorem isCofibrant_of_classicalCW (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] : IsCofibrant X := by
  exact OriginalCellFamilyModelConstruction.originalClassicalCW_isCofibrant X

/-- The literal classical boundary-family inclusion is a model cofibration,
using the same neutral matched disk-boundary isomorphisms. -/
theorem classicalBoundary_cofibration (n : ℕ) (I : Type u) :
    Cofibration (CellFamilyAttachment.boundaryToDisks I n) := by
  let K := OriginalCellFamilyModelConstruction.originalCellModelBoundaries n I
  let L := OriginalCellFamilyModelConstruction.originalCellModelDisks n I
  let f : K ⟶ L := OriginalCellFamilyModelConstruction.originalCellModelBoundarySum n I
  let i : SSet.toTop.obj K ⟶ SSet.toTop.obj L := SSet.toTop.map f
  let j := CellFamilyAttachment.boundaryToDisks I n
  let a := OriginalCellFamilyModelConstruction.originalCellModelBoundaryIso n I
  let b := OriginalCellFamilyModelConstruction.originalCellModelDisksIso n I
  let : Mono f := by
    have h := (cofibration_iff _).mp
      (OriginalCellFamilyModelConstruction.originalCellModelBoundarySum_cofibration n I)
    change Mono f at h
    exact h
  let : Cofibration i := by
    apply (cofibration_iff _).mpr
    change TopCat.realizedBoundaryInclusions.rlp.llp i
    exact SSet.toTop_map_mem_realizedBoundaryLLP f
  have e : Arrow.mk i ≅ Arrow.mk j :=
    Arrow.isoMk' i j a b
      (OriginalCellFamilyModelConstruction.originalCellModelRealizedBoundarySquare n I).symm
  exact (cofibration_iff j).mpr
    (((cofibrations TopCat.{u}).arrow_mk_iso_iff e).mp
      ((cofibration_iff i).mp (inferInstance : Cofibration i)))

/-- Attaching this actual classical cell family preserves cofibrancy of
its original space through the actual pushout inclusion. -/
theorem isCofibrant_attachment (X : TopCat.{u}) [IsCofibrant X]
    (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    IsCofibrant (CellFamilyAttachment.space X n att) := by
  let : Cofibration (CellFamilyAttachment.boundaryToDisks I n) :=
    classicalBoundary_cofibration n I
  let j := CellFamilyAttachment.inclusion X n att
  let : Cofibration j := by
    apply (cofibration_iff _).mpr
    exact (cofibrations TopCat.{u}).of_isPushout
      (CellFamilyAttachment.isPushout X n att).flip
        ((cofibration_iff _).mp
          (inferInstance : Cofibration (CellFamilyAttachment.boundaryToDisks I n)))
  exact isCofibrant_of_cofibration j

/-- Each actual cell retains the same entire boundary/characteristic
adjoint square, in every dimension and index family. -/
theorem adjunctSquare_cell (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) (i : I) :
    sSetTopAdj.homEquiv (SSet.boundary.{u} (n + 1)).toSSet X
        ((SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.left ≫ att i) ≫
      TopCat.toSSet.map (CellFamilyAttachment.inclusion X n att) =
        (SSet.boundary.{u} (n + 1)).ι ≫
          sSetTopAdj.homEquiv (Δ[n + 1] : SSet.{u}) (CellFamilyAttachment.space X n att)
            ((SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.right ≫
              CellFamilyAttachment.cell X n att i)
              := by
  exact OriginalCellFamilyModelConstruction.originalAdjunct_square X n I att i

end AlgebraicTopology.CellFamilySimplicialModel

end
