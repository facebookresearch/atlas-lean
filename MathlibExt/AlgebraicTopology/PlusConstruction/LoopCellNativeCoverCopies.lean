/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverPullbackCopies
public import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellSphericalGenerators
public import MathlibExt.AlgebraicTopology.PlusConstruction.CellFundamentalGroupQuotient
public import MathlibExt.Topology.Homotopy.TopCat.HurewiczOne
public import Mathlib.CategoryTheory.Conj

/-!
# The original lifted two-cell families

The native disk lifts are computed from the original two-cell attachment.
Their deck translates give the entire pulled-back disk family. The copy
labels identify with the literal quotient fundamental group through the
original singular point connector and the original van Kampen quotient map.
The boundary map retains the same chosen lifts. No identity-path condition
is imposed on the chosen first vertex of an individual disk lift.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicTopology.LoopCellSphericalGenerators
open scoped Simplicial

universe u

namespace AlgebraicTopology.LoopCellNativeCoverCopies

attribute [local instance] TopCat.toSSet_obj_kanComplex

/-- The actual native deck group is the original quotient fundamental group. -/
def nativeDeckGroupEquiv (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    End (SSet.FundamentalGroupoid.mk (nativeTargetPoint X x P)) ≃*
      FundamentalGroup X x ⧸ P := by
  let Y : TopCat.{u} := LoopCellAttachment.space X x P
  let f : X ⟶ Y := LoopCellAttachment.inclusion X x P
  let xs : (TopCat.toSSet.obj X) _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm x
  have hObj : (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)).obj
        (SSet.FundamentalGroupoid.mk xs) =
      SSet.FundamentalGroupoid.mk (nativeTargetPoint X x P) :=
    SSet.mapFundamentalGroupoid_obj_mk (TopCat.toSSet.map f) xs
  let e : SSet.FundamentalGroupoid.mk (nativeTargetPoint X x P) ≅
      SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm (f x)) :=
    (eqToIso hObj).symm ≪≫ TopCat.singularMappedVertexIso f x
  let d : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm (f x))) ≃*
      FundamentalGroup Y (f x) :=
    TopCat.singularFundamentalGroupoidEndMulEquiv Y (f x)
  let q : FundamentalGroup Y (f x) ≃* (FundamentalGroup X x ⧸ P) :=
    (LoopCellAttachment.fundamentalGroupQuotientMulEquiv X x P).symm
  exact e.conj.trans (d.trans q)

/-- The computed deck dictionary is the original quotient map after the
actual singular image-point equality, with no normalization of any disk lift. -/
theorem nativeDeckGroupEquiv_canonical (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (a : End (SSet.FundamentalGroupoid.mk (nativeTargetPoint X x P))) :
    let Y : TopCat.{u} := LoopCellAttachment.space X x P
    let f : X ⟶ Y := LoopCellAttachment.inclusion X x P
    let K : SSet.{u} := TopCat.toSSet.obj Y
    let sx : (TopCat.toSSet.obj X) _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm x
    let F : SSet.FundamentalGroupoid (TopCat.toSSet.obj X) ⥤ SSet.FundamentalGroupoid K :=
      SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)
    let A : SSet.FundamentalGroupoid K := F.obj (SSet.FundamentalGroupoid.mk sx)
    let B : SSet.FundamentalGroupoid K := SSet.FundamentalGroupoid.mk (nativeTargetPoint X x P)
    let C : SSet.FundamentalGroupoid K :=
        SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm (f x))
    let hObj : A = B := SSet.mapFundamentalGroupoid_obj_mk (TopCat.toSSet.map f) sx
    let hMap : A = C := TopCat.singularMappedVertex_eq f x
    let c : B ≅ C := eqToIso (hObj.symm.trans hMap)
    let d : End C ≃* FundamentalGroup Y (f x) :=
        TopCat.singularFundamentalGroupoidEndMulEquiv Y (f x)
    let q : FundamentalGroup Y (f x) ≃* (FundamentalGroup X x ⧸ P) :=
      (LoopCellAttachment.fundamentalGroupQuotientMulEquiv X x P).symm
    let aB : End B := a
    nativeDeckGroupEquiv X x P a = q (d (c.conj aB)) := by
  let Y : TopCat.{u} := LoopCellAttachment.space X x P
  let f : X ⟶ Y := LoopCellAttachment.inclusion X x P
  let K : SSet.{u} := TopCat.toSSet.obj Y
  let sx : (TopCat.toSSet.obj X) _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm x
  let F : SSet.FundamentalGroupoid (TopCat.toSSet.obj X) ⥤ SSet.FundamentalGroupoid K :=
    SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)
  let A : SSet.FundamentalGroupoid K := F.obj (SSet.FundamentalGroupoid.mk sx)
  let B : SSet.FundamentalGroupoid K := SSet.FundamentalGroupoid.mk (nativeTargetPoint X x P)
  let C : SSet.FundamentalGroupoid K := SSet.FundamentalGroupoid.mk
      (TopCat.toSSetObj₀Equiv.symm (f x))
  let hObj : A = B := SSet.mapFundamentalGroupoid_obj_mk (TopCat.toSSet.map f) sx
  let hMap : A = C := TopCat.singularMappedVertex_eq f x
  let e : B ≅ C := (eqToIso hObj).symm ≪≫ TopCat.singularMappedVertexIso f x
  let c : B ≅ C := eqToIso (hObj.symm.trans hMap)
  let d : End C ≃* FundamentalGroup Y (f x) := TopCat.singularFundamentalGroupoidEndMulEquiv Y (f x)
  let q : FundamentalGroup Y (f x) ≃* (FundamentalGroup X x ⧸ P) :=
    (LoopCellAttachment.fundamentalGroupQuotientMulEquiv X x P).symm
  let aB : End B := a
  have hSymm : (eqToIso hObj : A ≅ B).symm = (eqToIso hObj.symm : B ≅ A) := by
    apply Iso.ext
    rfl
  have hRecipe : (TopCat.singularMappedVertexIso f x : A ≅ C) = (eqToIso hMap : A ≅ C) :=
    TopCat.singularMappedVertexIso_eq f x
  have hE : e = c :=
    (congrArg (fun t : A ≅ C => (eqToIso hObj : A ≅ B).symm ≪≫ t) hRecipe).trans
      ((congrArg (fun t : B ≅ A => t ≪≫ (eqToIso hMap : A ≅ C)) hSymm).trans
        (eqToIso_trans hObj.symm hMap))
  have hValue : q (d (e.conj aB)) = q (d (c.conj aB)) :=
    congrArg (fun t : B ≅ C => q (d (t.conj aB))) hE
  change q (d (e.conj aB)) = q (d (c.conj aB))
  exact hValue

/-- The full original subgroup-indexed standard two-disk family. -/
abbrev diskFamily (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) : SSet.{u} :=
  ∐ fun _ : P => (Δ[2] : SSet.{u})

/-- The full original subgroup-indexed standard boundary family. -/
abbrev boundaryFamily (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) : SSet.{u} :=
  ∐ fun _ : P => (SSet.boundary.{u} 2).toSSet

/-- The literal map from all the original boundaries to all the original disks. -/
def boundarySum (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) : boundaryFamily X x P ⟶ diskFamily X x P :=
  CategoryTheory.Limits.Sigma.map (fun _ : P => (SSet.boundary.{u} 2).ι)

/-- The actual computed whole disk family in the same original native cover. -/
def diskFamilyLift (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) : diskFamily X x P ⟶ nativeCover X x P :=
  CategoryTheory.Limits.Sigma.desc (fun p : P => nativeDiskLift X x P p)

/-- The actual computed boundary family in the same original pulled-back old cover. -/
def boundaryFamilyLift (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    boundaryFamily X x P ⟶ nativePullback X x P :=
  CategoryTheory.Limits.Sigma.desc (fun p : P => nativeBoundaryLift X x P p)

/-- Every whole disk projects to its original characteristic-map adjoint. -/
theorem diskFamilyLift_projection (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    diskFamilyLift X x P ≫ SSet.KanComplex.nativeCoverProjection
        (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P) =
      CategoryTheory.Limits.Sigma.desc (fun p : P =>
        sSetTopAdj.homEquiv (Δ[2] : SSet.{u}) (LoopCellAttachment.space X x P)
          ((diskBoundaryArrowIso 2).hom.right ≫ LoopCellAttachment.cell X x P p)) := by
  apply CategoryTheory.Limits.Sigma.hom_ext
  intro p
  calc
    CategoryTheory.Limits.Sigma.ι (fun _ : P => (Δ[2] : SSet.{u})) p ≫
        (diskFamilyLift X x P ≫ SSet.KanComplex.nativeCoverProjection
          (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P)) =
        (CategoryTheory.Limits.Sigma.ι (fun _ : P => (Δ[2] : SSet.{u})) p ≫
          diskFamilyLift X x P) ≫ SSet.KanComplex.nativeCoverProjection
            (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P) :=
      (Category.assoc _ _ _).symm
    _ = nativeDiskLift X x P p ≫ SSet.KanComplex.nativeCoverProjection
        (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P) :=
      congrArg (fun h => h ≫ SSet.KanComplex.nativeCoverProjection
        (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P))
        (CategoryTheory.Limits.Sigma.ι_comp_desc (fun q : P => nativeDiskLift X x P q) p)
    _ = _ := (nativeDiskLift_projection X x P p).trans
      (CategoryTheory.Limits.Sigma.ι_comp_desc (fun q : P =>
        sSetTopAdj.homEquiv (Δ[2] : SSet.{u}) (LoopCellAttachment.space X x P)
          ((diskBoundaryArrowIso 2).hom.right ≫ LoopCellAttachment.cell X x P q)) p).symm

/-- The entire old-cover boundary family is the boundary of the SAME chosen disk family. -/
theorem boundaryFamilyLift_toCover (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    boundaryFamilyLift X x P ≫ nativePullbackToCover X x P =
      boundarySum X x P ≫ diskFamilyLift X x P := by
  apply CategoryTheory.Limits.Sigma.hom_ext
  intro p
  have hb : CategoryTheory.Limits.Sigma.ι
      (fun _ : P => (SSet.boundary.{u} 2).toSSet) p ≫ boundaryFamilyLift X x P =
        nativeBoundaryLift X x P p :=
    CategoryTheory.Limits.Sigma.ι_comp_desc (fun q : P => nativeBoundaryLift X x P q) p
  have hj : CategoryTheory.Limits.Sigma.ι
      (fun _ : P => (SSet.boundary.{u} 2).toSSet) p ≫ boundarySum X x P =
        (SSet.boundary.{u} 2).ι ≫
          CategoryTheory.Limits.Sigma.ι (fun _ : P => (Δ[2] : SSet.{u})) p :=
    CategoryTheory.Limits.Sigma.ι_map (fun _ : P => (SSet.boundary.{u} 2).ι) p
  have hd : CategoryTheory.Limits.Sigma.ι (fun _ : P => (Δ[2] : SSet.{u})) p ≫
      diskFamilyLift X x P = nativeDiskLift X x P p :=
    CategoryTheory.Limits.Sigma.ι_comp_desc (fun q : P => nativeDiskLift X x P q) p
  calc
    CategoryTheory.Limits.Sigma.ι (fun _ : P => (SSet.boundary.{u} 2).toSSet) p ≫
        (boundaryFamilyLift X x P ≫ nativePullbackToCover X x P) =
        (CategoryTheory.Limits.Sigma.ι (fun _ : P => (SSet.boundary.{u} 2).toSSet) p ≫
          boundaryFamilyLift X x P) ≫ nativePullbackToCover X x P :=
      (Category.assoc _ _ _).symm
    _ = nativeBoundaryLift X x P p ≫ nativePullbackToCover X x P :=
      congrArg (fun h => h ≫ nativePullbackToCover X x P) hb
    _ = (SSet.boundary.{u} 2).ι ≫ nativeDiskLift X x P p :=
      nativeBoundaryLift_toCover X x P p
    _ = (SSet.boundary.{u} 2).ι ≫
        (CategoryTheory.Limits.Sigma.ι (fun _ : P => (Δ[2] : SSet.{u})) p ≫
          diskFamilyLift X x P) := congrArg (fun h => (SSet.boundary.{u} 2).ι ≫ h) hd.symm
    _ = ((SSet.boundary.{u} 2).ι ≫
        CategoryTheory.Limits.Sigma.ι (fun _ : P => (Δ[2] : SSet.{u})) p) ≫
          diskFamilyLift X x P := (Category.assoc _ _ _).symm
    _ = (CategoryTheory.Limits.Sigma.ι (fun _ : P => (SSet.boundary.{u} 2).toSSet) p ≫
        boundarySum X x P) ≫ diskFamilyLift X x P :=
      congrArg (fun h => h ≫ diskFamilyLift X x P) hj.symm
    _ = CategoryTheory.Limits.Sigma.ι (fun _ : P => (SSet.boundary.{u} 2).toSSet) p ≫
        (boundarySum X x P ≫ diskFamilyLift X x P) := Category.assoc _ _ _

/-- Every quotient-group copy of every original disk gives the entire literal pulled family. -/
def diskFamilyCopiesIso (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    (∐ fun _ : FundamentalGroup X x ⧸ P => diskFamily X x P) ≅
      pullback (diskFamilyLift X x P ≫ SSet.KanComplex.nativeCoverProjection
          (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P))
        (SSet.KanComplex.nativeCoverProjection
          (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P)) := by
  let e := nativeDeckGroupEquiv X x P
  let reindex : (∐ fun _ : FundamentalGroup X x ⧸ P => diskFamily X x P) ≅
      (∐ fun _ : End (SSet.FundamentalGroupoid.mk (nativeTargetPoint X x P)) =>
        diskFamily X x P) :=
    CategoryTheory.Limits.Sigma.whiskerEquiv e.symm.toEquiv
      (fun _ => Iso.refl (diskFamily X x P))
  exact reindex ≪≫ SSet.KanComplex.nativeCoverPullbackCopiesIso (diskFamilyLift X x P)

/-- Each quotient label gives the SAME whole chosen lift followed by its actual deck map. -/
theorem diskFamilyCopiesIso_ι (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    CategoryTheory.Limits.Sigma.ι (fun _ : FundamentalGroup X x ⧸ P => diskFamily X x P) q ≫
        (diskFamilyCopiesIso X x P).hom =
      SSet.KanComplex.nativeCoverCopyLift (diskFamilyLift X x P)
        ((nativeDeckGroupEquiv X x P).symm q) := by
  let e := nativeDeckGroupEquiv X x P
  let reindex : (∐ fun _ : FundamentalGroup X x ⧸ P => diskFamily X x P) ≅
      (∐ fun _ : End (SSet.FundamentalGroupoid.mk (nativeTargetPoint X x P)) =>
        diskFamily X x P) :=
    CategoryTheory.Limits.Sigma.whiskerEquiv e.symm.toEquiv
      (fun _ => Iso.refl (diskFamily X x P))
  have hi : CategoryTheory.Limits.Sigma.ι
        (fun _ : FundamentalGroup X x ⧸ P => diskFamily X x P) q ≫ reindex.hom =
      CategoryTheory.Limits.Sigma.ι
        (fun _ : End (SSet.FundamentalGroupoid.mk (nativeTargetPoint X x P)) =>
          diskFamily X x P) (e.symm q) := by
    let Q := FundamentalGroup X x ⧸ P
    let G := End (SSet.FundamentalGroupoid.mk (nativeTargetPoint X x P))
    let K : SSet.{u} := diskFamily X x P
    have hStock : CategoryTheory.Limits.Sigma.ι (fun _ : Q => K) q ≫
        CategoryTheory.Limits.Sigma.map' (f := fun _ : G => K) (g := fun _ : Q => K)
          (e.symm.toEquiv : Q → G) (fun _ : Q => (𝟙 K : K ⟶ K)) =
      CategoryTheory.Limits.Sigma.ι (fun _ : G => K) (e.symm.toEquiv q) :=
      (CategoryTheory.Limits.Sigma.ι_comp_map'
        (f := fun _ : G => K) (g := fun _ : Q => K) (e.symm.toEquiv : Q → G)
        (fun _ : Q => (𝟙 K : K ⟶ K)) q).trans (Category.id_comp _)
    have hIndex : e.symm.toEquiv q = e.symm q := by
      simpa only [MulEquiv.toEquiv_eq_coe] using congrFun (MulEquiv.coe_toEquiv e.symm) q
    have hComponent : CategoryTheory.Limits.Sigma.ι (fun _ : Q => K) q ≫
        CategoryTheory.Limits.Sigma.map' (f := fun _ : G => K) (g := fun _ : Q => K)
          (e.symm.toEquiv : Q → G) (fun _ : Q => (𝟙 K : K ⟶ K)) =
      CategoryTheory.Limits.Sigma.ι (fun _ : G => K) (e.symm q) :=
      hStock.trans (congrArg (fun a : G => CategoryTheory.Limits.Sigma.ι (fun _ : G => K) a) hIndex)
    simpa only [reindex, CategoryTheory.Limits.Sigma.whiskerEquiv,
      Iso.refl_hom, Iso.refl_inv, eqToHom_refl, Category.comp_id, Category.id_comp,
      MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv] using hComponent
  change CategoryTheory.Limits.Sigma.ι
      (fun _ : FundamentalGroup X x ⧸ P => diskFamily X x P) q ≫
        (reindex.hom ≫ (SSet.KanComplex.nativeCoverPullbackCopiesIso
          (diskFamilyLift X x P)).hom) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun h => h ≫ (SSet.KanComplex.nativeCoverPullbackCopiesIso
      (diskFamilyLift X x P)).hom) hi).trans
        (SSet.KanComplex.nativeCoverPullbackCopiesIso_ι (diskFamilyLift X x P) (e.symm q)))

/-- The unit label is the actual chosen disk family, without an identity-path assumption. -/
theorem diskFamilyCopiesIso_unit (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    CategoryTheory.Limits.Sigma.ι (fun _ : FundamentalGroup X x ⧸ P => diskFamily X x P) 1 ≫
        (diskFamilyCopiesIso X x P).hom =
      SSet.KanComplex.nativeCoverCopyLift (diskFamilyLift X x P)
        (1 : End (SSet.FundamentalGroupoid.mk (nativeTargetPoint X x P))) := by
  exact (diskFamilyCopiesIso_ι X x P 1).trans
    (congrArg (fun a => SSet.KanComplex.nativeCoverCopyLift (diskFamilyLift X x P) a)
      (nativeDeckGroupEquiv X x P).symm.map_one)

/-- The actual deck action is left multiplication on EVERY original quotient-labelled copy. -/
theorem diskFamilyCopiesIso_deck_ι (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (q r : FundamentalGroup X x ⧸ P) :
    CategoryTheory.Limits.Sigma.ι
        (fun _ : FundamentalGroup X x ⧸ P => diskFamily X x P) (q * r) ≫
          (diskFamilyCopiesIso X x P).hom =
      (CategoryTheory.Limits.Sigma.ι
        (fun _ : FundamentalGroup X x ⧸ P => diskFamily X x P) r ≫
          (diskFamilyCopiesIso X x P).hom) ≫
        SSet.KanComplex.nativeCoverCopyPullbackDeck (diskFamilyLift X x P)
          ((nativeDeckGroupEquiv X x P).symm q) := by
  let e := nativeDeckGroupEquiv X x P
  exact (diskFamilyCopiesIso_ι X x P (q * r)).trans
    ((congrArg (fun a => SSet.KanComplex.nativeCoverCopyLift (diskFamilyLift X x P) a)
      (e.symm.map_mul q r)).trans
        ((SSet.KanComplex.nativeCoverCopyLift_deck (diskFamilyLift X x P)
          (e.symm q) (e.symm r)).trans
            (congrArg (fun h => h ≫ SSet.KanComplex.nativeCoverCopyPullbackDeck
              (diskFamilyLift X x P) (e.symm q)) (diskFamilyCopiesIso_ι X x P r).symm)))

/-- The entire boundary pullback uses restrictions of the SAME chosen disk family. -/
def boundaryFamilyCopiesIso (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    (∐ fun _ : FundamentalGroup X x ⧸ P => boundaryFamily X x P) ≅
      pullback ((boundarySum X x P ≫ diskFamilyLift X x P) ≫
          SSet.KanComplex.nativeCoverProjection
            (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P))
        (SSet.KanComplex.nativeCoverProjection
          (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P)) := by
  let e := nativeDeckGroupEquiv X x P
  let reindex : (∐ fun _ : FundamentalGroup X x ⧸ P => boundaryFamily X x P) ≅
      (∐ fun _ : End (SSet.FundamentalGroupoid.mk (nativeTargetPoint X x P)) =>
        boundaryFamily X x P) :=
    CategoryTheory.Limits.Sigma.whiskerEquiv e.symm.toEquiv
      (fun _ => Iso.refl (boundaryFamily X x P))
  exact reindex ≪≫ SSet.KanComplex.nativeCoverPullbackCopiesIso
    (boundarySum X x P ≫ diskFamilyLift X x P)

/-- Each boundary copy retains the same quotient label and the same translated disk boundary. -/
theorem boundaryFamilyCopiesIso_ι (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    CategoryTheory.Limits.Sigma.ι
        (fun _ : FundamentalGroup X x ⧸ P => boundaryFamily X x P) q ≫
          (boundaryFamilyCopiesIso X x P).hom =
      SSet.KanComplex.nativeCoverCopyLift (boundarySum X x P ≫ diskFamilyLift X x P)
        ((nativeDeckGroupEquiv X x P).symm q) := by
  let e := nativeDeckGroupEquiv X x P
  let reindex : (∐ fun _ : FundamentalGroup X x ⧸ P => boundaryFamily X x P) ≅
      (∐ fun _ : End (SSet.FundamentalGroupoid.mk (nativeTargetPoint X x P)) =>
        boundaryFamily X x P) :=
    CategoryTheory.Limits.Sigma.whiskerEquiv e.symm.toEquiv
      (fun _ => Iso.refl (boundaryFamily X x P))
  have hi : CategoryTheory.Limits.Sigma.ι
        (fun _ : FundamentalGroup X x ⧸ P => boundaryFamily X x P) q ≫ reindex.hom =
      CategoryTheory.Limits.Sigma.ι
        (fun _ : End (SSet.FundamentalGroupoid.mk (nativeTargetPoint X x P)) =>
          boundaryFamily X x P) (e.symm q) := by
    let Q := FundamentalGroup X x ⧸ P
    let G := End (SSet.FundamentalGroupoid.mk (nativeTargetPoint X x P))
    let K : SSet.{u} := boundaryFamily X x P
    have hStock : CategoryTheory.Limits.Sigma.ι (fun _ : Q => K) q ≫
        CategoryTheory.Limits.Sigma.map' (f := fun _ : G => K) (g := fun _ : Q => K)
          (e.symm.toEquiv : Q → G) (fun _ : Q => (𝟙 K : K ⟶ K)) =
      CategoryTheory.Limits.Sigma.ι (fun _ : G => K) (e.symm.toEquiv q) :=
      (CategoryTheory.Limits.Sigma.ι_comp_map'
        (f := fun _ : G => K) (g := fun _ : Q => K) (e.symm.toEquiv : Q → G)
        (fun _ : Q => (𝟙 K : K ⟶ K)) q).trans (Category.id_comp _)
    have hIndex : e.symm.toEquiv q = e.symm q := by
      simpa only [MulEquiv.toEquiv_eq_coe] using congrFun (MulEquiv.coe_toEquiv e.symm) q
    have hComponent : CategoryTheory.Limits.Sigma.ι (fun _ : Q => K) q ≫
        CategoryTheory.Limits.Sigma.map' (f := fun _ : G => K) (g := fun _ : Q => K)
          (e.symm.toEquiv : Q → G) (fun _ : Q => (𝟙 K : K ⟶ K)) =
      CategoryTheory.Limits.Sigma.ι (fun _ : G => K) (e.symm q) :=
      hStock.trans (congrArg (fun a : G => CategoryTheory.Limits.Sigma.ι (fun _ : G => K) a) hIndex)
    simpa only [reindex, CategoryTheory.Limits.Sigma.whiskerEquiv,
      Iso.refl_hom, Iso.refl_inv, eqToHom_refl, Category.comp_id, Category.id_comp,
      MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv] using hComponent
  change CategoryTheory.Limits.Sigma.ι
      (fun _ : FundamentalGroup X x ⧸ P => boundaryFamily X x P) q ≫
        (reindex.hom ≫ (SSet.KanComplex.nativeCoverPullbackCopiesIso
          (boundarySum X x P ≫ diskFamilyLift X x P)).hom) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun h => h ≫ (SSet.KanComplex.nativeCoverPullbackCopiesIso
      (boundarySum X x P ≫ diskFamilyLift X x P)).hom) hi).trans
        (SSet.KanComplex.nativeCoverPullbackCopiesIso_ι
          (boundarySum X x P ≫ diskFamilyLift X x P) (e.symm q)))

/-- The original boundary inclusion sends each whole boundary copy into the SAME disk copy. -/
theorem boundaryFamilyCopiesIso_disk_ι (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    boundarySum X x P ≫
        (CategoryTheory.Limits.Sigma.ι
          (fun _ : FundamentalGroup X x ⧸ P => diskFamily X x P) q ≫
            (diskFamilyCopiesIso X x P).hom) =
      (CategoryTheory.Limits.Sigma.ι
        (fun _ : FundamentalGroup X x ⧸ P => boundaryFamily X x P) q ≫
          (boundaryFamilyCopiesIso X x P).hom) ≫
        SSet.KanComplex.nativeCoverCopyBaseChange (diskFamilyLift X x P) (boundarySum X x P) := by
  let e := nativeDeckGroupEquiv X x P
  exact (congrArg (fun h => boundarySum X x P ≫ h) (diskFamilyCopiesIso_ι X x P q)).trans
    ((SSet.KanComplex.nativeCoverCopyLift_baseChange (diskFamilyLift X x P)
      (boundarySum X x P) (e.symm q)).trans
        (congrArg (fun h => h ≫ SSet.KanComplex.nativeCoverCopyBaseChange
          (diskFamilyLift X x P) (boundarySum X x P)) (boundaryFamilyCopiesIso_ι X x P q).symm))

/-- The computed family boundary map is the literal coproduct of original boundary inclusions. -/
theorem boundarySum_eq (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    boundarySum X x P =
      CategoryTheory.Limits.Sigma.map (fun _ : P => (SSet.boundary.{u} 2).ι) := by
  rfl

/-- Every component of the computed disk family is the SAME original chosen native lift. -/
theorem diskFamilyLift_ι (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    CategoryTheory.Limits.Sigma.ι (fun _ : P => (Δ[2] : SSet.{u})) p ≫
      diskFamilyLift X x P = nativeDiskLift X x P p := by
  exact CategoryTheory.Limits.Sigma.ι_comp_desc (fun q : P => nativeDiskLift X x P q) p

/-- Every boundary component is the SAME original boundary lift into the old cover. -/
theorem boundaryFamilyLift_ι (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    CategoryTheory.Limits.Sigma.ι (fun _ : P => (SSet.boundary.{u} 2).toSSet) p ≫
      boundaryFamilyLift X x P = nativeBoundaryLift X x P p := by
  exact CategoryTheory.Limits.Sigma.ι_comp_desc (fun q : P => nativeBoundaryLift X x P q) p

end AlgebraicTopology.LoopCellNativeCoverCopies

end
