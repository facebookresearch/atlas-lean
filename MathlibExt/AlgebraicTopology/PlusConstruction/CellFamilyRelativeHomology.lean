/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CellAttachmentPointQuotient
public import MathlibExt.AlgebraicTopology.SingularHomology.CofiberPairPointQuotient
public import MathlibExt.AlgebraicTopology.SingularHomology.RelativeHomologyCoproducts
public import MathlibExt.AlgebraicTopology.SingularHomology.Sphere.HomologyUniverse

/-!
# Relative homology of actual cell-family attachments

For an arbitrary family of `(n + 1)`-cells, the literal coproduct of disk
pairs maps to the pair formed by the original-space inclusion in the actual
attachment.  The point-quotient comparison proves that this pair map induces
an isomorphism on relative singular homology.  Combining it with preservation
of coproducts and the existing disk-pair coordinate identifies relative
homology in degree `n + 1` with one copy of the coefficient group per cell and
proves vanishing in every other natural or integer degree.

The construction uses the actual attachment pushout throughout.  It assumes
no excision comparison, quotient equivalence, cellular boundary, spherical
representative, or plus-construction witness.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.CWComplex

universe u

namespace AlgebraicTopology.CellFamilyAttachment

variable {ι : Type u} (X : TopCat.{u}) (n : ℕ)
variable (a : ι → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X))

private theorem ndr_isPointQuotientHomologyPair
    {P : TopPair.{u}} (d : TopPair.NDRData P) :
    AlgebraicTopology.isPointQuotientHomologyPair P := by
  classical
  by_cases h : Nonempty P.snd
  · let _ : Nonempty P.snd := h
    exact Or.inl ⟨d.toGoodPairData⟩
  · let _ : IsEmpty P.snd := ⟨fun x => h ⟨x⟩⟩
    exact Or.inr inferInstance

/-- The literal family pair is a good pair when its boundary family is
nonempty, and is a point-quotient homology pair by the empty branch otherwise. -/
theorem literalPair_isPointQuotientHomologyPair :
    AlgebraicTopology.isPointQuotientHomologyPair (literalPair ι n) :=
  ndr_isPointQuotientHomologyPair (ndrData ι n)

/-- The pair formed by the original-space inclusion in the actual attachment
is a good pair when the original space is nonempty, and uses the empty branch
otherwise. -/
theorem attachmentPair_isPointQuotientHomologyPair :
    AlgebraicTopology.isPointQuotientHomologyPair
      (CellCollarDeformation.attachmentPair X n a) :=
  ndr_isPointQuotientHomologyPair (CellCollarDeformation.attachmentData X n a)

/-- The literal pair, bundled with the evidence required by the canonical
relative-to-point-quotient homology comparison. -/
noncomputable def literalPointQuotientHomologyPair :
    AlgebraicTopology.PointQuotientHomologyPair.{u} :=
  ⟨literalPair ι n, literalPair_isPointQuotientHomologyPair (ι := ι) n⟩

/-- The actual attachment pair, bundled with its constructed NDR evidence. -/
noncomputable def attachmentPointQuotientHomologyPair :
    AlgebraicTopology.PointQuotientHomologyPair.{u} :=
  ⟨CellCollarDeformation.attachmentPair X n a,
    attachmentPair_isPointQuotientHomologyPair X n a⟩

/-- The actual literal-to-attachment pair map in the full subcategory of
point-quotient homology pairs. -/
def literalToAttachmentPointQuotientHomologyPair :
    literalPointQuotientHomologyPair (ι := ι) n ⟶
      attachmentPointQuotientHomologyPair X n a :=
  ObjectProperty.homMk (literalToAttachmentPair X n a)

/-- The actual literal-to-attachment pair map induces an isomorphism on
relative singular homology in every natural degree. -/
theorem isIso_relativeSingularHomology_map_literalToAttachmentPair
    (R : AddCommGrpCat.{u}) (k : ℕ) :
    IsIso ((relativeSingularHomologyFunctor AddCommGrpCat.{u} R k).map
      (literalToAttachmentPair X n a)) := by
  let P := literalPointQuotientHomologyPair (ι := ι) n
  let Q := attachmentPointQuotientHomologyPair X n a
  let f : P ⟶ Q := literalToAttachmentPointQuotientHomologyPair X n a
  let η := pointQuotientRelativeReducedSingularHomologyNatIso
    AddCommGrpCat.{u} R k
  let _ : IsIso
      (TopPair.pointQuotientFunctor.map (literalToAttachmentPair X n a)) :=
    inferInstance
  let _ : IsIso
      (TopPair.pointQuotientFunctor.map
        (literalToAttachmentPair X n a)).right := by
    change IsIso ((Under.forget (TopCat.of PUnit)).map
      (TopPair.pointQuotientFunctor.map
        (literalToAttachmentPair X n a)))
    infer_instance
  let redMap :=
    (reducedSingularHomologyFunctor AddCommGrpCat.{u} R k).map
      (TopPair.pointQuotientFunctor.map
        (literalToAttachmentPair X n a)).right
  let _ : IsIso redMap := by infer_instance
  have hComm :
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R k).map
            (literalToAttachmentPair X n a) ≫ η.hom.app Q =
        η.hom.app P ≫ redMap := by
    have h := η.hom.naturality f
    change
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R k).map
            (literalToAttachmentPair X n a) ≫ η.hom.app Q =
        η.hom.app P ≫ redMap at h
    exact h
  let hEtaP : IsIso (η.hom.app P) := NatIso.hom_app_isIso η P
  let hRedMap : IsIso redMap := inferInstance
  let hRight : IsIso (η.hom.app P ≫ redMap) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ hEtaP hRedMap
  exact @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _
    (inferInstance : IsIso (η.hom.app Q)) hRight hComm

/-- Relative homology of the literal family and the actual attachment pair
are canonically isomorphic through the genuine pair map. -/
noncomputable def literalToAttachmentRelativeHomologyIso
    (R : AddCommGrpCat.{u}) (k : ℕ) :
    (relativeSingularHomologyFunctor AddCommGrpCat.{u} R k).obj
        (literalPair ι n) ≅
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R k).obj
        (CellCollarDeformation.attachmentPair X n a) := by
  let _ := isIso_relativeSingularHomology_map_literalToAttachmentPair X n a R k
  exact asIso ((relativeSingularHomologyFunctor AddCommGrpCat.{u} R k).map
    (literalToAttachmentPair X n a))

@[simp]
theorem literalToAttachmentRelativeHomologyIso_hom
    (R : AddCommGrpCat.{u}) (k : ℕ) :
    (literalToAttachmentRelativeHomologyIso X n a R k).hom =
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R k).map
        (literalToAttachmentPair X n a) :=
  rfl

/-- The component disk pair maps to the actual attachment pair through the
literal pair comparison. -/
def cellPairMap (i : ι) :
    classicalCellDiskPair.{u} (n + 1) ⟶
      CellCollarDeformation.attachmentPair X n a :=
  TopPair.sigmaι (fun _ : ι => classicalCellDiskPair.{u} (n + 1)) i ≫
    (sigmaPairIso ι n).hom ≫ literalToAttachmentPair X n a

/-- The ambient map of a component pair is its actual characteristic disk. -/
theorem cellPairMap_fst (i : ι) :
    TopPair.Hom.fst (cellPairMap X n a i) = cell X n a i := by
  apply TopCat.ext
  intro z
  change diskInclusion X n a
      (TopPair.Hom.fst (sigmaPairIso ι n).hom
        (TopPair.Hom.fst
          (TopPair.sigmaι
            (fun _ : ι => classicalCellDiskPair.{u} (n + 1)) i) z)) =
    cell X n a i z
  rw [sigmaPairIso_hom_fst_apply]
  rfl

/-- The subspace map of a component pair is its original attaching map. -/
theorem cellPairMap_snd (i : ι) :
    TopPair.Hom.snd (cellPairMap X n a i) = a i := by
  apply TopCat.ext
  intro z
  change attachingMap X n a
      (TopPair.Hom.snd (sigmaPairIso ι n).hom
        (TopPair.Hom.snd
          (TopPair.sigmaι
            (fun _ : ι => classicalCellDiskPair.{u} (n + 1)) i) z)) =
    a i z
  rw [sigmaPairIso_hom_snd_apply]
  rfl

/-- Relative homology of the actual attachment is the coproduct of the
relative homology groups of its literal component disk pairs. -/
noncomputable def attachmentRelativeHomologyCoproductIso
    (R : AddCommGrpCat.{u}) (k : ℕ) :
    (∐ fun _ : ι =>
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R k).obj
        (classicalCellDiskPair.{u} (n + 1))) ≅
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R k).obj
        (CellCollarDeformation.attachmentPair X n a) :=
  relativeSingularHomologySigmaIso
      (fun _ : ι => classicalCellDiskPair.{u} (n + 1)) R k ≪≫
    (relativeSingularHomologyFunctor AddCommGrpCat.{u} R k).mapIso
      (sigmaPairIso ι n) ≪≫
    literalToAttachmentRelativeHomologyIso X n a R k

/-- The coproduct comparison sends each component exactly through the
corresponding component pair map. -/
@[reassoc]
theorem relativeHomology_ι_comp_attachmentRelativeHomologyCoproductIso_hom
    (R : AddCommGrpCat.{u}) (k : ℕ) (i : ι) :
    Sigma.ι
          (fun _ : ι =>
            (relativeSingularHomologyFunctor AddCommGrpCat.{u} R k).obj
              (classicalCellDiskPair.{u} (n + 1))) i ≫
        (attachmentRelativeHomologyCoproductIso X n a R k).hom =
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R k).map
        (cellPairMap X n a i) := by
  rw [attachmentRelativeHomologyCoproductIso, Iso.trans_hom, Iso.trans_hom]
  rw [← Category.assoc,
    relativeSingularHomologySigmaIso_hom_ι]
  simp only [Functor.mapIso_hom,
    literalToAttachmentRelativeHomologyIso_hom, ← Functor.map_comp]
  simp only [cellPairMap]

/-- The inverse coproduct comparison returns the relative map of a component
to its exact coproduct injection. -/
@[reassoc]
theorem relativeHomology_map_cellPair_comp_attachmentRelativeHomologyCoproductIso_inv
    (R : AddCommGrpCat.{u}) (k : ℕ) (i : ι) :
    (relativeSingularHomologyFunctor AddCommGrpCat.{u} R k).map
          (cellPairMap X n a i) ≫
        (attachmentRelativeHomologyCoproductIso X n a R k).inv =
      Sigma.ι
        (fun _ : ι =>
          (relativeSingularHomologyFunctor AddCommGrpCat.{u} R k).obj
            (classicalCellDiskPair.{u} (n + 1))) i := by
  rw [← relativeHomology_ι_comp_attachmentRelativeHomologyCoproductIso_hom,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- In the cell dimension, actual relative homology is one coproduct copy of
the coefficient group for every attached cell. -/
noncomputable def attachmentRelativeDiagonalIso
    (R : AddCommGrpCat.{u}) :
    (∐ fun _ : ι => R) ≅
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R (n + 1)).obj
        (CellCollarDeformation.attachmentPair X n a) :=
  Limits.Sigma.mapIso (fun _ : ι =>
      classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u, u} R (n + 1)) ≪≫
    attachmentRelativeHomologyCoproductIso X n a R (n + 1)

/-- The relative class homomorphism of one actual attached cell. -/
noncomputable def attachmentRelativeCellHom
    (R : AddCommGrpCat.{u}) (i : ι) :
    R ⟶
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R (n + 1)).obj
        (CellCollarDeformation.attachmentPair X n a) :=
  Sigma.ι (fun _ : ι => R) i ≫
    (attachmentRelativeDiagonalIso X n a R).hom

/-- The diagonal coproduct coordinate restricts to the selected cell class. -/
@[reassoc]
theorem coefficient_ι_comp_attachmentRelativeDiagonalIso_hom
    (R : AddCommGrpCat.{u}) (i : ι) :
    Sigma.ι (fun _ : ι => R) i ≫
        (attachmentRelativeDiagonalIso X n a R).hom =
      attachmentRelativeCellHom X n a R i :=
  rfl

/-- Returning through the diagonal coordinate recovers the exact coproduct
injection of the selected cell. -/
@[reassoc]
theorem attachmentRelativeCellHom_comp_attachmentRelativeDiagonalIso_inv
    (R : AddCommGrpCat.{u}) (i : ι) :
    attachmentRelativeCellHom X n a R i ≫
        (attachmentRelativeDiagonalIso X n a R).inv =
      Sigma.ι (fun _ : ι => R) i := by
  unfold attachmentRelativeCellHom
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The selected cell class is the accepted disk-pair fundamental class
followed by the actual component pair map. -/
theorem attachmentRelativeCellHom_eq_diskPair
    (R : AddCommGrpCat.{u}) (i : ι) :
    attachmentRelativeCellHom X n a R i =
      (classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u, u}
          R (n + 1)).hom ≫
        (relativeSingularHomologyFunctor AddCommGrpCat.{u} R (n + 1)).map
          (cellPairMap X n a i) := by
  rw [← relativeHomology_ι_comp_attachmentRelativeHomologyCoproductIso_hom]
  simp [attachmentRelativeCellHom, attachmentRelativeDiagonalIso]

/-- Relative homology of the actual family attachment vanishes away from the
cell dimension. -/
theorem isZero_attachmentRelativeHomology_of_ne
    (R : AddCommGrpCat.{u}) (k : ℕ) (hk : k ≠ n + 1) :
    IsZero
      ((relativeSingularHomologyFunctor AddCommGrpCat.{u} R k).obj
        (CellCollarDeformation.attachmentPair X n a)) := by
  let F : Discrete ι ⥤ AddCommGrpCat.{u} :=
    Discrete.functor fun _ : ι =>
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R k).obj
        (classicalCellDiskPair.{u} (n + 1))
  have hF : IsZero F := Functor.isZero F fun _ =>
    isZero_relativeSingularHomology_classicalCellDiskPair_of_ne_of_univLE
      R (n + 1) k hk
  have hSigma : IsZero
      (∐ fun _ : ι =>
        (relativeSingularHomologyFunctor AddCommGrpCat.{u} R k).obj
          (classicalCellDiskPair.{u} (n + 1))) :=
    IsColimit.isZero_pt (colimit.isColimit F) hF
  exact hSigma.of_iso
    (attachmentRelativeHomologyCoproductIso X n a R k).symm

/-- Integer-graded relative homology of the actual family attachment vanishes
away from the cell dimension, including all negative degrees. -/
theorem isZero_attachmentRelativeHomologyInt_of_ne
    (R : AddCommGrpCat.{u}) (k : ℤ) (hk : k ≠ ((n + 1 : ℕ) : ℤ)) :
    IsZero
      ((relativeSingularHomologyIntFunctor AddCommGrpCat.{u} R k).obj
        (CellCollarDeformation.attachmentPair X n a)) := by
  by_cases hk0 : k < 0
  · exact isZero_relativeSingularHomologyIntFunctor_of_neg
      AddCommGrpCat.{u} R k hk0
        (CellCollarDeformation.attachmentPair X n a)
  · have hkNonneg : 0 ≤ k := le_of_not_gt hk0
    have hkNat : k.toNat ≠ n + 1 := by
      intro h
      apply hk
      rw [← Int.toNat_of_nonneg hkNonneg, h]
    have hNat := isZero_attachmentRelativeHomology_of_ne X n a R k.toNat hkNat
    have e :=
      (relativeSingularHomologyNatToIntIso AddCommGrpCat.{u} R k.toNat).app
        (CellCollarDeformation.attachmentPair X n a)
    have hkCast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hkNonneg
    rw [hkCast] at e
    exact hNat.of_iso e

end AlgebraicTopology.CellFamilyAttachment

end

end
