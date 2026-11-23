/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CellFamilyRelativeExact
public import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellAttachment

/-!
# Relative homology of the actual loop-cell attachment

The two-cell attachment indexed by the original subgroup has relative
degree-two homology equal to one coproduct copy of the coefficient group for
every original subgroup element.  Its indexed classes are induced by the
actual characteristic disks.  Relative degree three vanishes, so the original
inclusion is monic in degree two and epic in degree one.

No connectedness, normality, perfectness, spherical representative, or
plus-construction hypothesis is used here.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology.CWComplex

universe u

namespace AlgebraicTopology.LoopCellAttachment

variable (X : TopCat.{u}) (x : X)
variable (P : Subgroup (FundamentalGroup X x))

/-- The concrete pair of the two-cell attachment and the original space. -/
abbrev relativePair : TopPair.{u} :=
  CellCollarDeformation.attachmentPair X 1 (attachingMap X x P)

/-- The pair map of the original `p`-indexed characteristic disk. -/
def cellPairMap (p : P) : classicalCellDiskPair.{u} 2 ⟶ relativePair X x P :=
  CellFamilyAttachment.cellPairMap X 1 (attachingMap X x P) p

@[simp]
theorem cellPairMap_fst (p : P) :
    TopPair.Hom.fst (cellPairMap X x P p) = cell X x P p := by
  apply TopCat.ext
  intro z
  change CellFamilyAttachment.diskInclusion X 1 (attachingMap X x P)
      (TopPair.Hom.fst (CellFamilyAttachment.sigmaPairIso P 1).hom
        (TopPair.Hom.fst
          (TopPair.sigmaι
            (fun _ : P => classicalCellDiskPair.{u} 2) p) z)) =
    CellFamilyAttachment.diskInclusion X 1 (attachingMap X x P) ⟨p, z⟩
  rw [CellFamilyAttachment.sigmaPairIso_hom_fst_apply]

@[simp]
theorem cellPairMap_snd (p : P) :
    TopPair.Hom.snd (cellPairMap X x P p) = attachingMap X x P p := by
  apply TopCat.ext
  intro z
  change CellFamilyAttachment.attachingMap X 1 (attachingMap X x P)
      (TopPair.Hom.snd (CellFamilyAttachment.sigmaPairIso P 1).hom
        (TopPair.Hom.snd
          (TopPair.sigmaι
            (fun _ : P => classicalCellDiskPair.{u} 2) p) z)) =
    attachingMap X x P p z
  rw [CellFamilyAttachment.sigmaPairIso_hom_snd_apply]
  rfl

variable (R : AddCommGrpCat.{u})

/-- Relative degree-two homology of the actual loop-cell attachment is the
coproduct of one coefficient object for every original subgroup element. -/
noncomputable def relativeHomologyTwoIso :
    (∐ fun _ : P => R) ≅
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2).obj
        (relativePair X x P) :=
  CellFamilyAttachment.attachmentRelativeDiagonalIso
    X 1 (attachingMap X x P) R

/-- The relative degree-two generator belonging to the original element `p`. -/
noncomputable def relativeGenerator (p : P) :
    R ⟶ (relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2).obj
      (relativePair X x P) :=
  CellFamilyAttachment.attachmentRelativeCellHom
    X 1 (attachingMap X x P) R p

/-- The `p`th generator is the classical disk generator followed by the
relative map induced by the original characteristic disk. -/
theorem relativeGenerator_eq_characteristic (p : P) :
    relativeGenerator X x P R p =
      (classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u} R 2).hom ≫
        (relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2).map
          (cellPairMap X x P p) :=
  CellFamilyAttachment.attachmentRelativeCellHom_eq_diskPair
    X 1 (attachingMap X x P) R p

/-- The indexed relative generators assemble to the complete coordinate. -/
theorem relativeGenerator_desc :
    Sigma.desc (fun p => relativeGenerator X x P R p) =
      (relativeHomologyTwoIso X x P R).hom := by
  apply Limits.Sigma.hom_ext
  intro p
  rw [Limits.Sigma.ι_comp_desc]
  exact CellFamilyAttachment.coefficient_ι_comp_attachmentRelativeDiagonalIso_hom
    X 1 (attachingMap X x P) R p

/-- Maps out of relative degree-two homology are determined by the original
subgroup-indexed generators. -/
theorem relativeHomologyTwo_hom_ext
    {A : AddCommGrpCat.{u}}
    {f g : (relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2).obj
        (relativePair X x P) ⟶ A}
    (h : ∀ p, relativeGenerator X x P R p ≫ f =
      relativeGenerator X x P R p ≫ g) : f = g := by
  apply (cancel_epi (relativeHomologyTwoIso X x P R).hom).mp
  apply Limits.Sigma.hom_ext
  intro p
  change
    (Sigma.ι (fun _ : P => R) p ≫
        (CellFamilyAttachment.attachmentRelativeDiagonalIso
          X 1 (attachingMap X x P) R).hom) ≫ f =
      (Sigma.ι (fun _ : P => R) p ≫
        (CellFamilyAttachment.attachmentRelativeDiagonalIso
          X 1 (attachingMap X x P) R).hom) ≫ g
  rw [CellFamilyAttachment.coefficient_ι_comp_attachmentRelativeDiagonalIso_hom]
  exact h p

/-- Relative degree-three homology of the actual two-cell attachment vanishes. -/
theorem isZero_relativeHomology_three :
    IsZero ((relativeSingularHomologyFunctor AddCommGrpCat.{u} R 3).obj
      (relativePair X x P)) := by
  exact CellFamilyAttachment.isZero_attachmentRelativeHomology_of_ne
    X 1 (attachingMap X x P) R 3 (by omega)

/-- The original inclusion is monic on degree-two homology. -/
theorem mono_inclusionHomologyMap_two :
    Mono (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj R).map
      (inclusion X x P)) :=
  CellFamilyAttachment.mono_attachmentSubspaceMap_top
    X 1 (attachingMap X x P) R

/-- The original inclusion is epic on degree-one homology. -/
theorem epi_inclusionHomologyMap_one :
    Epi (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj R).map
      (inclusion X x P)) :=
  CellFamilyAttachment.epi_attachmentSubspaceMap_pred
    X 1 (attachingMap X x P) R

end AlgebraicTopology.LoopCellAttachment

end
