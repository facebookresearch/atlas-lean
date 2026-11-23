/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellRelativeHomology

/-!
# Clients for actual cell-family relative homology

These clients exercise independent topology and coefficient universes, the
empty family, a selected cell in a genuine indexed family, the pointwise
formula for the actual quotient projection, and the subgroup-indexed loop-cell
specialization.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.CWComplex

namespace AlgebraicTopology.CellFamilyRelativeHomologyTests

/-! ## Mixed topology and coefficient universes -/

/-- Off-diagonal reduced sphere homology accepts a universe-one sphere and
universe-two coefficients. -/
theorem mixedUniverseReducedSphereClient
    (R : AddCommGrpCat.{2}) (d k : ℕ) (hk : k ≠ d) :
    IsZero (reducedSingularHomology AddCommGrpCat.{2} R k
      (TopCat.sphere.{1} d)) :=
  isZero_reducedSphereHomology_of_ne_of_univLE R d k hk

/-- The integer disk coordinate retains the independent topology and
coefficient universes. -/
noncomputable def mixedUniverseDiskIntCoordinate
    (R : AddCommGrpCat.{2}) (d : ℕ) :
    R ≅
      (relativeSingularHomologyIntFunctor AddCommGrpCat.{2} R (d : ℤ)).obj
        (classicalCellDiskPair.{1} d) :=
  classicalCellDiskPairRelativeHomologyIntIso R d

/-- Returning the mixed-universe integer coordinate to natural grading gives
the accepted disk coordinate, rather than a second normalization. -/
theorem mixedUniverseDiskIntBridgeClient
    (R : AddCommGrpCat.{2}) (d : ℕ) :
    (mixedUniverseDiskIntCoordinate R d).hom ≫
        (relativeSingularHomologyNatToIntIso
          AddCommGrpCat.{2} R d).hom.app (classicalCellDiskPair.{1} d) =
      (classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{1, 2} R d).hom :=
  classicalCellDiskPairRelativeHomologyIntIso_hom_comp_natToInt R d

/-- The mixed-universe disk pair also vanishes in an arbitrary integer degree
away from its dimension. -/
theorem mixedUniverseDiskIntVanishingClient
    (R : AddCommGrpCat.{2}) (d : ℕ) (k : ℤ) (hk : k ≠ (d : ℤ)) :
    IsZero
      ((relativeSingularHomologyIntFunctor AddCommGrpCat.{2} R k).obj
        (classicalCellDiskPair.{1} d)) :=
  isZero_relativeSingularHomologyInt_classicalCellDiskPair_of_ne_of_univLE
    R d k hk

/-! ## The empty family -/

/-- A genuinely universe-one empty cell index. -/
abbrev EmptyCells : Type 1 := ULift.{1} (Fin 0)

/-- The unique attaching family indexed by `EmptyCells`. -/
def emptyAttachingMaps (X : TopCat.{1}) (n : ℕ)
    (i : EmptyCells) : (classicalCellDiskPair.{1} (n + 1)).snd ⟶ X :=
  Fin.elim0 i.down

/-- With no cells, the relative homology of the actual attachment pair
vanishes in every natural degree, including the nominal cell degree. -/
theorem emptyFamilyEveryRelativeDegreeVanishes
    (X : TopCat.{1}) (R : AddCommGrpCat.{1}) (n k : ℕ) :
    IsZero
      ((relativeSingularHomologyFunctor AddCommGrpCat.{1} R k).obj
        (CellCollarDeformation.attachmentPair X n
          (emptyAttachingMaps X n))) := by
  by_cases hk : k = n + 1
  · subst k
    let F : Discrete EmptyCells ⥤ AddCommGrpCat.{1} :=
      Discrete.functor fun _ : EmptyCells => R
    have hF : IsZero F :=
      Functor.isZero F fun i => Fin.elim0 i.as.down
    have hSource : IsZero (∐ fun _ : EmptyCells => R) :=
      IsColimit.isZero_pt (colimit.isColimit F) hF
    exact hSource.of_iso
      (CellFamilyAttachment.attachmentRelativeDiagonalIso
        X n (emptyAttachingMaps X n) R).symm
  · exact CellFamilyAttachment.isZero_attachmentRelativeHomology_of_ne
      X n (emptyAttachingMaps X n) R k hk

/-! ## A selected cell and the actual quotient map -/

universe u

variable {ι : Type u} (X : TopCat.{u}) (n : ℕ)
variable (a : ι → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X))
variable (R : AddCommGrpCat.{u})

/-- A selected characteristic disk returns to its exact coproduct summand,
both through the family generator and through the classical disk coordinate. -/
theorem selectedCellCoproductRoundTripClient (i : ι) :
    CellFamilyAttachment.attachmentRelativeCellHom X n a R i ≫
          (CellFamilyAttachment.attachmentRelativeDiagonalIso X n a R).inv =
        Sigma.ι (fun _ : ι => R) i ∧
      ((classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u, u}
            R (n + 1)).hom ≫
          (relativeSingularHomologyFunctor AddCommGrpCat.{u} R (n + 1)).map
            (CellFamilyAttachment.cellPairMap X n a i)) ≫
          (CellFamilyAttachment.attachmentRelativeDiagonalIso X n a R).inv =
        Sigma.ι (fun _ : ι => R) i := by
  have hRoundTrip :=
    CellFamilyAttachment.attachmentRelativeCellHom_comp_attachmentRelativeDiagonalIso_inv
      X n a R i
  refine ⟨hRoundTrip, ?_⟩
  rw [← CellFamilyAttachment.attachmentRelativeCellHom_eq_diskPair X n a R i]
  exact hRoundTrip

local notation "forgetToArrow" => MorphismProperty.Arrow.forget _ _ _

/-- The quotient isomorphism's projection formula holds pointwise on an
actual member of the literal disk family. -/
theorem quotientProjectionPointClient
    (z : CellFamilyAttachment.disks ι n) :
    (ConcreteCategory.hom
      (TopCat.pointQuotientProjection.app
          ((forgetToArrow).obj (CellFamilyAttachment.literalPair ι n)) ≫
        (CellFamilyAttachment.attachmentPointQuotientIso X n a).hom.right)) z =
      (ConcreteCategory.hom
        (CellFamilyAttachment.diskInclusion X n a ≫
          TopCat.pointQuotientProjection.app
            ((forgetToArrow).obj
              (CellCollarDeformation.attachmentPair X n a)))) z := by
  exact ConcreteCategory.congr_hom
    (CellFamilyAttachment.pointQuotientProjection_comp_attachmentPointQuotientIso_hom
      X n a) z

/-! ## The original subgroup-indexed two-cell family -/

variable (x : X) (P : Subgroup (FundamentalGroup X x))

/-- A chosen original subgroup element gives its actual relative generator;
the same specialization simultaneously exposes the degree-three vanishing and
the degree-two/degree-one mono/epi consequences. -/
theorem loopCellSelectedGeneratorAndAdjacentDegreesClient (p : P) :
    LoopCellAttachment.relativeGenerator X x P R p ≫
          (LoopCellAttachment.relativeHomologyTwoIso X x P R).inv =
        Sigma.ι (fun _ : P => R) p ∧
      IsZero
        ((relativeSingularHomologyFunctor AddCommGrpCat.{u} R 3).obj
          (LoopCellAttachment.relativePair X x P)) ∧
      Mono (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj R).map
        (LoopCellAttachment.inclusion X x P)) ∧
      Epi (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj R).map
        (LoopCellAttachment.inclusion X x P)) := by
  refine ⟨?_, LoopCellAttachment.isZero_relativeHomology_three X x P R,
    LoopCellAttachment.mono_inclusionHomologyMap_two X x P R,
    LoopCellAttachment.epi_inclusionHomologyMap_one X x P R⟩
  exact
    CellFamilyAttachment.attachmentRelativeCellHom_comp_attachmentRelativeDiagonalIso_inv
      X 1 (LoopCellAttachment.attachingMap X x P) R p

end AlgebraicTopology.CellFamilyRelativeHomologyTests

end
