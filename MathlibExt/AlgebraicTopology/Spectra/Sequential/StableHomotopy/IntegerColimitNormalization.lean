/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.IntegerStablePi

/-!
# The original diagonal colimits in their canonical integer degree

Every starting level and positive homotopy index uses the same original
diagonal and filtered group quotient. The actual structure comparison and
genuine successor cofinality give both maps for every finite offset.
The degree and level transports then identify each diagonal colimit with
the one original integer stable homotopy functor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.IntegerColimitNormalization

open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalStructureGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.PositiveStructureGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open GrpCat.FilteredColimits.Successor

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The full original diagonal followed by its actual filtered group quotient. -/
abbrev diagonalColimitFunctor (m k : ℕ) : SequentialSpectrum.{u, v} ⥤ GrpCat.{v} :=
  diagonalDiagramFunctor m k ⋙ GrpCat.FilteredColimits.colimitFunctor

/-- Every full input map is the same original map of filtered group quotients. -/
theorem diagonalColimitFunctor_map (m k : ℕ)
    {X Y : SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (diagonalColimitFunctor m k).map f =
      GrpCat.FilteredColimits.colimitMap ((diagonalDiagramFunctor m k).map f) := rfl

/-- Every leg is the actual original filtered group quotient leg. -/
def diagonalLeg (m k : ℕ) (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    ((diagonalDiagramFunctor m k).obj X).obj n ⟶ (diagonalColimitFunctor m k).obj X :=
  (GrpCat.FilteredColimits.colimitCocone ((diagonalDiagramFunctor m k).obj X)).ι.app n

/-- Its entire function is the original quotient representative function. -/
theorem diagonalLeg_apply (m k : ℕ) (X : SequentialSpectrum.{u, v}) (n : ℕ)
    (a : ((diagonalDiagramFunctor m k).obj X).obj n) :
    (diagonalLeg m k X n).hom a =
      GrpCat.FilteredColimits.G.mk ((diagonalDiagramFunctor m k).obj X) ⟨n, a⟩ := rfl

/-- The original structure map and actual successor cofinality give the full natural Iso. -/
def successorNatIso (m k : ℕ) :
    diagonalColimitFunctor.{u, v} m k ≅ diagonalColimitFunctor (m + 1) (k + 1) :=
  NatIso.ofComponents (fun X => diagonalStructureColimitIso m k X) (fun f => by
    rw [diagonalStructureColimitIso_hom, diagonalStructureColimitIso_hom]
    exact (diagonalColimitStructureNatTrans m k).naturality f)

/-- Its forward function is the same actual original structure map of group quotients. -/
theorem successorNatIso_hom (m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (successorNatIso m k).hom.app X =
      GrpCat.FilteredColimits.colimitMap ((diagonalStructureNatTrans m k).app X) :=
  diagonalStructureColimitIso_hom m k X

/-- Its inverse retains the full original index comparison and successor quotient comparison. -/
theorem successorNatIso_inv (m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (successorNatIso m k).inv.app X =
      GrpCat.FilteredColimits.colimitMap ((diagonalSuccessorIndexNatIso m k).hom.app X) ≫
        (successorComparisonIso ((diagonalDiagramFunctor m k).obj X)).hom := rfl

/-- Every forward successor leg retains the actual original structure map. -/
theorem successorNatIso_hom_leg (m k : ℕ) (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    diagonalLeg m k X n ≫ (successorNatIso m k).hom.app X =
      ((diagonalStructureNatTrans m k).app X).app n ≫
        diagonalLeg (m + 1) (k + 1) X n := by
  rw [successorNatIso_hom]
  exact GrpCat.FilteredColimits.colimitMap_ι ((diagonalStructureNatTrans m k).app X) n

/-- Every inverse successor leg retains the actual index map and original next quotient leg. -/
theorem successorNatIso_inv_leg (m k : ℕ) (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    diagonalLeg (m + 1) (k + 1) X n ≫ (successorNatIso m k).inv.app X =
      ((diagonalSuccessorIndexNatIso m k).hom.app X).app n ≫
        diagonalLeg m k X (n + 1) := by
  dsimp only [diagonalLeg]
  rw [successorNatIso_inv, ← Category.assoc,
    GrpCat.FilteredColimits.colimitMap_ι, Category.assoc]
  exact congrArg (fun f => ((diagonalSuccessorIndexNatIso m k).hom.app X).app n ≫ f)
    (successorComparisonIso_hom_ι ((diagonalDiagramFunctor m k).obj X) n)

/-- Every offset uses the actual original successor comparison repeatedly. -/
def offsetNatIso (m k : ℕ) : ∀ r : ℕ,
    diagonalColimitFunctor.{u, v} m k ≅ diagonalColimitFunctor (m + r) (k + r) :=
  Nat.rec
    (motive := fun r => diagonalColimitFunctor.{u, v} m k ≅
      diagonalColimitFunctor (m + r) (k + r))
    (Iso.refl _) (fun r previous => previous ≪≫ successorNatIso (m + r) (k + r))

/-- Both original zero-offset group-colimit maps are the identity. -/
theorem offsetNatIsoZero (m k : ℕ) : offsetNatIso.{u, v} m k 0 = Iso.refl _ := rfl

/-- Both complete successor-offset maps retain the original successor comparison. -/
theorem offsetNatIsoSucc (m k r : ℕ) :
    offsetNatIso.{u, v} m k (r + 1) =
      offsetNatIso m k r ≪≫ successorNatIso (m + r) (k + r) := rfl

private def offsetCastNatIso (a b c d r : ℕ) (hLevel : a + r = c) (hIndex : b + r = d) :
    diagonalColimitFunctor.{u, v} c d ≅ diagonalColimitFunctor a b :=
  Functor.isoWhiskerRight
      (eqToIso (congrArg₂ diagonalDiagramFunctor hLevel.symm hIndex.symm))
      GrpCat.FilteredColimits.colimitFunctor ≪≫ (offsetNatIso a b r).symm

private theorem offsetCastNatIso_of_zero (a b c d r : ℕ)
    (hLevel : a + r = c) (hIndex : b + r = d) (hr : r = 0) :
    offsetCastNatIso.{u, v} a b c d r hLevel hIndex =
      eqToIso (congrArg₂ diagonalColimitFunctor
        (hLevel.symm.trans ((congrArg (fun s => a + s) hr).trans (Nat.add_zero a)))
        (hIndex.symm.trans ((congrArg (fun s => b + s) hr).trans (Nat.add_zero b)))) := by
  subst r
  simp only [Nat.add_zero] at hLevel hIndex
  subst c
  subst d
  simp only [offsetCastNatIso, offsetNatIso, eqToIso_refl,
    Functor.isoWhiskerRight_refl]
  exact Iso.trans_refl _

/-- The whole diagram map of an offset uses the same original structure maps. -/
def offsetDiagramNatTrans (m k : ℕ) : ∀ r : ℕ,
    diagonalDiagramFunctor.{u, v} m k ⟶ diagonalDiagramFunctor (m + r) (k + r) :=
  Nat.rec
    (motive := fun r => diagonalDiagramFunctor.{u, v} m k ⟶
      diagonalDiagramFunctor (m + r) (k + r))
    (𝟙 _) (fun r previous => previous ≫ diagonalStructureNatTrans (m + r) (k + r))

/-- The whole zero-offset original diagonal map is the identity transformation. -/
theorem offsetDiagramNatTransZero (m k : ℕ) :
    offsetDiagramNatTrans.{u, v} m k 0 = 𝟙 _ := rfl

/-- The whole successor-offset map retains the original diagonal structure transformation. -/
theorem offsetDiagramNatTransSucc (m k r : ℕ) :
    offsetDiagramNatTrans.{u, v} m k (r + 1) =
      offsetDiagramNatTrans m k r ≫ diagonalStructureNatTrans (m + r) (k + r) := rfl

/-- The complete forward offset function is the original induced map on group quotients. -/
theorem offsetNatIso_hom (m k r : ℕ) (X : SequentialSpectrum.{u, v}) :
    (offsetNatIso m k r).hom.app X =
      GrpCat.FilteredColimits.colimitMap ((offsetDiagramNatTrans m k r).app X) := by
  induction r with
  | zero =>
    exact (GrpCat.FilteredColimits.colimitMap_id _).symm
  | succ r ih =>
    change (offsetNatIso m k r).hom.app X ≫
        (successorNatIso (m + r) (k + r)).hom.app X = _
    rw [ih, successorNatIso_hom]
    exact (GrpCat.FilteredColimits.colimitFunctor.map_comp
      ((offsetDiagramNatTrans m k r).app X)
      ((diagonalStructureNatTrans (m + r) (k + r)).app X)).symm

/-- The full inverse offset function retains the entire original comparison word. -/
theorem offsetNatIso_inv_succ (m k r : ℕ) (X : SequentialSpectrum.{u, v}) :
    (offsetNatIso m k (r + 1)).inv.app X =
      GrpCat.FilteredColimits.colimitMap
          ((diagonalSuccessorIndexNatIso (m + r) (k + r)).hom.app X) ≫
        (successorComparisonIso ((diagonalDiagramFunctor (m + r) (k + r)).obj X)).hom ≫
          (offsetNatIso m k r).inv.app X := by
  change (successorNatIso (m + r) (k + r)).inv.app X ≫ _ = _
  rw [successorNatIso_inv]
  exact Category.assoc _ _ _

/-- Every forward offset leg uses the complete original iterated structure function. -/
theorem offsetNatIso_hom_leg (m k r : ℕ) (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    diagonalLeg m k X n ≫ (offsetNatIso m k r).hom.app X =
      ((offsetDiagramNatTrans m k r).app X).app n ≫
        diagonalLeg (m + r) (k + r) X n := by
  rw [offsetNatIso_hom]
  exact GrpCat.FilteredColimits.colimitMap_ι ((offsetDiagramNatTrans m k r).app X) n

/-- Every inverse offset leg retains each original index map and the next original leg. -/
theorem offsetNatIso_inv_leg_succ (m k r : ℕ) (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    diagonalLeg (m + (r + 1)) (k + (r + 1)) X n ≫
        (offsetNatIso m k (r + 1)).inv.app X =
      ((diagonalSuccessorIndexNatIso (m + r) (k + r)).hom.app X).app n ≫
        (diagonalLeg (m + r) (k + r) X (n + 1) ≫ (offsetNatIso m k r).inv.app X) := by
  change diagonalLeg ((m + r) + 1) ((k + r) + 1) X n ≫
    ((successorNatIso (m + r) (k + r)).inv.app X ≫
      (offsetNatIso m k r).inv.app X) = _
  rw [← Category.assoc, successorNatIso_inv_leg, Category.assoc]

/-- The actual integer homotopy degree of the original starting level and positive index. -/
def integerDegree (m k : ℕ) : ℤ := ((k + 1 : ℕ) : ℤ) - (m : ℤ)

/-- The offset is the original starting level minus the canonical starting level. -/
def normalizationOffset (m k : ℕ) : ℕ := m - integerTailLevel (integerDegree m k)

/-- Every original level is its actual canonical level plus the full finite offset. -/
theorem canonicalLevel_add_offset (m k : ℕ) :
    integerTailLevel (integerDegree m k) + normalizationOffset m k = m := by
  simp only [integerTailLevel, integerDegree, normalizationOffset]
  omega

/-- Every original positive index has the same full canonical finite offset. -/
theorem canonicalPositiveIndex_add_offset (m k : ℕ) :
    integerTailPositiveIndex (integerDegree m k) + normalizationOffset m k = k := by
  simp only [integerTailLevel, integerTailPositiveIndex, integerDegree, normalizationOffset]
  omega

/-- The complete original diagonal transports its actual degree and level indexes. -/
def normalizationDiagramIso (m k : ℕ) : diagonalDiagramFunctor.{u, v} m k ≅
    diagonalDiagramFunctor
      (integerTailLevel (integerDegree m k) + normalizationOffset m k)
      (integerTailPositiveIndex (integerDegree m k) + normalizationOffset m k) :=
  eqToIso (congrArg₂ diagonalDiagramFunctor
    (canonicalLevel_add_offset m k).symm (canonicalPositiveIndex_add_offset m k).symm)

/-- Every original diagonal colimit has both maps to the one original integer functor. -/
def integerColimitNatIso (m k : ℕ) : diagonalColimitFunctor.{u, v} m k ≅
    integerStablePiFunctor (integerDegree m k) :=
  offsetCastNatIso (integerTailLevel (integerDegree m k))
    (integerTailPositiveIndex (integerDegree m k)) m k (normalizationOffset m k)
    (canonicalLevel_add_offset m k) (canonicalPositiveIndex_add_offset m k)

/-- Its full forward quotient function retains both original index transports and offset maps. -/
theorem integerColimitNatIso_hom (m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (integerColimitNatIso m k).hom.app X =
      GrpCat.FilteredColimits.colimitMap ((normalizationDiagramIso m k).hom.app X) ≫
        (offsetNatIso (integerTailLevel (integerDegree m k))
          (integerTailPositiveIndex (integerDegree m k)) (normalizationOffset m k)).inv.app X :=
  rfl

/-- Its full inverse quotient function retains every original structure and index transport. -/
theorem integerColimitNatIso_inv (m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (integerColimitNatIso m k).inv.app X =
      GrpCat.FilteredColimits.colimitMap
          ((offsetDiagramNatTrans (integerTailLevel (integerDegree m k))
            (integerTailPositiveIndex (integerDegree m k)) (normalizationOffset m k)).app X) ≫
        GrpCat.FilteredColimits.colimitMap ((normalizationDiagramIso m k).inv.app X) := by
  change (offsetNatIso (integerTailLevel (integerDegree m k))
      (integerTailPositiveIndex (integerDegree m k)) (normalizationOffset m k)).hom.app X ≫
    GrpCat.FilteredColimits.colimitMap ((normalizationDiagramIso m k).inv.app X) = _
  rw [offsetNatIso_hom]

/-- Every forward normalization leg retains the actual degree/level casts and inverse offset leg. -/
theorem integerColimitNatIso_hom_leg (m k : ℕ) (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    diagonalLeg m k X n ≫ (integerColimitNatIso m k).hom.app X =
      ((normalizationDiagramIso m k).hom.app X).app n ≫
        (diagonalLeg
          (integerTailLevel (integerDegree m k) + normalizationOffset m k)
          (integerTailPositiveIndex (integerDegree m k) + normalizationOffset m k) X n ≫
            (offsetNatIso (integerTailLevel (integerDegree m k))
              (integerTailPositiveIndex (integerDegree m k))
              (normalizationOffset m k)).inv.app X) := by
  dsimp only [diagonalLeg]
  rw [integerColimitNatIso_hom, ← Category.assoc,
    GrpCat.FilteredColimits.colimitMap_ι, Category.assoc]

/-- Every inverse normalization leg is the original structure word and unchanged quotient leg. -/
theorem integerColimitNatIso_inv_leg (m k : ℕ) (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    integerStablePiLeg (integerDegree m k) X n ≫ (integerColimitNatIso m k).inv.app X =
      ((offsetDiagramNatTrans (integerTailLevel (integerDegree m k))
        (integerTailPositiveIndex (integerDegree m k))
        (normalizationOffset m k)).app X).app n ≫
      ((normalizationDiagramIso m k).inv.app X).app n ≫ diagonalLeg m k X n := by
  dsimp only [integerStablePiLeg, diagonalLeg]
  rw [integerColimitNatIso_inv, ← Category.assoc,
    GrpCat.FilteredColimits.colimitMap_ι, Category.assoc,
    GrpCat.FilteredColimits.colimitMap_ι]

/-- Both original source maps commute with the whole forward integer quotient function. -/
theorem integerColimitNatIso_hom_naturality (m k : ℕ)
    {X Y : SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    GrpCat.FilteredColimits.colimitMap ((diagonalDiagramFunctor m k).map f) ≫
        (integerColimitNatIso m k).hom.app Y =
      (integerColimitNatIso m k).hom.app X ≫
        (integerStablePiFunctor (integerDegree m k)).map f :=
  (integerColimitNatIso m k).hom.naturality f

/-- Both original source maps commute with the entire inverse integer quotient function. -/
theorem integerColimitNatIso_inv_naturality (m k : ℕ)
    {X Y : SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (integerStablePiFunctor (integerDegree m k)).map f ≫
        (integerColimitNatIso m k).inv.app Y =
      (integerColimitNatIso m k).inv.app X ≫
        GrpCat.FilteredColimits.colimitMap ((diagonalDiagramFunctor m k).map f) :=
  (integerColimitNatIso m k).inv.naturality f

/-- Every complete original source Arrow has its actual integer quotient Arrow Iso. -/
def integerMapArrowIso (m k : ℕ)
    {X Y : SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    Arrow.mk ((diagonalColimitFunctor m k).map f) ≅
      Arrow.mk ((integerStablePiFunctor (integerDegree m k)).map f) :=
  Arrow.isoMk ((integerColimitNatIso m k).app X) ((integerColimitNatIso m k).app Y)
    ((integerColimitNatIso m k).hom.naturality f).symm

/-- The actual canonical starting indexes retain their literal original integer degree. -/
theorem integerDegree_canonical (q : ℤ) :
    integerDegree (integerTailLevel q) (integerTailPositiveIndex q) = q := by
  simpa only [integerDegree, Nat.add_zero] using integerTail_degree q 0

/-- The original canonical diagonal has zero normalization offset. -/
theorem normalizationOffset_canonical (q : ℤ) :
    normalizationOffset (integerTailLevel q) (integerTailPositiveIndex q) = 0 := by
  simp only [normalizationOffset, integerDegree_canonical, Nat.sub_self]

/-- Canonical normalization compares the literal same one original integer functor. -/
def canonicalNatIso (q : ℤ) : integerStablePiFunctor.{u, v} q ≅ integerStablePiFunctor q :=
  integerColimitNatIso (integerTailLevel q) (integerTailPositiveIndex q) ≪≫
    eqToIso (congrArg integerStablePiFunctor (integerDegree_canonical q))

/-- Both quotient functions of the literal canonical case are the original identity maps. -/
theorem canonicalNatIso_refl (q : ℤ) : canonicalNatIso.{u, v} q = Iso.refl _ := by
  have hZero := offsetCastNatIso_of_zero.{u, v}
    (integerTailLevel (integerDegree (integerTailLevel q) (integerTailPositiveIndex q)))
    (integerTailPositiveIndex (integerDegree (integerTailLevel q) (integerTailPositiveIndex q)))
    (integerTailLevel q) (integerTailPositiveIndex q)
    (normalizationOffset (integerTailLevel q) (integerTailPositiveIndex q))
    (canonicalLevel_add_offset (integerTailLevel q) (integerTailPositiveIndex q))
    (canonicalPositiveIndex_add_offset (integerTailLevel q) (integerTailPositiveIndex q))
    (normalizationOffset_canonical q)
  have h := congrArg (fun e => e ≪≫
    eqToIso (congrArg integerStablePiFunctor (integerDegree_canonical q))) hZero
  exact h.trans ((eqToIso_trans _ _).trans (eqToIso_refl _))

end PointedCGWH.SequentialSpectrum.StableHomotopy.IntegerColimitNormalization
