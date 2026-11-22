/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
See NOTICE in the repository root for the original attribution.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.ConditionalFiberSequence

/-!
# Conditional full Hom sequence of every individual orthogonal fiber cone

Each caller supplies its actual cone and limit witness independently.
The original point-set limit comparison identifies its entire Hom terms
with the canonical fiber terms. Its original first projection remains
the sequence restriction, and both projection equations determine all
source and caller choice maps.

The full integer sequence has all three pointed Hom exactness positions.
For every family of caller cones its forward function is the same actual
original comparison test. The only pending premise is Hom bijectivity
of that original suspended-fiber comparison; no Omega endpoint or model
assumption is added.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.ConditionalChosenFiberSequence

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.FiberGeometry
open PointedCGWH.Spectra.Orthogonal.IntegerTargetTests
open PointedCGWH.Spectra.Orthogonal.NegativeHomTests
open PointedCGWH.Spectra.Orthogonal.ChosenFiberHomTests
open PointedCGWH.Spectra.Orthogonal.ChosenFiberBoundaryTests
open PointedCGWH.Spectra.Orthogonal.FiberInclusionImage
open PointedCGWH.Spectra.Orthogonal.ConditionalFiberHom

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev C := OrthogonalCarrier.{u, v}
private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev canonicalChoices := fun F : Arrow C.{u, v} => fiberCone F.hom
private abbrev canonicalLimits := fun F : Arrow C.{u, v} => fiberConeIsLimit F.hom

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev H := toHomotopyCategory C.{u, v}
private abbrev CQ := NativeK.CofiberNullity.cofiberQ (B := B) (I := O.{u, v})

namespace General

variable {P : ObjectProperty (Arrow C.{u, v})}
  (hP : P ≤ ChosenFiberHomTests.fibrantFibrationProperty.{u, v} (B := B))

open PointedCGWH.Spectra.Orthogonal.ChosenFiberHomTests.General
open PointedCGWH.Spectra.Orthogonal.ChosenFiberBoundaryTests.General
open PointedCGWH.Spectra.Orthogonal.FiberInclusionImage.General
open PointedCGWH.Spectra.Orthogonal.ConditionalFiberHom.General
open PointedCGWH.Spectra.Orthogonal.ConditionalFiberSequence.General

/-- The full Hom term of the caller's individual fiber cone keeps its actual carrier. -/
abbrev chosenHom (q : ℤ) (F : P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (E : C.{u, v}) :=
  H.obj c.pt ⟶ H.obj ((integerTarget q).obj E)

/-- The original point-set limit comparison gives both whole Hom functions. -/
def toCanonicalHom (q : ℤ) (F : P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) : chosenHom q F c E ≃ ChosenFiberHomTests.General.fiberHom canonicalChoices q F E :=
  Iso.homCongr (H.mapIso (chosenFiberIso F.obj.hom c hc)) (Iso.refl _)

/-- The whole forward function uses the actual inverse point-set limit comparison. -/
theorem toCanonicalHom_apply (q : ℤ) (F : P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (g : chosenHom q F c E) :
    toCanonicalHom q F c hc E g = H.map (chosenFiberIso F.obj.hom c hc).inv ≫ g := by
  simp only [toCanonicalHom, Iso.homCongr_apply, Functor.mapIso_inv,
    Iso.refl_hom, Category.comp_id]

/-- Its same full inverse uses the original forward point-set limit comparison. -/
theorem toCanonicalHom_symm_apply (q : ℤ) (F : P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (g : ChosenFiberHomTests.General.fiberHom canonicalChoices q F E) :
    (toCanonicalHom q F c hc E).symm g = H.map (chosenFiberIso F.obj.hom c hc).hom ≫ g := by
  simp only [toCanonicalHom, Iso.homCongr_symm, Iso.homCongr_apply,
    Iso.symm_inv, Iso.symm_hom, Functor.mapIso_hom, Iso.refl_inv, Category.comp_id]

omit B in
/-- The original full chosen-fiber source or self-comparison law on the shared Arrow subcategory. -/
theorem canonicalMap {F G : P.FullSubcategory} (f : F ⟶ G) :
    chosenFiberMap f.hom (canonicalChoices F.obj) (canonicalChoices G.obj)
        (canonicalLimits G.obj) = fiberFunctor.map f.hom := by
  apply pullback.hom_ext
  · exact (chosenFiberMap_fst f.hom _ _ _).trans (fiberMap_fst f.hom).symm
  · exact (chosenFiberMap_snd f.hom _ _ _).trans (fiberMap_snd f.hom).symm

omit B in
/-- The original full chosen-fiber source or self-comparison law on the shared Arrow subcategory. -/
theorem comparison_inv_source {F G : P.FullSubcategory} (f : F ⟶ G)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (d : PullbackCone G.obj.hom (Diagrams.zeroTo G.obj.right)) (hd : IsLimit d) :
    fiberFunctor.map f.hom ≫ (chosenFiberIso G.obj.hom d hd).inv =
      (chosenFiberIso F.obj.hom c hc).inv ≫ chosenFiberMap f.hom c d hd := by
  apply (cancel_epi (chosenFiberIso F.obj.hom c hc).hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc,
    ← chosenFiberIso_naturality f.hom c hc d hd, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- Every full original source Arrow square keeps both individually
supplied caller cones and their actual original fiber map. -/
theorem toCanonicalHom_source (q : ℤ) {F G : P.FullSubcategory} (f : F ⟶ G)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (d : PullbackCone G.obj.hom (Diagrams.zeroTo G.obj.right)) (hd : IsLimit d)
    (E : C.{u, v}) (g : chosenHom q G d E) :
    toCanonicalHom q F c hc E (H.map (chosenFiberMap f.hom c d hd) ≫ g) =
      ChosenFiberHomTests.General.fiberSource canonicalChoices canonicalLimits q f E (toCanonicalHom q G d hd E g) := by
  have h := H.congr_map (comparison_inv_source f c hc d hd)
  simp only [Functor.map_comp] at h
  rw [toCanonicalHom_apply, toCanonicalHom_apply]
  change H.map (chosenFiberIso F.obj.hom c hc).inv ≫
      (H.map (chosenFiberMap f.hom c d hd) ≫ g) =
    H.map (chosenFiberMap f.hom (canonicalChoices F.obj) (canonicalChoices G.obj)
      (canonicalLimits G.obj)) ≫ (H.map (chosenFiberIso G.obj.hom d hd).inv ≫ g)
  rw [canonicalMap, ← Category.assoc, ← h, Category.assoc]

/-- The same inverse retains both actual caller cones in every complete source square. -/
theorem toCanonicalHom_symm_source (q : ℤ) {F G : P.FullSubcategory} (f : F ⟶ G)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (d : PullbackCone G.obj.hom (Diagrams.zeroTo G.obj.right)) (hd : IsLimit d)
    (E : C.{u, v}) (g : ChosenFiberHomTests.General.fiberHom canonicalChoices q G E) :
    (toCanonicalHom q F c hc E).symm (ChosenFiberHomTests.General.fiberSource canonicalChoices canonicalLimits q
      f E g) =
      H.map (chosenFiberMap f.hom c d hd) ≫ (toCanonicalHom q G d hd E).symm g := by
  apply (toCanonicalHom q F c hc E).injective
  rw [Equiv.apply_symm_apply, toCanonicalHom_source, Equiv.apply_symm_apply]

/-- Every actual integer target map retains the same original inverse limit comparison. -/
theorem toCanonicalHom_target (q : ℤ) (F : P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    {E E' : C.{u, v}} (t : E ⟶ E') (g : chosenHom q F c E) :
    toCanonicalHom q F c hc E' (g ≫ H.map ((integerTarget q).map t)) =
      toCanonicalHom q F c hc E g ≫ H.map ((integerTarget q).map t) := by
  rw [toCanonicalHom_apply, toCanonicalHom_apply]
  exact (Category.assoc _ _ _).symm

/-- Its inverse retains the original forward limit comparison and the entire target action. -/
theorem toCanonicalHom_symm_target (q : ℤ) (F : P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    {E E' : C.{u, v}} (t : E ⟶ E') (g : ChosenFiberHomTests.General.fiberHom canonicalChoices q F E) :
    (toCanonicalHom q F c hc E').symm (g ≫ H.map ((integerTarget q).map t)) =
      (toCanonicalHom q F c hc E).symm g ≫ H.map ((integerTarget q).map t) := by
  rw [toCanonicalHom_symm_apply, toCanonicalHom_symm_apply]
  exact (Category.assoc _ _ _).symm

/-- The caller cone is tested through its full original limit comparison
and the inverse of the same canonical original comparison Hom function. -/
def cofiberToChosenFiberHomEquiv (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP
  := hP) (B := B))
    (q : ℤ) (F : P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (hE : omegaProperty E) : ChosenFiberHomTests.General.cofiberHom q F E ≃ chosenHom (q + 1) F c E :=
  (ConditionalFiberHom.General.cofiberToFiberHomEquiv (hP := hP) hComparison canonicalChoices canonicalLimits q
    F E hE).trans
    (toCanonicalHom (q + 1) F c hc E).symm

/-- The same actual point-set comparison is the whole forward Hom function. -/
theorem cofiberToChosenFiberHomEquiv_apply
    (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP := hP) (B := B)) (q : ℤ) (F :
      P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.cofiberHom q F E) :
    cofiberToChosenFiberHomEquiv (hP := hP) hComparison q F c hc E hE g =
      H.map (chosenFiberIso F.obj.hom c hc).hom ≫
        ChosenFiberHomTests.General.comparisonTest (hP := hP) canonicalChoices canonicalLimits q F E hE g :=
  toCanonicalHom_symm_apply (q + 1) F c hc E _

/-- The whole original comparison function retains the caller's same actual null class. -/
theorem cofiberToChosenFiberHomEquiv_null
    (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP := hP) (B := B)) (q : ℤ) (F :
      P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (hE : omegaProperty E) :
    cofiberToChosenFiberHomEquiv (hP := hP) hComparison q F c hc E hE
        (OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj) ((integerTarget q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom c.pt ((integerTarget (q + 1)).obj E) := by
  rw [cofiberToChosenFiberHomEquiv_apply (hP := hP), ChosenFiberHomTests.General.comparisonTest_null (hP := hP)]
  exact OrdinaryHoCofiberKernel.precomp_nullHom (chosenFiberIso F.obj.hom c hc).hom

/-- Its full inverse retains the same original cofiber null class. -/
theorem cofiberToChosenFiberHomEquiv_symm_null
    (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP := hP) (B := B)) (q : ℤ) (F :
      P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (hE : omegaProperty E) :
    (cofiberToChosenFiberHomEquiv (hP := hP) hComparison q F c hc E hE).symm
        (OrdinaryHoCofiberKernel.nullHom c.pt ((integerTarget (q + 1)).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj) ((integerTarget q).obj E) := by
  apply (cofiberToChosenFiberHomEquiv (hP := hP) hComparison q F c hc E hE).injective
  rw [Equiv.apply_symm_apply, cofiberToChosenFiberHomEquiv_null (hP := hP)]

/-- The genuine original boundary is sent to the caller's unchanged first projection. -/
theorem cofiberToChosenFiberHomEquiv_boundary
    (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP := hP) (B := B)) (q : ℤ) (F :
      P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.totalHom (q + 1) F E) :
    cofiberToChosenFiberHomEquiv (hP := hP) hComparison q F c hc E hE
      (ChosenFiberBoundaryTests.General.boundaryTest q F E hE g) =
      H.map c.fst ≫ g := by
  rw [cofiberToChosenFiberHomEquiv_apply (hP := hP),
    ChosenFiberBoundaryTests.General.boundaryTest_fiberRestriction (hP := hP)]
  have h := H.congr_map (chosenFiberIso_hom_fst F.obj.hom c hc)
  simp only [Functor.map_comp] at h
  change H.map (chosenFiberIso F.obj.hom c hc).hom ≫ (H.map (fiberToTotal F.obj.hom) ≫ g) = _
  rw [← Category.assoc, h]

/-- Every full source square retains both actual individual cones in the entire forward function. -/
theorem cofiberToChosenFiberHomEquiv_source
    (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP := hP) (B := B)) (q : ℤ)
    {F G : P.FullSubcategory} (f : F ⟶ G)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (d : PullbackCone G.obj.hom (Diagrams.zeroTo G.obj.right)) (hd : IsLimit d)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.cofiberHom q G E) :
    cofiberToChosenFiberHomEquiv (hP := hP) hComparison q F c hc E hE (ChosenFiberHomTests.General.cofiberSource
      q f E g) =
      H.map (chosenFiberMap f.hom c d hd) ≫
        cofiberToChosenFiberHomEquiv (hP := hP) hComparison q G d hd E hE g := by
  change (toCanonicalHom (q + 1) F c hc E).symm
      (ConditionalFiberHom.General.cofiberToFiberHomEquiv (hP := hP) hComparison canonicalChoices
        canonicalLimits q F E hE
        (ChosenFiberHomTests.General.cofiberSource q f E g)) = _
  rw [ConditionalFiberHom.General.cofiberToFiberHomEquiv_source (hP := hP),
    toCanonicalHom_symm_source (q + 1) f c hc d hd E]
  rfl

/-- The same full inverse retains both original individual source cones and their chosen map. -/
theorem cofiberToChosenFiberHomEquiv_symm_source
    (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP := hP) (B := B)) (q : ℤ)
    {F G : P.FullSubcategory} (f : F ⟶ G)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (d : PullbackCone G.obj.hom (Diagrams.zeroTo G.obj.right)) (hd : IsLimit d)
    (E : C.{u, v}) (hE : omegaProperty E) (g : chosenHom (q + 1) G d E) :
    (cofiberToChosenFiberHomEquiv (hP := hP) hComparison q F c hc E hE).symm
        (H.map (chosenFiberMap f.hom c d hd) ≫ g) =
      ChosenFiberHomTests.General.cofiberSource q f E ((cofiberToChosenFiberHomEquiv (hP := hP) hComparison q G
        d hd E hE).symm g) := by
  apply (cofiberToChosenFiberHomEquiv (hP := hP) hComparison q F c hc E hE).injective
  rw [Equiv.apply_symm_apply, cofiberToChosenFiberHomEquiv_source (hP := hP), Equiv.apply_symm_apply]

/-- Every original native target map retains both complete integer
actions in the forward function. -/
theorem cofiberToChosenFiberHomEquiv_target
    (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP := hP) (B := B)) (q : ℤ) (F :
      P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    {E E' : C.{u, v}} (t : E ⟶ E') (hE : omegaProperty E) (hE' : omegaProperty E')
    (g : ChosenFiberHomTests.General.cofiberHom q F E) :
    cofiberToChosenFiberHomEquiv (hP := hP) hComparison q F c hc E' hE'
      (ChosenFiberHomTests.General.cofiberTarget q F t g) =
      cofiberToChosenFiberHomEquiv (hP := hP) hComparison q F c hc E hE g ≫
        H.map ((integerTarget (q + 1)).map t) := by
  change (toCanonicalHom (q + 1) F c hc E').symm
      (ConditionalFiberHom.General.cofiberToFiberHomEquiv (hP := hP) hComparison canonicalChoices
        canonicalLimits q F E' hE'
        (ChosenFiberHomTests.General.cofiberTarget q F t g)) = _
  rw [ConditionalFiberHom.General.cofiberToFiberHomEquiv_target (hP := hP) hComparison canonicalChoices
    canonicalLimits q F t hE hE']
  change (toCanonicalHom (q + 1) F c hc E').symm
      (ConditionalFiberHom.General.cofiberToFiberHomEquiv (hP := hP) hComparison canonicalChoices
        canonicalLimits q F E hE g ≫
        H.map ((integerTarget (q + 1)).map t)) = _
  exact toCanonicalHom_symm_target (q + 1) F c hc t _

/-- The full inverse keeps the same original integer target transformation. -/
theorem cofiberToChosenFiberHomEquiv_symm_target
    (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP := hP) (B := B)) (q : ℤ) (F :
      P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    {E E' : C.{u, v}} (t : E ⟶ E') (hE : omegaProperty E) (hE' : omegaProperty E')
    (g : chosenHom (q + 1) F c E) :
    (cofiberToChosenFiberHomEquiv (hP := hP) hComparison q F c hc E' hE').symm
        (g ≫ H.map ((integerTarget (q + 1)).map t)) =
      ChosenFiberHomTests.General.cofiberTarget q F t ((cofiberToChosenFiberHomEquiv (hP := hP) hComparison q F
        c hc E hE).symm g) := by
  apply (cofiberToChosenFiberHomEquiv (hP := hP) hComparison q F c hc E' hE').injective
  rw [Equiv.apply_symm_apply,
    cofiberToChosenFiberHomEquiv_target (hP := hP) hComparison q F c hc t hE hE', Equiv.apply_symm_apply]

/-- The actual individual cone's connecting map retains the original cofiber target leg. -/
def connecting (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP := hP) (B := B))
    (q : ℤ) (F : P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (hE : omegaProperty E) : chosenHom (q + 1) F c E → FiberInclusionImage.General.baseHom q F E :=
  fun g => FiberInclusionImage.General.cofiberRestriction q F E
    ((cofiberToChosenFiberHomEquiv (hP := hP) hComparison q F c hc E hE).symm g)

/-- The unchanged base term is exact for every individually supplied caller fiber cone. -/
theorem exact_at_base (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP := hP) (B := B))
    (q : ℤ) (F : P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (hE : omegaProperty E) (g : FiberInclusionImage.General.baseHom q F E) :
    (∃ h : chosenHom (q + 1) F c E, connecting (hP := hP) hComparison q F c hc E hE h = g) ↔
      FiberInclusionImage.General.baseRestriction q F E g =
        OrdinaryHoCofiberKernel.nullHom F.obj.left ((integerTarget q).obj E) := by
  let e := cofiberToChosenFiberHomEquiv (hP := hP) hComparison q F c hc E hE
  constructor
  · rintro ⟨k, hk⟩
    exact (ConditionalFiberSequence.General.cofiberRestriction_image_iff q F E g).mp ⟨e.symm k, hk⟩
  · intro h
    obtain ⟨k, hk⟩ := (ConditionalFiberSequence.General.cofiberRestriction_image_iff q F E g).mpr h
    refine ⟨e k, ?_⟩
    change FiberInclusionImage.General.cofiberRestriction q F E (e.symm (e k)) = g
    rw [Equiv.symm_apply_apply]
    exact hk

/-- The actual caller first projection is exact at its individually chosen fiber term. -/
theorem exact_at_fiber (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP := hP) (B := B))
    (q : ℤ) (F : P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (hE : omegaProperty E) (g : chosenHom (q + 1) F c E) :
    (∃ h : ChosenFiberHomTests.General.totalHom (q + 1) F E, H.map c.fst ≫ h = g) ↔
      connecting (hP := hP) hComparison q F c hc E hE g =
        OrdinaryHoCofiberKernel.nullHom F.obj.right ((integerTarget q).obj E) := by
  let e := cofiberToChosenFiberHomEquiv (hP := hP) hComparison q F c hc E hE
  have hExact := FiberInclusionImage.General.boundary_image_iff q F E hE (e.symm g)
  constructor
  · rintro ⟨k, hk⟩
    apply hExact.mp
    refine ⟨k, ?_⟩
    apply e.injective
    rw [cofiberToChosenFiberHomEquiv_boundary (hP := hP), hk, Equiv.apply_symm_apply]
  · intro h
    obtain ⟨k, hk⟩ := hExact.mpr h
    refine ⟨k, ?_⟩
    rw [← cofiberToChosenFiberHomEquiv_boundary (hP := hP) hComparison q F c hc E hE k]
    change e (ChosenFiberBoundaryTests.General.boundaryTest q F E hE k) = g
    rw [hk, Equiv.apply_symm_apply]

/-- The shifted original total term is exact for the actual caller fst,
with no global choice-family extension required of that cone. -/
theorem exact_at_shifted_total (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP :=
  hP) (B := B))
    (q : ℤ) (F : P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.totalHom (q + 1) F E) :
    (∃ h : FiberInclusionImage.General.baseHom (q + 1) F E, FiberInclusionImage.General.baseRestriction (q + 1)
      F E h = g) ↔
      H.map c.fst ≫ g = OrdinaryHoCofiberKernel.nullHom c.pt ((integerTarget (q + 1)).obj E) := by
  apply (ConditionalFiberSequence.General.boundaryTest_null_iff_baseImage q F E hE g).trans
  constructor
  · intro h
    have h' := congrArg (cofiberToChosenFiberHomEquiv (hP := hP) hComparison q F c hc E hE) h
    rw [cofiberToChosenFiberHomEquiv_boundary (hP := hP), cofiberToChosenFiberHomEquiv_null (hP := hP)] at h'
    exact h'
  · intro h
    apply (cofiberToChosenFiberHomEquiv (hP := hP) hComparison q F c hc E hE).injective
    rw [cofiberToChosenFiberHomEquiv_boundary (hP := hP), cofiberToChosenFiberHomEquiv_null (hP := hP)]
    exact h

/-- Every actual full source square retains both individual caller
cones in the connecting square. -/
theorem connecting_source (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP := hP) (B := B))
    (q : ℤ) {F G : P.FullSubcategory} (f : F ⟶ G)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (d : PullbackCone G.obj.hom (Diagrams.zeroTo G.obj.right)) (hd : IsLimit d)
    (E : C.{u, v}) (hE : omegaProperty E) (g : chosenHom (q + 1) G d E) :
    connecting (hP := hP) hComparison q F c hc E hE (H.map (chosenFiberMap f.hom c d hd) ≫ g) =
      FiberInclusionImage.General.baseSource q f E (connecting (hP := hP) hComparison q G d hd E hE g) := by
  unfold connecting
  rw [cofiberToChosenFiberHomEquiv_symm_source (hP := hP), FiberInclusionImage.General.cofiberRestriction_source]

/-- Every original native target map retains both entire integer connecting actions. -/
theorem connecting_target (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP := hP) (B := B))
    (q : ℤ) (F : P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    {E E' : C.{u, v}} (t : E ⟶ E') (hE : omegaProperty E) (hE' : omegaProperty E')
    (g : chosenHom (q + 1) F c E) :
    connecting (hP := hP) hComparison q F c hc E' hE' (g ≫ H.map ((integerTarget (q + 1)).map t)) =
      connecting (hP := hP) hComparison q F c hc E hE g ≫ H.map ((integerTarget q).map t) := by
  unfold connecting
  rw [cofiberToChosenFiberHomEquiv_symm_target (hP := hP) hComparison q F c hc t hE hE',
    FiberInclusionImage.General.cofiberRestriction_target]

/-- Each individual connecting function preserves the caller's actual null class. -/
theorem connecting_null (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP := hP) (B := B))
    (q : ℤ) (F : P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (hE : omegaProperty E) :
    connecting (hP := hP) hComparison q F c hc E hE
        (OrdinaryHoCofiberKernel.nullHom c.pt ((integerTarget (q + 1)).obj E)) =
      OrdinaryHoCofiberKernel.nullHom F.obj.right ((integerTarget q).obj E) := by
  unfold connecting
  rw [cofiberToChosenFiberHomEquiv_symm_null (hP := hP), FiberInclusionImage.General.cofiberRestriction_null]

omit B in
/-- The original full chosen-fiber source or self-comparison law on the shared Arrow subcategory. -/
theorem canonicalSelf_hom (F : P.FullSubcategory) :
    (chosenFiberIso F.obj.hom (canonicalChoices F.obj) (canonicalLimits F.obj)).hom =
      𝟙 (fiber F.obj.hom) := by
  apply pullback.hom_ext
  · exact (chosenFiberIso_hom_fst F.obj.hom (canonicalChoices F.obj)
      (canonicalLimits F.obj)).trans (Category.id_comp _).symm
  · exact (chosenFiberIso_hom_snd F.obj.hom (canonicalChoices F.obj)
      (canonicalLimits F.obj)).trans (Category.id_comp _).symm

/-- Every whole caller family uses the same actual point-set limit
comparison as its individual caller cone. -/
theorem toCanonicalHom_eq_family
    (a : ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F)) (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (g : ChosenFiberHomTests.General.fiberHom a q F E) :
    toCanonicalHom q F (a F.obj) (ha F.obj) E g =
      ChosenFiberHomTests.General.choiceHomEquiv canonicalChoices canonicalLimits a ha q F E g := by
  rw [toCanonicalHom_apply, ChosenFiberHomTests.General.choiceHomEquiv_apply,
    ChosenFiberHomTests.General.choiceIso_eq_native canonicalChoices canonicalLimits a ha F]
  change H.map (chosenFiberIso F.obj.hom (a F.obj) (ha F.obj)).inv ≫ g =
    H.map ((chosenFiberIso F.obj.hom (canonicalChoices F.obj) (canonicalLimits F.obj)).hom ≫
      (chosenFiberIso F.obj.hom (a F.obj) (ha F.obj)).inv) ≫ g
  have hn : (chosenFiberIso F.obj.hom (canonicalChoices F.obj) (canonicalLimits F.obj)).hom ≫
      (chosenFiberIso F.obj.hom (a F.obj) (ha F.obj)).inv =
    (chosenFiberIso F.obj.hom (a F.obj) (ha F.obj)).inv :=
    (congrArg (fun t => t ≫ (chosenFiberIso F.obj.hom (a F.obj) (ha F.obj)).inv)
      (canonicalSelf_hom F)).trans (Category.id_comp _)
  exact congrArg (fun t => t ≫ g) (H.congr_map hn).symm

/-- For every actual caller family the individual cone equivalence
has exactly the unchanged original comparison test as its forward function. -/
theorem cofiberToChosenFiberHomEquiv_eq_family
    (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP := hP) (B := B))
    (a : ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F)) (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) :
    cofiberToChosenFiberHomEquiv (hP := hP) hComparison q F (a F.obj) (ha F.obj) E hE =
      ConditionalFiberHom.General.cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE := by
  apply Equiv.ext
  intro g
  apply (toCanonicalHom (q + 1) F (a F.obj) (ha F.obj) E).injective
  change toCanonicalHom (q + 1) F (a F.obj) (ha F.obj) E
      ((toCanonicalHom (q + 1) F (a F.obj) (ha F.obj) E).symm
        (ConditionalFiberHom.General.cofiberToFiberHomEquiv (hP := hP) hComparison canonicalChoices
          canonicalLimits q F E hE g)) = _
  rw [Equiv.apply_symm_apply, toCanonicalHom_eq_family,
    ConditionalFiberHom.General.cofiberToFiberHomEquiv_choice (hP := hP) hComparison canonicalChoices
      canonicalLimits a ha q F E hE]

/-- The whole family and individual caller cone give the identical
actual original connecting function in every integer degree. -/
theorem connecting_eq_family (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP :=
  hP) (B := B))
    (a : ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F)) (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.fiberHom a (q + 1) F E) :
    connecting (hP := hP) hComparison q F (a F.obj) (ha F.obj) E hE g =
      ConditionalFiberSequence.General.connecting (hP := hP) hComparison a ha q F E hE g := by
  unfold connecting
  rw [cofiberToChosenFiberHomEquiv_eq_family (hP := hP)]
  rfl

/-- The full forward caller choice map keeps the same actual original
limit comparison on every Hom test of both individual cones. -/
theorem toCanonicalHom_choice (q : ℤ) (F : P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (d : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hd : IsLimit d)
    (E : C.{u, v}) (g : chosenHom q F d E) :
    toCanonicalHom q F c hc E
        (H.map (ChosenFiberNaturality.choiceIso F.obj.hom c hc d hd).hom ≫ g) =
      toCanonicalHom q F d hd E g := by
  have hn : (chosenFiberIso F.obj.hom c hc).inv ≫
      (ChosenFiberNaturality.choiceIso F.obj.hom c hc d hd).hom =
    (chosenFiberIso F.obj.hom d hd).inv := by
    change (chosenFiberIso F.obj.hom c hc).inv ≫
      ((chosenFiberIso F.obj.hom c hc).hom ≫ (chosenFiberIso F.obj.hom d hd).inv) = _
    rw [Iso.inv_hom_id_assoc]
  have h := H.congr_map hn
  simp only [Functor.map_comp] at h
  rw [toCanonicalHom_apply, toCanonicalHom_apply]
  rw [← Category.assoc, h]

/-- The same original inverse caller choice map keeps both full Hom
functions of the two actual individual limit cones. -/
theorem toCanonicalHom_choice_inverse (q : ℤ) (F : P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (d : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hd : IsLimit d)
    (E : C.{u, v}) (g : chosenHom q F c E) :
    toCanonicalHom q F d hd E
        (H.map (ChosenFiberNaturality.choiceIso F.obj.hom c hc d hd).inv ≫ g) =
      toCanonicalHom q F c hc E g := by
  have hn : (chosenFiberIso F.obj.hom d hd).inv ≫
      (ChosenFiberNaturality.choiceIso F.obj.hom c hc d hd).inv =
    (chosenFiberIso F.obj.hom c hc).inv := by
    change (chosenFiberIso F.obj.hom d hd).inv ≫
      ((chosenFiberIso F.obj.hom d hd).hom ≫ (chosenFiberIso F.obj.hom c hc).inv) = _
    rw [Iso.inv_hom_id_assoc]
  have h := H.congr_map hn
  simp only [Functor.map_comp] at h
  rw [toCanonicalHom_apply, toCanonicalHom_apply]
  rw [← Category.assoc, h]

/-- Both full original individual caller choice maps retain the same
actual integer connecting function. -/
theorem connecting_choice (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP := hP) (B := B))
    (q : ℤ) (F : P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (d : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hd : IsLimit d)
    (E : C.{u, v}) (hE : omegaProperty E) (g : chosenHom (q + 1) F d E) :
    connecting (hP := hP) hComparison q F c hc E hE
        (H.map (ChosenFiberNaturality.choiceIso F.obj.hom c hc d hd).hom ≫ g) =
      connecting (hP := hP) hComparison q F d hd E hE g := by
  change FiberInclusionImage.General.cofiberRestriction q F E
      ((ConditionalFiberHom.General.cofiberToFiberHomEquiv (hP := hP) hComparison canonicalChoices
        canonicalLimits q F E hE).symm
        (toCanonicalHom (q + 1) F c hc E
          (H.map (ChosenFiberNaturality.choiceIso F.obj.hom c hc d hd).hom ≫ g))) = _
  rw [toCanonicalHom_choice]
  rfl

/-- Their full inverse choice direction also retains the unchanged
original integer connecting function. -/
theorem connecting_choice_inverse (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP
  := hP) (B := B))
    (q : ℤ) (F : P.FullSubcategory)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (d : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hd : IsLimit d)
    (E : C.{u, v}) (hE : omegaProperty E) (g : chosenHom (q + 1) F c E) :
    connecting (hP := hP) hComparison q F d hd E hE
        (H.map (ChosenFiberNaturality.choiceIso F.obj.hom c hc d hd).inv ≫ g) =
      connecting (hP := hP) hComparison q F c hc E hE g := by
  change FiberInclusionImage.General.cofiberRestriction q F E
      ((ConditionalFiberHom.General.cofiberToFiberHomEquiv (hP := hP) hComparison canonicalChoices
        canonicalLimits q F E hE).symm
        (toCanonicalHom (q + 1) F d hd E
          (H.map (ChosenFiberNaturality.choiceIso F.obj.hom c hc d hd).inv ≫ g))) = _
  rw [toCanonicalHom_choice_inverse]
  rfl

end General

/-- The full Hom term of the caller's individual fiber cone keeps its actual carrier. -/
abbrev chosenHom (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (E : C.{u, v}) :=
  General.chosenHom
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (c := c)
    (E := E)

/-- The original point-set limit comparison gives both whole Hom functions. -/
def toCanonicalHom (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) : chosenHom q F c E ≃ fiberHom canonicalChoices q F E :=
  General.toCanonicalHom
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (E := E)

/-- The whole forward function uses the actual inverse point-set limit comparison. -/
theorem toCanonicalHom_apply (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (g : chosenHom q F c E) :
    toCanonicalHom q F c hc E g = H.map (chosenFiberIso F.obj.hom c hc).inv ≫ g :=
  General.toCanonicalHom_apply
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (E := E)
    (g := g)

/-- Its same full inverse uses the original forward point-set limit comparison. -/
theorem toCanonicalHom_symm_apply (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (g : fiberHom canonicalChoices q F E) :
    (toCanonicalHom q F c hc E).symm g = H.map (chosenFiberIso F.obj.hom c hc).hom ≫ g :=
  General.toCanonicalHom_symm_apply
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (E := E)
    (g := g)

omit B in
private theorem canonicalMap {F G : rightArrows.{u, v}} (f : F ⟶ G) :
    chosenFiberMap f.hom (canonicalChoices F.obj) (canonicalChoices G.obj)
        (canonicalLimits G.obj) = fiberFunctor.map f.hom :=
  General.canonicalMap
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (F := F)
    (G := G)
    (f := f)

omit B in
private theorem comparison_inv_source {F G : rightArrows.{u, v}} (f : F ⟶ G)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (d : PullbackCone G.obj.hom (Diagrams.zeroTo G.obj.right)) (hd : IsLimit d) :
    fiberFunctor.map f.hom ≫ (chosenFiberIso G.obj.hom d hd).inv =
      (chosenFiberIso F.obj.hom c hc).inv ≫ chosenFiberMap f.hom c d hd :=
  General.comparison_inv_source
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (F := F)
    (G := G)
    (f := f)
    (c := c)
    (hc := hc)
    (d := d)
    (hd := hd)

/-- Every full original source Arrow square keeps both individually
supplied caller cones and their actual original fiber map. -/
theorem toCanonicalHom_source (q : ℤ) {F G : rightArrows.{u, v}} (f : F ⟶ G)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (d : PullbackCone G.obj.hom (Diagrams.zeroTo G.obj.right)) (hd : IsLimit d)
    (E : C.{u, v}) (g : chosenHom q G d E) :
    toCanonicalHom q F c hc E (H.map (chosenFiberMap f.hom c d hd) ≫ g) =
      fiberSource canonicalChoices canonicalLimits q f E (toCanonicalHom q G d hd E g) :=
  General.toCanonicalHom_source
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (G := G)
    (f := f)
    (c := c)
    (hc := hc)
    (d := d)
    (hd := hd)
    (E := E)
    (g := g)

/-- The same inverse retains both actual caller cones in every complete source square. -/
theorem toCanonicalHom_symm_source (q : ℤ) {F G : rightArrows.{u, v}} (f : F ⟶ G)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (d : PullbackCone G.obj.hom (Diagrams.zeroTo G.obj.right)) (hd : IsLimit d)
    (E : C.{u, v}) (g : fiberHom canonicalChoices q G E) :
    (toCanonicalHom q F c hc E).symm (fiberSource canonicalChoices canonicalLimits q f E g) =
      H.map (chosenFiberMap f.hom c d hd) ≫ (toCanonicalHom q G d hd E).symm g :=
  General.toCanonicalHom_symm_source
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (G := G)
    (f := f)
    (c := c)
    (hc := hc)
    (d := d)
    (hd := hd)
    (E := E)
    (g := g)

/-- Every actual integer target map retains the same original inverse limit comparison. -/
theorem toCanonicalHom_target (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    {E E' : C.{u, v}} (t : E ⟶ E') (g : chosenHom q F c E) :
    toCanonicalHom q F c hc E' (g ≫ H.map ((integerTarget q).map t)) =
      toCanonicalHom q F c hc E g ≫ H.map ((integerTarget q).map t) :=
  General.toCanonicalHom_target
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (E := E)
    (E' := E')
    (t := t)
    (g := g)

/-- Its inverse retains the original forward limit comparison and the entire target action. -/
theorem toCanonicalHom_symm_target (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    {E E' : C.{u, v}} (t : E ⟶ E') (g : fiberHom canonicalChoices q F E) :
    (toCanonicalHom q F c hc E').symm (g ≫ H.map ((integerTarget q).map t)) =
      (toCanonicalHom q F c hc E).symm g ≫ H.map ((integerTarget q).map t) :=
  General.toCanonicalHom_symm_target
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (E := E)
    (E' := E')
    (t := t)
    (g := g)

/-- The caller cone is tested through its full original limit comparison
and the inverse of the same canonical original comparison Hom function. -/
def cofiberToChosenFiberHomEquiv (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (hE : omegaProperty E) : cofiberHom q F E ≃ chosenHom (q + 1) F c E :=
  General.cofiberToChosenFiberHomEquiv
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (E := E)
    (hE := hE)

/-- The same actual point-set comparison is the whole forward Hom function. -/
theorem cofiberToChosenFiberHomEquiv_apply
    (hComparison : ComparisonHomBijections.{u, v} (B := B)) (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (hE : omegaProperty E) (g : cofiberHom q F E) :
    cofiberToChosenFiberHomEquiv hComparison q F c hc E hE g =
      H.map (chosenFiberIso F.obj.hom c hc).hom ≫
        comparisonTest canonicalChoices canonicalLimits q F E hE g :=
  General.cofiberToChosenFiberHomEquiv_apply
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (E := E)
    (hE := hE)
    (g := g)

/-- The whole original comparison function retains the caller's same actual null class. -/
theorem cofiberToChosenFiberHomEquiv_null
    (hComparison : ComparisonHomBijections.{u, v} (B := B)) (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (hE : omegaProperty E) :
    cofiberToChosenFiberHomEquiv hComparison q F c hc E hE
        (OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj) ((integerTarget q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom c.pt ((integerTarget (q + 1)).obj E) :=
  General.cofiberToChosenFiberHomEquiv_null
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (E := E)
    (hE := hE)

/-- Its full inverse retains the same original cofiber null class. -/
theorem cofiberToChosenFiberHomEquiv_symm_null
    (hComparison : ComparisonHomBijections.{u, v} (B := B)) (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (hE : omegaProperty E) :
    (cofiberToChosenFiberHomEquiv hComparison q F c hc E hE).symm
        (OrdinaryHoCofiberKernel.nullHom c.pt ((integerTarget (q + 1)).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj) ((integerTarget q).obj E) :=
  General.cofiberToChosenFiberHomEquiv_symm_null
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (E := E)
    (hE := hE)

/-- The genuine original boundary is sent to the caller's unchanged first projection. -/
theorem cofiberToChosenFiberHomEquiv_boundary
    (hComparison : ComparisonHomBijections.{u, v} (B := B)) (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (hE : omegaProperty E) (g : totalHom (q + 1) F E) :
    cofiberToChosenFiberHomEquiv hComparison q F c hc E hE (boundaryTest q F E hE g) =
      H.map c.fst ≫ g :=
  General.cofiberToChosenFiberHomEquiv_boundary
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (E := E)
    (hE := hE)
    (g := g)

/-- Every full source square retains both actual individual cones in the entire forward function. -/
theorem cofiberToChosenFiberHomEquiv_source
    (hComparison : ComparisonHomBijections.{u, v} (B := B)) (q : ℤ)
    {F G : rightArrows.{u, v}} (f : F ⟶ G)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (d : PullbackCone G.obj.hom (Diagrams.zeroTo G.obj.right)) (hd : IsLimit d)
    (E : C.{u, v}) (hE : omegaProperty E) (g : cofiberHom q G E) :
    cofiberToChosenFiberHomEquiv hComparison q F c hc E hE (cofiberSource q f E g) =
      H.map (chosenFiberMap f.hom c d hd) ≫
        cofiberToChosenFiberHomEquiv hComparison q G d hd E hE g :=
  General.cofiberToChosenFiberHomEquiv_source
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (q := q)
    (F := F)
    (G := G)
    (f := f)
    (c := c)
    (hc := hc)
    (d := d)
    (hd := hd)
    (E := E)
    (hE := hE)
    (g := g)

/-- The same full inverse retains both original individual source cones and their chosen map. -/
theorem cofiberToChosenFiberHomEquiv_symm_source
    (hComparison : ComparisonHomBijections.{u, v} (B := B)) (q : ℤ)
    {F G : rightArrows.{u, v}} (f : F ⟶ G)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (d : PullbackCone G.obj.hom (Diagrams.zeroTo G.obj.right)) (hd : IsLimit d)
    (E : C.{u, v}) (hE : omegaProperty E) (g : chosenHom (q + 1) G d E) :
    (cofiberToChosenFiberHomEquiv hComparison q F c hc E hE).symm
        (H.map (chosenFiberMap f.hom c d hd) ≫ g) =
      cofiberSource q f E ((cofiberToChosenFiberHomEquiv hComparison q G d hd E hE).symm g) :=
  General.cofiberToChosenFiberHomEquiv_symm_source
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (q := q)
    (F := F)
    (G := G)
    (f := f)
    (c := c)
    (hc := hc)
    (d := d)
    (hd := hd)
    (E := E)
    (hE := hE)
    (g := g)

/-- Every original native target map retains both complete integer
actions in the forward function. -/
theorem cofiberToChosenFiberHomEquiv_target
    (hComparison : ComparisonHomBijections.{u, v} (B := B)) (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    {E E' : C.{u, v}} (t : E ⟶ E') (hE : omegaProperty E) (hE' : omegaProperty E')
    (g : cofiberHom q F E) :
    cofiberToChosenFiberHomEquiv hComparison q F c hc E' hE' (cofiberTarget q F t g) =
      cofiberToChosenFiberHomEquiv hComparison q F c hc E hE g ≫
        H.map ((integerTarget (q + 1)).map t) :=
  General.cofiberToChosenFiberHomEquiv_target
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (E := E)
    (E' := E')
    (t := t)
    (hE := hE)
    (hE' := hE')
    (g := g)

/-- The full inverse keeps the same original integer target transformation. -/
theorem cofiberToChosenFiberHomEquiv_symm_target
    (hComparison : ComparisonHomBijections.{u, v} (B := B)) (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    {E E' : C.{u, v}} (t : E ⟶ E') (hE : omegaProperty E) (hE' : omegaProperty E')
    (g : chosenHom (q + 1) F c E) :
    (cofiberToChosenFiberHomEquiv hComparison q F c hc E' hE').symm
        (g ≫ H.map ((integerTarget (q + 1)).map t)) =
      cofiberTarget q F t ((cofiberToChosenFiberHomEquiv hComparison q F c hc E hE).symm g) :=
  General.cofiberToChosenFiberHomEquiv_symm_target
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (E := E)
    (E' := E')
    (t := t)
    (hE := hE)
    (hE' := hE')
    (g := g)

/-- The actual individual cone's connecting map retains the original cofiber target leg. -/
def connecting (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (hE : omegaProperty E) : chosenHom (q + 1) F c E → baseHom q F E :=
  General.connecting
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (E := E)
    (hE := hE)

/-- The unchanged base term is exact for every individually supplied caller fiber cone. -/
theorem exact_at_base (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (hE : omegaProperty E) (g : baseHom q F E) :
    (∃ h : chosenHom (q + 1) F c E, connecting hComparison q F c hc E hE h = g) ↔
      baseRestriction q F E g =
        OrdinaryHoCofiberKernel.nullHom F.obj.left ((integerTarget q).obj E) :=
  General.exact_at_base
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (E := E)
    (hE := hE)
    (g := g)

/-- The actual caller first projection is exact at its individually chosen fiber term. -/
theorem exact_at_fiber (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (hE : omegaProperty E) (g : chosenHom (q + 1) F c E) :
    (∃ h : totalHom (q + 1) F E, H.map c.fst ≫ h = g) ↔
      connecting hComparison q F c hc E hE g =
        OrdinaryHoCofiberKernel.nullHom F.obj.right ((integerTarget q).obj E) :=
  General.exact_at_fiber
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (E := E)
    (hE := hE)
    (g := g)

/-- The shifted original total term is exact for the actual caller fst,
with no global choice-family extension required of that cone. -/
theorem exact_at_shifted_total (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (hE : omegaProperty E) (g : totalHom (q + 1) F E) :
    (∃ h : baseHom (q + 1) F E, baseRestriction (q + 1) F E h = g) ↔
      H.map c.fst ≫ g = OrdinaryHoCofiberKernel.nullHom c.pt ((integerTarget (q + 1)).obj E) :=
  General.exact_at_shifted_total
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (E := E)
    (hE := hE)
    (g := g)

/-- Every actual full source square retains both individual caller
cones in the connecting square. -/
theorem connecting_source (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (q : ℤ) {F G : rightArrows.{u, v}} (f : F ⟶ G)
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (d : PullbackCone G.obj.hom (Diagrams.zeroTo G.obj.right)) (hd : IsLimit d)
    (E : C.{u, v}) (hE : omegaProperty E) (g : chosenHom (q + 1) G d E) :
    connecting hComparison q F c hc E hE (H.map (chosenFiberMap f.hom c d hd) ≫ g) =
      baseSource q f E (connecting hComparison q G d hd E hE g) :=
  General.connecting_source
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (q := q)
    (F := F)
    (G := G)
    (f := f)
    (c := c)
    (hc := hc)
    (d := d)
    (hd := hd)
    (E := E)
    (hE := hE)
    (g := g)

/-- Every original native target map retains both entire integer connecting actions. -/
theorem connecting_target (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    {E E' : C.{u, v}} (t : E ⟶ E') (hE : omegaProperty E) (hE' : omegaProperty E')
    (g : chosenHom (q + 1) F c E) :
    connecting hComparison q F c hc E' hE' (g ≫ H.map ((integerTarget (q + 1)).map t)) =
      connecting hComparison q F c hc E hE g ≫ H.map ((integerTarget q).map t) :=
  General.connecting_target
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (E := E)
    (E' := E')
    (t := t)
    (hE := hE)
    (hE' := hE')
    (g := g)

/-- Each individual connecting function preserves the caller's actual null class. -/
theorem connecting_null (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (E : C.{u, v}) (hE : omegaProperty E) :
    connecting hComparison q F c hc E hE
        (OrdinaryHoCofiberKernel.nullHom c.pt ((integerTarget (q + 1)).obj E)) =
      OrdinaryHoCofiberKernel.nullHom F.obj.right ((integerTarget q).obj E) :=
  General.connecting_null
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (E := E)
    (hE := hE)

omit B in
private theorem canonicalSelf_hom (F : rightArrows.{u, v}) :
    (chosenFiberIso F.obj.hom (canonicalChoices F.obj) (canonicalLimits F.obj)).hom =
      𝟙 (fiber F.obj.hom) :=
  General.canonicalSelf_hom
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (F := F)

/-- Every whole caller family uses the same actual point-set limit
comparison as its individual caller cone. -/
theorem toCanonicalHom_eq_family
    (a : ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F)) (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (g : fiberHom a q F E) :
    toCanonicalHom q F (a F.obj) (ha F.obj) E g =
      choiceHomEquiv canonicalChoices canonicalLimits a ha q F E g :=
  General.toCanonicalHom_eq_family
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)
    (g := g)

/-- For every actual caller family the individual cone equivalence
has exactly the unchanged original comparison test as its forward function. -/
theorem cofiberToChosenFiberHomEquiv_eq_family
    (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (a : ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F)) (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) :
    cofiberToChosenFiberHomEquiv hComparison q F (a F.obj) (ha F.obj) E hE =
      cofiberToFiberHomEquiv hComparison a ha q F E hE :=
  General.cofiberToChosenFiberHomEquiv_eq_family
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)

/-- The whole family and individual caller cone give the identical
actual original connecting function in every integer degree. -/
theorem connecting_eq_family (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (a : ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F)) (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) (g : fiberHom a (q + 1) F E) :
    connecting hComparison q F (a F.obj) (ha F.obj) E hE g =
      ConditionalFiberSequence.connecting hComparison a ha q F E hE g :=
  General.connecting_eq_family
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)
    (g := g)

/-- The full forward caller choice map keeps the same actual original
limit comparison on every Hom test of both individual cones. -/
theorem toCanonicalHom_choice (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (d : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hd : IsLimit d)
    (E : C.{u, v}) (g : chosenHom q F d E) :
    toCanonicalHom q F c hc E
        (H.map (ChosenFiberNaturality.choiceIso F.obj.hom c hc d hd).hom ≫ g) =
      toCanonicalHom q F d hd E g :=
  General.toCanonicalHom_choice
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (d := d)
    (hd := hd)
    (E := E)
    (g := g)

/-- The same original inverse caller choice map keeps both full Hom
functions of the two actual individual limit cones. -/
theorem toCanonicalHom_choice_inverse (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (d : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hd : IsLimit d)
    (E : C.{u, v}) (g : chosenHom q F c E) :
    toCanonicalHom q F d hd E
        (H.map (ChosenFiberNaturality.choiceIso F.obj.hom c hc d hd).inv ≫ g) =
      toCanonicalHom q F c hc E g :=
  General.toCanonicalHom_choice_inverse
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (d := d)
    (hd := hd)
    (E := E)
    (g := g)

/-- Both full original individual caller choice maps retain the same
actual integer connecting function. -/
theorem connecting_choice (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (d : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hd : IsLimit d)
    (E : C.{u, v}) (hE : omegaProperty E) (g : chosenHom (q + 1) F d E) :
    connecting hComparison q F c hc E hE
        (H.map (ChosenFiberNaturality.choiceIso F.obj.hom c hc d hd).hom ≫ g) =
      connecting hComparison q F d hd E hE g :=
  General.connecting_choice
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (d := d)
    (hd := hd)
    (E := E)
    (hE := hE)
    (g := g)

/-- Their full inverse choice direction also retains the unchanged
original integer connecting function. -/
theorem connecting_choice_inverse (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (q : ℤ) (F : rightArrows.{u, v})
    (c : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hc : IsLimit c)
    (d : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hd : IsLimit d)
    (E : C.{u, v}) (hE : omegaProperty E) (g : chosenHom (q + 1) F c E) :
    connecting hComparison q F d hd E hE
        (H.map (ChosenFiberNaturality.choiceIso F.obj.hom c hc d hd).inv ≫ g) =
      connecting hComparison q F c hc E hE g :=
  General.connecting_choice_inverse
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (q := q)
    (F := F)
    (c := c)
    (hc := hc)
    (d := d)
    (hd := hd)
    (E := E)
    (hE := hE)
    (g := g)

end PointedCGWH.Spectra.Orthogonal.ConditionalChosenFiberSequence
