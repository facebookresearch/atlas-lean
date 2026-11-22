/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.ChosenFiberBoundary

/-!
# Actual original fiber inclusion images in every integer degree

The original Q-cofiber target leg and both original Q counit maps give
the actual restriction to the unchanged base spectrum. The original
second Puppe position is exact for this same map after the actual integer
suspension Hom equivalence. The proved original boundary identity then
identifies the image of the caller's first fiber projection with the image
under the actual comparison test of this cofiber restriction kernel.

The comparison test is its actual source function throughout; neither its
bijectivity nor the full stable model is an input. All original native
source squares, full target maps and caller fiber choices are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.FiberInclusionImage

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.FiberGeometry
open PointedCGWH.Spectra.Orthogonal.ShiftedHomTests
open PointedCGWH.Spectra.Orthogonal.NegativeHomTests
open PointedCGWH.Spectra.Orthogonal.IntegerTargetTests
open PointedCGWH.Spectra.Orthogonal.ChosenFiberHomTests
open PointedCGWH.Spectra.Orthogonal.ChosenFiberBoundaryTests

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := OrthogonalCarrier.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev H := toHomotopyCategory C.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := O.{u, v})
private abbrev S := OriginalISuspension.suspension (B := B) (I := O.{u, v})
private abbrev CQ := NativeK.CofiberNullity.cofiberQ (B := B) (I := O.{u, v})
private abbrev cone := OriginalICone.cone (B := B) (I := O.{u, v})
private abbrev inclusion := OriginalICone.inclusion (B := B) (I := O.{u, v})
private abbrev c := OriginalISuspension.cocone (B := B) (I := O.{u, v})
private abbrev hc := OriginalISuspension.coconeIsColimit (B := B) (I := O.{u, v})

namespace General

variable {P : ObjectProperty (Arrow C.{u, v})}
  (hP : P ≤ ChosenFiberHomTests.fibrantFibrationProperty.{u, v} (B := B))

open PointedCGWH.Spectra.Orthogonal.ChosenFiberHomTests.General
open PointedCGWH.Spectra.Orthogonal.ChosenFiberBoundaryTests.General

/-- Every original base spectrum has its unchanged integer target Hom term. -/
abbrev baseHom (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v}) :=
  H.obj F.obj.right ⟶ H.obj ((integerTarget q).obj E)

/-- The original full native arrow acts by its unchanged level Ho source map. -/
def baseRestriction (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v}) :
    baseHom q F E → ChosenFiberHomTests.General.totalHom q F E := fun g => H.map F.obj.hom ≫ g

/-- Every actual base source map retains its original full Arrow component. -/
def baseSource (q : ℤ) {F G : P.FullSubcategory} (f : F ⟶ G) (E : C.{u, v}) :
    baseHom q G E → baseHom q F E := fun g => H.map f.hom.right ≫ g

/-- The original cofiber target leg retains the entire original Q base. -/
abbrev cofiberTargetLeg (F : P.FullSubcategory) : Q.obj F.obj.right ⟶ CQ.obj F.obj :=
  (c (Q.mapArrow.obj F.obj)).inr

/-- The actual base restriction uses the original Q counit inverse
and the unchanged original cofiber target inclusion. -/
def cofiberRestriction (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v}) :
    ChosenFiberHomTests.General.cofiberHom q F E → baseHom q F E :=
  fun g => (epsilonHoIso F.obj.right).inv ≫ (H.map (cofiberTargetLeg F) ≫ g)

/-- Every original cofiber target leg retains both complete native source components. -/
theorem cofiberTargetLeg_source {F G : P.FullSubcategory} (f : F ⟶ G) :
    cofiberTargetLeg F ≫ CQ.map f.hom = Q.map f.hom.right ≫ cofiberTargetLeg G :=
  OrdinaryHoChosenPuppe.cofiberMap_target cone inclusion c hc (Q.mapArrow.map f.hom)

/-- Every original base square retains the unchanged original arrow restriction. -/
theorem baseRestriction_source (q : ℤ) {F G : P.FullSubcategory} (f : F ⟶ G)
    (E : C.{u, v}) (g : baseHom q G E) :
    baseRestriction q F E (baseSource q f E g) =
      ChosenFiberHomTests.General.totalSource q f E (baseRestriction q G E g) := by
  have h := H.congr_map f.hom.w.symm
  simp only [Functor.map_comp] at h
  change H.map F.obj.hom ≫ (H.map f.hom.right ≫ g) =
    H.map f.hom.left ≫ (H.map G.obj.hom ≫ g)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ g) h).trans (Category.assoc _ _ _))

/-- Every full original target map retains the unchanged base restriction. -/
theorem baseRestriction_target (q : ℤ) (F : P.FullSubcategory)
    {E E' : C.{u, v}} (t : E ⟶ E') (g : baseHom q F E) :
    baseRestriction q F E' (g ≫ H.map ((integerTarget q).map t)) =
      baseRestriction q F E g ≫ H.map ((integerTarget q).map t) :=
  (Category.assoc _ _ _).symm

/-- Every complete original Q source square and counit inverse
retain the same cofiber restriction to the actual base spectrum. -/
theorem cofiberRestriction_source (q : ℤ) {F G : P.FullSubcategory} (f : F ⟶ G)
    (E : C.{u, v}) (g : ChosenFiberHomTests.General.cofiberHom q G E) :
    cofiberRestriction q F E (ChosenFiberHomTests.General.cofiberSource q f E g) =
      baseSource q f E (cofiberRestriction q G E g) := by
  have hε : H.map f.hom.right ≫ (epsilonHoIso G.obj.right).inv =
      (epsilonHoIso F.obj.right).inv ≫ H.map (Q.map f.hom.right) :=
    (Replacement.cofibrantReplacementProjectionIso
      (B := B) (A := O.{u, v})).inv.naturality f.hom.right
  have h := H.congr_map (cofiberTargetLeg_source f)
  simp only [Functor.map_comp] at h
  change (epsilonHoIso F.obj.right).inv ≫
      (H.map (cofiberTargetLeg F) ≫ (H.map (CQ.map f.hom) ≫ g)) =
    H.map f.hom.right ≫
      ((epsilonHoIso G.obj.right).inv ≫ (H.map (cofiberTargetLeg G) ≫ g))
  rw [← Category.assoc (H.map (cofiberTargetLeg F)), h,
    Category.assoc, ← Category.assoc (epsilonHoIso F.obj.right).inv,
    ← hε, Category.assoc]

/-- Every full integer target action retains both original cofiber restriction factors. -/
theorem cofiberRestriction_target (q : ℤ) (F : P.FullSubcategory)
    {E E' : C.{u, v}} (t : E ⟶ E') (g : ChosenFiberHomTests.General.cofiberHom q F E) :
    cofiberRestriction q F E' (ChosenFiberHomTests.General.cofiberTarget q F t g) =
      cofiberRestriction q F E g ≫ H.map ((integerTarget q).map t) := by
  simp only [cofiberRestriction, ChosenFiberHomTests.General.cofiberTarget, Category.assoc]

/-- The same unchanged original base restriction retains its actual null class. -/
theorem baseRestriction_null (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v}) :
    baseRestriction q F E
        (OrdinaryHoCofiberKernel.nullHom F.obj.right ((integerTarget q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom F.obj.left ((integerTarget q).obj E) :=
  OrdinaryHoCofiberKernel.precomp_nullHom F.obj.hom

/-- Both original Q counit and target-inclusion factors retain the same original null class. -/
theorem cofiberRestriction_null (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v}) :
    cofiberRestriction q F E
        (OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj) ((integerTarget q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom F.obj.right ((integerTarget q).obj E) := by
  change (epsilonHoIso F.obj.right).inv ≫
      (H.map (cofiberTargetLeg F) ≫
        OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj) ((integerTarget q).obj E)) = _
  rw [OrdinaryHoCofiberKernel.precomp_nullHom]
  exact NullHomTransport.precomp_nullHom (epsilonHoIso F.obj.right).inv

/-- The genuine original Q counit inverse transports the exact same
null kernel at the actual base and at its unchanged original Q replacement. -/
theorem cofiberRestriction_null_iff (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (g : ChosenFiberHomTests.General.cofiberHom q F E) :
    cofiberRestriction q F E g =
        OrdinaryHoCofiberKernel.nullHom F.obj.right ((integerTarget q).obj E) ↔
      H.map (cofiberTargetLeg F) ≫ g =
        OrdinaryHoCofiberKernel.nullHom (Q.obj F.obj.right) ((integerTarget q).obj E) := by
  constructor
  · intro h
    have h' := congrArg (fun t => (epsilonHoIso F.obj.right).hom ≫ t) h
    change (epsilonHoIso F.obj.right).hom ≫
        ((epsilonHoIso F.obj.right).inv ≫ (H.map (cofiberTargetLeg F) ≫ g)) = _ at h'
    rw [Iso.hom_inv_id_assoc] at h'
    exact h'.trans (NullHomTransport.precomp_nullHom (epsilonHoIso F.obj.right).hom)
  · intro h
    change (epsilonHoIso F.obj.right).inv ≫ (H.map (cofiberTargetLeg F) ≫ g) = _
    rw [h]
    exact NullHomTransport.precomp_nullHom (epsilonHoIso F.obj.right).inv

/-- The actual original boundary image is exactly the unchanged base
restriction null kernel after the entire integer suspension Hom function. -/
theorem boundary_image_iff (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v})
    (hE : omegaProperty E) (g : ChosenFiberHomTests.General.cofiberHom q F E) :
    (∃ h : ChosenFiberHomTests.General.totalHom (q + 1) F E, ChosenFiberBoundaryTests.General.boundaryTest q F E
      hE h = g) ↔
      cofiberRestriction q F E g =
        OrdinaryHoCofiberKernel.nullHom F.obj.right ((integerTarget q).obj E) := by
  let _ : IsCofibrant (Q.mapArrow.obj F.obj).right :=
    Replacement.isCofibrant_cofibrantReplacement (B := B) F.obj.right
  let _ : Cofibration (inclusion.app (Q.mapArrow.obj F.obj).left) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr
      (OriginalICone.inclusion_cofibration (Q.mapArrow.obj F.obj).left)
  let _ : IsFibrant ((integerTarget q).obj E) := allObjectsFibrant _
  have h := OrdinaryHoChosenPuppe.second_exact
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero cone inclusion c hc
      (Q.mapArrow.obj F.obj) ((integerTarget q).obj E) g
  rw [cofiberRestriction_null_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact h.mp ⟨(shiftHomEquiv q F.obj.left E hE).symm k, hk⟩
  · intro hk
    obtain ⟨k, hk⟩ := h.mpr hk
    exact ⟨shiftHomEquiv q F.obj.left E hE k, by
      change H.map (ChosenFiberBoundaryTests.General.boundary F) ≫
        (shiftHomEquiv q F.obj.left E hE).symm (shiftHomEquiv q F.obj.left E hE k) = g
      rw [Equiv.symm_apply_apply]
      exact hk⟩

variable (a : ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
  (ha : ∀ F, IsLimit (a F))

/-- The unchanged caller fiber-projection image is precisely the image
under the same actual original comparison function of the actual original
cofiber base-restriction null kernel. No comparison bijectivity is required. -/
theorem fiberRestriction_image_iff (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v})
    (hE : omegaProperty E) (g : ChosenFiberHomTests.General.fiberHom a (q + 1) F E) :
    (∃ h : ChosenFiberHomTests.General.totalHom (q + 1) F E, ChosenFiberHomTests.General.fiberRestriction a (q +
      1) F E h = g) ↔
      ∃ h : ChosenFiberHomTests.General.cofiberHom q F E, ChosenFiberHomTests.General.comparisonTest (hP := hP)
        a ha q F E hE h = g ∧
        cofiberRestriction q F E h =
          OrdinaryHoCofiberKernel.nullHom F.obj.right ((integerTarget q).obj E) := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨ChosenFiberBoundaryTests.General.boundaryTest q F E hE k, ?_, ?_⟩
    · exact (ChosenFiberBoundaryTests.General.boundaryTest_fiberRestriction (hP := hP) a ha q F E hE k).trans hk
    · exact (boundary_image_iff q F E hE _).mp ⟨k, rfl⟩
  · rintro ⟨k, hk, hNull⟩
    obtain ⟨l, hl⟩ := (boundary_image_iff q F E hE k).mpr hNull
    refine ⟨l, ?_⟩
    exact (ChosenFiberBoundaryTests.General.boundaryTest_fiberRestriction (hP := hP) a ha q F E hE l).symm.trans
      ((congrArg (ChosenFiberHomTests.General.comparisonTest (hP := hP) a ha q F E hE) hl).trans hk)

include ha hP in
/-- Full weak tests make every actual caller projection test null by
the same original boundary and cofiber nullity, in every integer degree. -/
theorem fiberRestriction_eq_null (q : ℤ) (F : P.FullSubcategory)
    (hF : NativeK.omegaTests orthogonalFamily F.obj.hom)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.totalHom (q + 1) F E) :
    ChosenFiberHomTests.General.fiberRestriction a (q + 1) F E g =
      OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((integerTarget (q + 1)).obj E) := by
  have h := NativeK.CofiberNullity.cofiberQHom_eq_null (B := B) orthogonalFamily
    F.obj.hom hF ((integerTarget q).obj E) (integerTarget_isOmega q E hE)
      (ChosenFiberBoundaryTests.General.boundaryTest q F E hE g)
  exact (ChosenFiberBoundaryTests.General.boundaryTest_fiberRestriction (hP := hP) a ha q F E hE g).symm.trans
    ((congrArg (ChosenFiberHomTests.General.comparisonTest (hP := hP) a ha q F E hE) h).trans
      (ChosenFiberHomTests.General.comparisonTest_null (hP := hP) a ha q F E hE))

end General

/-- Every original base spectrum has its unchanged integer target Hom term. -/
abbrev baseHom (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v}) :=
  General.baseHom
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (E := E)

/-- The original full native arrow acts by its unchanged level Ho source map. -/
def baseRestriction (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v}) :
    baseHom q F E → totalHom q F E :=
  General.baseRestriction
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (E := E)

/-- Every actual base source map retains its original full Arrow component. -/
def baseSource (q : ℤ) {F G : rightArrows.{u, v}} (f : F ⟶ G) (E : C.{u, v}) :
    baseHom q G E → baseHom q F E :=
  General.baseSource
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (G := G)
    (f := f)
    (E := E)

/-- The original cofiber target leg retains the entire original Q base. -/
abbrev cofiberTargetLeg (F : rightArrows.{u, v}) : Q.obj F.obj.right ⟶ CQ.obj F.obj :=
  General.cofiberTargetLeg
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (F := F)

/-- The actual base restriction uses the original Q counit inverse
and the unchanged original cofiber target inclusion. -/
def cofiberRestriction (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v}) :
    cofiberHom q F E → baseHom q F E :=
  General.cofiberRestriction
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (E := E)

/-- Every original cofiber target leg retains both complete native source components. -/
theorem cofiberTargetLeg_source {F G : rightArrows.{u, v}} (f : F ⟶ G) :
    cofiberTargetLeg F ≫ CQ.map f.hom = Q.map f.hom.right ≫ cofiberTargetLeg G :=
  General.cofiberTargetLeg_source
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (F := F)
    (G := G)
    (f := f)

/-- Every original base square retains the unchanged original arrow restriction. -/
theorem baseRestriction_source (q : ℤ) {F G : rightArrows.{u, v}} (f : F ⟶ G)
    (E : C.{u, v}) (g : baseHom q G E) :
    baseRestriction q F E (baseSource q f E g) =
      totalSource q f E (baseRestriction q G E g) :=
  General.baseRestriction_source
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (G := G)
    (f := f)
    (E := E)
    (g := g)

/-- Every full original target map retains the unchanged base restriction. -/
theorem baseRestriction_target (q : ℤ) (F : rightArrows.{u, v})
    {E E' : C.{u, v}} (t : E ⟶ E') (g : baseHom q F E) :
    baseRestriction q F E' (g ≫ H.map ((integerTarget q).map t)) =
      baseRestriction q F E g ≫ H.map ((integerTarget q).map t) :=
  General.baseRestriction_target
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (E := E)
    (E' := E')
    (t := t)
    (g := g)

/-- Every complete original Q source square and counit inverse
retain the same cofiber restriction to the actual base spectrum. -/
theorem cofiberRestriction_source (q : ℤ) {F G : rightArrows.{u, v}} (f : F ⟶ G)
    (E : C.{u, v}) (g : cofiberHom q G E) :
    cofiberRestriction q F E (cofiberSource q f E g) =
      baseSource q f E (cofiberRestriction q G E g) :=
  General.cofiberRestriction_source
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (G := G)
    (f := f)
    (E := E)
    (g := g)

/-- Every full integer target action retains both original cofiber restriction factors. -/
theorem cofiberRestriction_target (q : ℤ) (F : rightArrows.{u, v})
    {E E' : C.{u, v}} (t : E ⟶ E') (g : cofiberHom q F E) :
    cofiberRestriction q F E' (cofiberTarget q F t g) =
      cofiberRestriction q F E g ≫ H.map ((integerTarget q).map t) :=
  General.cofiberRestriction_target
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (E := E)
    (E' := E')
    (t := t)
    (g := g)

/-- The same unchanged original base restriction retains its actual null class. -/
theorem baseRestriction_null (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v}) :
    baseRestriction q F E
        (OrdinaryHoCofiberKernel.nullHom F.obj.right ((integerTarget q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom F.obj.left ((integerTarget q).obj E) :=
  General.baseRestriction_null
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (E := E)

/-- Both original Q counit and target-inclusion factors retain the same original null class. -/
theorem cofiberRestriction_null (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v}) :
    cofiberRestriction q F E
        (OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj) ((integerTarget q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom F.obj.right ((integerTarget q).obj E) :=
  General.cofiberRestriction_null
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (E := E)

/-- The genuine original Q counit inverse transports the exact same
null kernel at the actual base and at its unchanged original Q replacement. -/
theorem cofiberRestriction_null_iff (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (g : cofiberHom q F E) :
    cofiberRestriction q F E g =
        OrdinaryHoCofiberKernel.nullHom F.obj.right ((integerTarget q).obj E) ↔
      H.map (cofiberTargetLeg F) ≫ g =
        OrdinaryHoCofiberKernel.nullHom (Q.obj F.obj.right) ((integerTarget q).obj E) :=
  General.cofiberRestriction_null_iff
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (E := E)
    (g := g)

/-- The actual original boundary image is exactly the unchanged base
restriction null kernel after the entire integer suspension Hom function. -/
theorem boundary_image_iff (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v})
    (hE : omegaProperty E) (g : cofiberHom q F E) :
    (∃ h : totalHom (q + 1) F E, boundaryTest q F E hE h = g) ↔
      cofiberRestriction q F E g =
        OrdinaryHoCofiberKernel.nullHom F.obj.right ((integerTarget q).obj E) :=
  General.boundary_image_iff
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)
    (g := g)

variable (a : ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
  (ha : ∀ F, IsLimit (a F))

/-- The unchanged caller fiber-projection image is precisely the image
under the same actual original comparison function of the actual original
cofiber base-restriction null kernel. No comparison bijectivity is required. -/
theorem fiberRestriction_image_iff (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v})
    (hE : omegaProperty E) (g : fiberHom a (q + 1) F E) :
    (∃ h : totalHom (q + 1) F E, fiberRestriction a (q + 1) F E h = g) ↔
      ∃ h : cofiberHom q F E, comparisonTest a ha q F E hE h = g ∧
        cofiberRestriction q F E h =
          OrdinaryHoCofiberKernel.nullHom F.obj.right ((integerTarget q).obj E) :=
  General.fiberRestriction_image_iff
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)
    (g := g)

include ha in
/-- Full weak tests make every actual caller projection test null by
the same original boundary and cofiber nullity, in every integer degree. -/
theorem fiberRestriction_eq_null (q : ℤ) (F : rightArrows.{u, v})
    (hF : NativeK.omegaTests orthogonalFamily F.obj.hom)
    (E : C.{u, v}) (hE : omegaProperty E) (g : totalHom (q + 1) F E) :
    fiberRestriction a (q + 1) F E g =
      OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((integerTarget (q + 1)).obj E) :=
  General.fiberRestriction_eq_null
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (hF := hF)
    (E := E)
    (hE := hE)
    (g := g)

end PointedCGWH.Spectra.Orthogonal.FiberInclusionImage
