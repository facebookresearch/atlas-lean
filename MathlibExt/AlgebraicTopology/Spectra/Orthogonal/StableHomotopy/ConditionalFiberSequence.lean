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

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.ConditionalFiberHom

/-!
# Conditional full orthogonal integer fiber Hom sequence

The inverse of the actual original comparison test gives the connecting
map from the caller fiber to the unchanged base spectrum. The original
boundary equation identifies the preceding map with the caller's actual
first projection. All three consecutive pointed Hom positions are exact
in every integer degree, with their full native source and target maps.

Only the original comparison Hom premise is conditional. Original Q
counits, their Ho inverses, the original cofiber target leg and every
caller fiber choice remain the original maps throughout.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.ConditionalFiberSequence

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.Orthogonal.ShiftedHomTests
open PointedCGWH.Spectra.Orthogonal.IntegerTargetTests
open PointedCGWH.Spectra.Orthogonal.NegativeHomTests
open PointedCGWH.Spectra.Orthogonal.ChosenFiberHomTests
open PointedCGWH.Spectra.Orthogonal.ChosenFiberBoundaryTests
open PointedCGWH.Spectra.Orthogonal.FiberInclusionImage
open PointedCGWH.Spectra.Orthogonal.ConditionalFiberHom

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := OrthogonalCarrier.{u, v}
private abbrev FiberChoices :=
  ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev H := toHomotopyCategory C.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := O.{u, v})
private abbrev S := OriginalISuspension.suspension (B := B) (I := O.{u, v})
private abbrev CQ := NativeK.CofiberNullity.cofiberQ (B := B) (I := O.{u, v})
private abbrev c := OriginalISuspension.cocone (B := B) (I := O.{u, v})
private abbrev hc := OriginalISuspension.coconeIsColimit (B := B) (I := O.{u, v})

namespace General

variable {P : ObjectProperty (Arrow C.{u, v})}
  (hP : P ≤ ChosenFiberHomTests.fibrantFibrationProperty.{u, v} (B := B))

open PointedCGWH.Spectra.Orthogonal.ChosenFiberHomTests.General
open PointedCGWH.Spectra.Orthogonal.ChosenFiberBoundaryTests.General
open PointedCGWH.Spectra.Orthogonal.FiberInclusionImage.General
open PointedCGWH.Spectra.Orthogonal.ConditionalFiberHom.General

/-- Both original Q counit isomorphisms transport the unchanged base
restriction null kernel to its actual original Q source map. -/
theorem baseRestriction_null_iff (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (g : FiberInclusionImage.General.baseHom q F E) :
    FiberInclusionImage.General.baseRestriction q F E g =
        OrdinaryHoCofiberKernel.nullHom F.obj.left ((integerTarget q).obj E) ↔
      H.map (Q.map F.obj.hom) ≫ ((epsilonHoIso F.obj.right).hom ≫ g) =
        OrdinaryHoCofiberKernel.nullHom (Q.obj F.obj.left) ((integerTarget q).obj E) := by
  have hn : H.map (Q.map F.obj.hom) ≫ (epsilonHoIso F.obj.right).hom =
      (epsilonHoIso F.obj.left).hom ≫ H.map F.obj.hom :=
    (Replacement.cofibrantReplacementProjectionIso
      (B := B) (A := O.{u, v})).hom.naturality F.obj.hom
  rw [← Category.assoc, hn, Category.assoc]
  constructor
  · intro h
    change (epsilonHoIso F.obj.left).hom ≫ FiberInclusionImage.General.baseRestriction q F E g = _
    rw [h]
    exact NullHomTransport.precomp_nullHom (epsilonHoIso F.obj.left).hom
  · intro h
    have h' := congrArg (fun t => (epsilonHoIso F.obj.left).inv ≫ t) h
    rw [Iso.inv_hom_id_assoc] at h'
    exact h'.trans (NullHomTransport.precomp_nullHom (epsilonHoIso F.obj.left).inv)

/-- The actual original cofiber target restriction image is exactly
the unchanged base restriction null kernel, before any comparison premise. -/
theorem cofiberRestriction_image_iff (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (g : FiberInclusionImage.General.baseHom q F E) :
    (∃ h : ChosenFiberHomTests.General.cofiberHom q F E, FiberInclusionImage.General.cofiberRestriction q F E h = g) ↔
      FiberInclusionImage.General.baseRestriction q F E g =
        OrdinaryHoCofiberKernel.nullHom F.obj.left ((integerTarget q).obj E) := by
  have hExact := ShiftedPuppeExactness.first_exact c hc q 0 F.obj E
    ((epsilonHoIso F.obj.right).hom ≫ g)
  change (∃ h : ChosenFiberHomTests.General.cofiberHom q F E,
      H.map (FiberInclusionImage.General.cofiberTargetLeg F) ≫ h = (epsilonHoIso F.obj.right).hom ≫ g) ↔
    H.map (Q.map F.obj.hom) ≫ ((epsilonHoIso F.obj.right).hom ≫ g) =
      OrdinaryHoCofiberKernel.nullHom (Q.obj F.obj.left) ((integerTarget q).obj E) at hExact
  rw [baseRestriction_null_iff]
  constructor
  · rintro ⟨k, hk⟩
    apply hExact.mp
    refine ⟨k, ?_⟩
    have h := congrArg (fun t => (epsilonHoIso F.obj.right).hom ≫ t) hk
    change (epsilonHoIso F.obj.right).hom ≫
      ((epsilonHoIso F.obj.right).inv ≫ (H.map (FiberInclusionImage.General.cofiberTargetLeg F) ≫ k)) = _ at h
    rw [Iso.hom_inv_id_assoc] at h
    exact h
  · intro h
    obtain ⟨k, hk⟩ := hExact.mpr h
    refine ⟨k, ?_⟩
    change (epsilonHoIso F.obj.right).inv ≫ (H.map (FiberInclusionImage.General.cofiberTargetLeg F) ≫ k) = g
    rw [hk, Iso.inv_hom_id_assoc]

/-- The original unsigned suspension position transports through the
actual integer suspension Hom function to the unchanged base arrow. -/
theorem boundaryTest_null_iff_baseImage (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.totalHom (q + 1) F E) :
    (∃ h : FiberInclusionImage.General.baseHom (q + 1) F E, FiberInclusionImage.General.baseRestriction (q + 1)
      F E h = g) ↔
      ChosenFiberBoundaryTests.General.boundaryTest q F E hE g =
        OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj) ((integerTarget q).obj E) := by
  have hExact := ShiftedPuppeExactness.third_exact c hc q 0 F.obj E
    ((shiftHomEquiv q F.obj.left E hE).symm g)
  change (∃ h : H.obj (S.obj (Q.obj F.obj.right)) ⟶ H.obj ((integerTarget q).obj E),
      H.map (S.map (Q.map F.obj.hom)) ≫ h = (shiftHomEquiv q F.obj.left E hE).symm g) ↔
    ChosenFiberBoundaryTests.General.boundaryTest q F E hE g =
      OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj) ((integerTarget q).obj E) at hExact
  constructor
  · rintro ⟨k, hk⟩
    apply hExact.mp
    refine ⟨(shiftHomEquiv q F.obj.right E hE).symm k, ?_⟩
    rw [← shiftHomEquiv_symm_source q F.obj.hom E hE]
    exact congrArg (shiftHomEquiv q F.obj.left E hE).symm hk
  · intro h
    obtain ⟨k, hk⟩ := hExact.mpr h
    refine ⟨shiftHomEquiv q F.obj.right E hE k, ?_⟩
    change H.map F.obj.hom ≫ shiftHomEquiv q F.obj.right E hE k = g
    exact (shiftHomEquiv_source q F.obj.hom E hE k).symm.trans
      ((congrArg (shiftHomEquiv q F.obj.left E hE) hk).trans
        (Equiv.apply_symm_apply _ g))

variable (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP := hP) (B := B))
  (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))

/-- The fiber connecting function is the original cofiber target
restriction of the inverse of the same original comparison test. -/
def connecting (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP := hP) (B := B))
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))
    (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v}) (hE : omegaProperty E) :
    ChosenFiberHomTests.General.fiberHom a (q + 1) F E → FiberInclusionImage.General.baseHom q F E :=
  fun g => FiberInclusionImage.General.cofiberRestriction q F E
    ((ConditionalFiberHom.General.cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE).symm g)

/-- The actual original base term is exact at every integer degree. -/
theorem exact_at_base (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) (g : FiberInclusionImage.General.baseHom q F E) :
    (∃ h : ChosenFiberHomTests.General.fiberHom a (q + 1) F E, connecting (hP := hP) hComparison a ha q F E hE h = g) ↔
      FiberInclusionImage.General.baseRestriction q F E g =
        OrdinaryHoCofiberKernel.nullHom F.obj.left ((integerTarget q).obj E) := by
  let e := ConditionalFiberHom.General.cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE
  constructor
  · rintro ⟨k, hk⟩
    exact (cofiberRestriction_image_iff q F E g).mp ⟨e.symm k, hk⟩
  · intro h
    obtain ⟨k, hk⟩ := (cofiberRestriction_image_iff q F E g).mpr h
    refine ⟨e k, ?_⟩
    change FiberInclusionImage.General.cofiberRestriction q F E (e.symm (e k)) = g
    rw [Equiv.symm_apply_apply]
    exact hk

/-- The caller fiber term is exact for the unchanged first projection
and the actual original cofiber connecting function. -/
theorem exact_at_fiber (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.fiberHom a (q + 1) F E) :
    (∃ h : ChosenFiberHomTests.General.totalHom (q + 1) F E, ChosenFiberHomTests.General.fiberRestriction a (q +
      1) F E h = g) ↔
      connecting (hP := hP) hComparison a ha q F E hE g =
        OrdinaryHoCofiberKernel.nullHom F.obj.right ((integerTarget q).obj E) := by
  let e := ConditionalFiberHom.General.cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE
  rw [FiberInclusionImage.General.fiberRestriction_image_iff (hP := hP) a ha q F E hE g]
  constructor
  · rintro ⟨k, hk, hNull⟩
    change e k = g at hk
    change FiberInclusionImage.General.cofiberRestriction q F E (e.symm g) = _
    rw [← hk, Equiv.symm_apply_apply]
    exact hNull
  · intro h
    exact ⟨e.symm g, e.apply_symm_apply g, h⟩

/-- The shifted total term is exact for the actual unchanged source
arrow and the same caller first projection, in every integer degree. -/
theorem exact_at_shifted_total (hComparison : ConditionalFiberHom.General.ComparisonHomBijections.{u, v} (hP :=
  hP) (B := B))
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F)) (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.totalHom (q + 1) F E) :
    (∃ h : FiberInclusionImage.General.baseHom (q + 1) F E, FiberInclusionImage.General.baseRestriction (q + 1)
      F E h = g) ↔
      ChosenFiberHomTests.General.fiberRestriction a (q + 1) F E g =
        OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((integerTarget (q + 1)).obj E) := by
  apply (boundaryTest_null_iff_baseImage q F E hE g).trans
  constructor
  · intro h
    have h' := congrArg (ConditionalFiberHom.General.cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE) h
    rw [ConditionalFiberHom.General.cofiberToFiberHomEquiv_boundaryTest (hP := hP),
      ConditionalFiberHom.General.cofiberToFiberHomEquiv_null (hP := hP)] at h'
    exact h'
  · intro h
    apply (ConditionalFiberHom.General.cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE).injective
    rw [ConditionalFiberHom.General.cofiberToFiberHomEquiv_boundaryTest (hP := hP),
      ConditionalFiberHom.General.cofiberToFiberHomEquiv_null (hP := hP)]
    exact h

/-- Every full K-right Arrow square retains its actual caller fiber
source map and the unchanged original base component in the connecting square. -/
theorem connecting_source (q : ℤ) {F G : P.FullSubcategory} (f : F ⟶ G)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.fiberHom a (q + 1) G E) :
    connecting (hP := hP) hComparison a ha q F E hE (ChosenFiberHomTests.General.fiberSource a ha (q + 1) f E g) =
      FiberInclusionImage.General.baseSource q f E (connecting (hP := hP) hComparison a ha q G E hE g) := by
  unfold connecting
  rw [ConditionalFiberHom.General.cofiberToFiberHomEquiv_symm_source (hP := hP),
    FiberInclusionImage.General.cofiberRestriction_source]

/-- Every actual native target map retains both original integer
target actions in the full fiber connecting square. -/
theorem connecting_target (q : ℤ) (F : P.FullSubcategory)
    {E E' : C.{u, v}} (t : E ⟶ E') (hE : omegaProperty E) (hE' : omegaProperty E')
    (g : ChosenFiberHomTests.General.fiberHom a (q + 1) F E) :
    connecting (hP := hP) hComparison a ha q F E' hE' (ChosenFiberHomTests.General.fiberTarget a (q + 1) F t g) =
      connecting (hP := hP) hComparison a ha q F E hE g ≫ H.map ((integerTarget q).map t) := by
  unfold connecting
  rw [ConditionalFiberHom.General.cofiberToFiberHomEquiv_symm_target (hP := hP) hComparison a ha q F t hE hE',
    FiberInclusionImage.General.cofiberRestriction_target]

/-- The same original fiber connecting function preserves the actual null class. -/
theorem connecting_null (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) :
    connecting (hP := hP) hComparison a ha q F E hE
        (OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((integerTarget (q + 1)).obj E)) =
      OrdinaryHoCofiberKernel.nullHom F.obj.right ((integerTarget q).obj E) := by
  unfold connecting
  rw [ConditionalFiberHom.General.cofiberToFiberHomEquiv_symm_null (hP := hP),
    FiberInclusionImage.General.cofiberRestriction_null]

/-- The consecutive original first-projection and connecting maps compose to null. -/
theorem connecting_fiberRestriction (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.totalHom (q + 1) F E) :
    connecting (hP := hP) hComparison a ha q F E hE (ChosenFiberHomTests.General.fiberRestriction a (q + 1) F E g) =
      OrdinaryHoCofiberKernel.nullHom F.obj.right ((integerTarget q).obj E) :=
  (exact_at_fiber (hP := hP) hComparison a ha q F E hE _).mp ⟨g, rfl⟩

/-- The consecutive connecting and unchanged base-arrow maps compose to null. -/
theorem baseRestriction_connecting (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.fiberHom a (q + 1) F E) :
    FiberInclusionImage.General.baseRestriction q F E (connecting (hP := hP) hComparison a ha q F E hE g) =
      OrdinaryHoCofiberKernel.nullHom F.obj.left ((integerTarget q).obj E) :=
  (exact_at_base (hP := hP) hComparison a ha q F E hE _).mp ⟨g, rfl⟩

variable (b : FiberChoices.{u, v}) (hb : ∀ F, IsLimit (b F))

/-- Both actual complete caller fiber choices preserve the full connecting function. -/
theorem connecting_choice (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.fiberHom b (q + 1) F E) :
    connecting (hP := hP) hComparison a ha q F E hE (ChosenFiberHomTests.General.choiceHomEquiv a ha b hb (q +
      1) F E g) =
      connecting (hP := hP) hComparison b hb q F E hE g := by
  unfold connecting
  rw [ConditionalFiberHom.General.cofiberToFiberHomEquiv_symm_choice (hP := hP)]

/-- The same connecting function preserves the actual inverse caller choice as well. -/
theorem connecting_choice_inverse (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.fiberHom a (q + 1) F E) :
    connecting (hP := hP) hComparison b hb q F E hE
        ((ChosenFiberHomTests.General.choiceHomEquiv a ha b hb (q + 1) F E).symm g) =
      connecting (hP := hP) hComparison a ha q F E hE g := by
  unfold connecting
  rw [ConditionalFiberHom.General.cofiberToFiberHomEquiv_symm_choice_inverse (hP := hP)]

end General

/-- Both original Q counit isomorphisms transport the unchanged base
restriction null kernel to its actual original Q source map. -/
theorem baseRestriction_null_iff (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (g : baseHom q F E) :
    baseRestriction q F E g =
        OrdinaryHoCofiberKernel.nullHom F.obj.left ((integerTarget q).obj E) ↔
      H.map (Q.map F.obj.hom) ≫ ((epsilonHoIso F.obj.right).hom ≫ g) =
        OrdinaryHoCofiberKernel.nullHom (Q.obj F.obj.left) ((integerTarget q).obj E) :=
  General.baseRestriction_null_iff
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (E := E)
    (g := g)

/-- The actual original cofiber target restriction image is exactly
the unchanged base restriction null kernel, before any comparison premise. -/
theorem cofiberRestriction_image_iff (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (g : baseHom q F E) :
    (∃ h : cofiberHom q F E, cofiberRestriction q F E h = g) ↔
      baseRestriction q F E g =
        OrdinaryHoCofiberKernel.nullHom F.obj.left ((integerTarget q).obj E) :=
  General.cofiberRestriction_image_iff
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (E := E)
    (g := g)

/-- The original unsigned suspension position transports through the
actual integer suspension Hom function to the unchanged base arrow. -/
theorem boundaryTest_null_iff_baseImage (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) (g : totalHom (q + 1) F E) :
    (∃ h : baseHom (q + 1) F E, baseRestriction (q + 1) F E h = g) ↔
      boundaryTest q F E hE g =
        OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj) ((integerTarget q).obj E) :=
  General.boundaryTest_null_iff_baseImage
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)
    (g := g)

variable (hComparison : ComparisonHomBijections.{u, v} (B := B))
  (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))

/-- The fiber connecting function is the original cofiber target
restriction of the inverse of the same original comparison test. -/
def connecting (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))
    (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v}) (hE : omegaProperty E) :
    fiberHom a (q + 1) F E → baseHom q F E :=
  General.connecting
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

/-- The actual original base term is exact at every integer degree. -/
theorem exact_at_base (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) (g : baseHom q F E) :
    (∃ h : fiberHom a (q + 1) F E, connecting hComparison a ha q F E hE h = g) ↔
      baseRestriction q F E g =
        OrdinaryHoCofiberKernel.nullHom F.obj.left ((integerTarget q).obj E) :=
  General.exact_at_base
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

/-- The caller fiber term is exact for the unchanged first projection
and the actual original cofiber connecting function. -/
theorem exact_at_fiber (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) (g : fiberHom a (q + 1) F E) :
    (∃ h : totalHom (q + 1) F E, fiberRestriction a (q + 1) F E h = g) ↔
      connecting hComparison a ha q F E hE g =
        OrdinaryHoCofiberKernel.nullHom F.obj.right ((integerTarget q).obj E) :=
  General.exact_at_fiber
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

/-- The shifted total term is exact for the actual unchanged source
arrow and the same caller first projection, in every integer degree. -/
theorem exact_at_shifted_total (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F)) (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) (g : totalHom (q + 1) F E) :
    (∃ h : baseHom (q + 1) F E, baseRestriction (q + 1) F E h = g) ↔
      fiberRestriction a (q + 1) F E g =
        OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((integerTarget (q + 1)).obj E) :=
  General.exact_at_shifted_total
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

/-- Every full K-right Arrow square retains its actual caller fiber
source map and the unchanged original base component in the connecting square. -/
theorem connecting_source (q : ℤ) {F G : rightArrows.{u, v}} (f : F ⟶ G)
    (E : C.{u, v}) (hE : omegaProperty E) (g : fiberHom a (q + 1) G E) :
    connecting hComparison a ha q F E hE (fiberSource a ha (q + 1) f E g) =
      baseSource q f E (connecting hComparison a ha q G E hE g) :=
  General.connecting_source
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (G := G)
    (f := f)
    (E := E)
    (hE := hE)
    (g := g)

/-- Every actual native target map retains both original integer
target actions in the full fiber connecting square. -/
theorem connecting_target (q : ℤ) (F : rightArrows.{u, v})
    {E E' : C.{u, v}} (t : E ⟶ E') (hE : omegaProperty E) (hE' : omegaProperty E')
    (g : fiberHom a (q + 1) F E) :
    connecting hComparison a ha q F E' hE' (fiberTarget a (q + 1) F t g) =
      connecting hComparison a ha q F E hE g ≫ H.map ((integerTarget q).map t) :=
  General.connecting_target
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)
    (E' := E')
    (t := t)
    (hE := hE)
    (hE' := hE')
    (g := g)

/-- The same original fiber connecting function preserves the actual null class. -/
theorem connecting_null (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) :
    connecting hComparison a ha q F E hE
        (OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((integerTarget (q + 1)).obj E)) =
      OrdinaryHoCofiberKernel.nullHom F.obj.right ((integerTarget q).obj E) :=
  General.connecting_null
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

/-- The consecutive original first-projection and connecting maps compose to null. -/
theorem connecting_fiberRestriction (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) (g : totalHom (q + 1) F E) :
    connecting hComparison a ha q F E hE (fiberRestriction a (q + 1) F E g) =
      OrdinaryHoCofiberKernel.nullHom F.obj.right ((integerTarget q).obj E) :=
  General.connecting_fiberRestriction
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

/-- The consecutive connecting and unchanged base-arrow maps compose to null. -/
theorem baseRestriction_connecting (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) (g : fiberHom a (q + 1) F E) :
    baseRestriction q F E (connecting hComparison a ha q F E hE g) =
      OrdinaryHoCofiberKernel.nullHom F.obj.left ((integerTarget q).obj E) :=
  General.baseRestriction_connecting
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

variable (b : FiberChoices.{u, v}) (hb : ∀ F, IsLimit (b F))

/-- Both actual complete caller fiber choices preserve the full connecting function. -/
theorem connecting_choice (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) (g : fiberHom b (q + 1) F E) :
    connecting hComparison a ha q F E hE (choiceHomEquiv a ha b hb (q + 1) F E g) =
      connecting hComparison b hb q F E hE g :=
  General.connecting_choice
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)
    (g := g)

/-- The same connecting function preserves the actual inverse caller choice as well. -/
theorem connecting_choice_inverse (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) (g : fiberHom a (q + 1) F E) :
    connecting hComparison b hb q F E hE
        ((choiceHomEquiv a ha b hb (q + 1) F E).symm g) =
      connecting hComparison a ha q F E hE g :=
  General.connecting_choice_inverse
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)
    (g := g)

end PointedCGWH.Spectra.Orthogonal.ConditionalFiberSequence
