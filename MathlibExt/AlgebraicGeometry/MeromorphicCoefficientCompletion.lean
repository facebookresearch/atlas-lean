/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MeromorphicHeckeModels
public import Mathlib.Algebra.Ring.Equiv

/-!
# Completion of the actual finite-pole coefficient subring

For an original Cartier chart A with parameter t, the meromorphic
coefficient ring is A[1/t]. Its map to the actual analytic punctured
sections uses the genuine unit restriction of t. The image is an actual
subring of those sections. Completion is defined on A[1/t] and, through
the injective restriction dictionary, on that image subring.

The completed target is the original chart-kernel completion with its
original parameter inverted. Every coefficient map below is fixed by
the actual restriction/completion units. Essential singularities need
not lie in this finite-pole image.

Reference: Fargues--Scholze, arXiv:2102.13459v4, Section III.3 and VI.1;
Beauville--Laszlo, *Un lemme de descente*.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MeromorphicCoefficientCompletion

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundleModifications AnalyticMeromorphicCoordinates

variable (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
  {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
  (Q : PoleChart p E d U)

omit [Fact p.Prime] in
/-- Native analytic arrows preserve every original E coefficient. -/
theorem sectionMap_coefficients {V W : ESpace p E} (f : W ⟶ V) :
    (sectionMap p E f).comp (coefficients p E V) = coefficients p E W := by
  have h := congrArg Quiver.Hom.unop f.w
  exact congrArg (fun a : CommRingCat.of E ⟶ (globalRings p).obj (op W.left) ↦ a.hom) h

/-- The actual rational finite-pole localization of the original chart ring. -/
abbrev MeromorphicRing := Localization.Away Q.parameter

variable (h : IsUnit (sectionMap p E Q.puncture.map Q.parameter))

/-- The actual restriction map on finite-pole coefficients. -/
def puncturedMap : MeromorphicRing p E d U Q →+* SectionRing p E Q.puncture.space :=
  Localization.awayLift (sectionMap p E Q.puncture.map) Q.parameter h

omit [Fact p.Prime] in
/-- Original chart coefficients restrict by their original analytic section map. -/
theorem puncturedMap_coefficients (a : SectionRing p E Q.space) :
    puncturedMap p E d U Q h (algebraMap _ (MeromorphicRing p E d U Q) a) =
      sectionMap p E Q.puncture.map a :=
  IsLocalization.Away.lift_eq Q.parameter h a

/-- The actual finite-pole image subring of the punctured analytic ring. -/
def MeromorphicImage : Subring (SectionRing p E Q.puncture.space) :=
  (puncturedMap p E d U Q h).range

/-- The original completion unit followed by actual parameter localization. -/
def completedCoefficientMap : SectionRing p E Q.space →+*
    MeromorphicHeckeModels.GenericRing p E d U Q :=
  (algebraMap (MeromorphicHeckeModels.FormalRing p E d U Q)
    (MeromorphicHeckeModels.GenericRing p E d U Q)).comp
      (MeromorphicHeckeModels.completionMap p E d U Q)

omit [Fact p.Prime] in
/-- The Cartier parameter is a genuine unit in that completed generic ring. -/
theorem completed_parameter_unit :
    IsUnit (completedCoefficientMap p E d U Q Q.parameter) :=
  IsLocalization.Away.algebraMap_isUnit
    (S := MeromorphicHeckeModels.GenericRing p E d U Q)
    (MeromorphicHeckeModels.formalParameter p E d U Q)

/-- Completion of finite-pole coefficients, using the actual localization universal map. -/
def completedMap : MeromorphicRing p E d U Q →+*
    MeromorphicHeckeModels.GenericRing p E d U Q :=
  Localization.awayLift (completedCoefficientMap p E d U Q) Q.parameter
    (completed_parameter_unit p E d U Q)

/-- The original restriction identifies its finite-pole image through the actual ring map. -/
def imageEquivalence (hi : Function.Injective (puncturedMap p E d U Q h)) :
    MeromorphicRing p E d U Q ≃+* MeromorphicImage p E d U Q h :=
  RingEquiv.ofBijective (puncturedMap p E d U Q h).rangeRestrict
    ⟨fun _ _ e ↦ hi (congrArg Subtype.val e),
      (puncturedMap p E d U Q h).rangeRestrict_surjective⟩

/-- Completion on the actual bounded-pole subring of punctured analytic sections. -/
def imageCompletion (hi : Function.Injective (puncturedMap p E d U Q h)) :
    MeromorphicImage p E d U Q h →+* MeromorphicHeckeModels.GenericRing p E d U Q :=
  (completedMap p E d U Q).comp (imageEquivalence p E d U Q h hi).symm.toRingHom

omit [Fact p.Prime] in
/-- The image-subring completion is the original finite-pole coefficient completion. -/
theorem imageCompletion_normalized
    (hi : Function.Injective (puncturedMap p E d U Q h))
    (a : MeromorphicRing p E d U Q) :
    imageCompletion p E d U Q h hi ((puncturedMap p E d U Q h).rangeRestrict a) =
      completedMap p E d U Q a := by
  change completedMap p E d U Q
    ((imageEquivalence p E d U Q h hi).symm ((imageEquivalence p E d U Q h hi) a)) = _
  rw [RingEquiv.symm_apply_apply]

omit [Fact p.Prime] in
/-- Its unit square retains every original analytic coefficient. -/
theorem completedMap_coefficients (a : SectionRing p E Q.space) :
    completedMap p E d U Q (algebraMap _ (MeromorphicRing p E d U Q) a) =
      completedCoefficientMap p E d U Q a :=
  IsLocalization.Away.lift_eq Q.parameter (completed_parameter_unit p E d U Q) a

/-- Original E scalars in the actual finite-pole ring. -/
def meromorphicScalars : E →+* MeromorphicRing p E d U Q :=
  (algebraMap (SectionRing p E Q.space) (MeromorphicRing p E d U Q)).comp
    (coefficients p E Q.space)

omit [Fact p.Prime] in
/-- The original coefficient field is retained in the positive-to-generic completion. -/
theorem completedMap_scalars (a : E) :
    completedMap p E d U Q (meromorphicScalars p E d U Q a) =
      MeromorphicHeckeModels.genericScalars p E d U Q a :=
  completedMap_coefficients p E d U Q (coefficients p E Q.space a)

/-- Native E-algebra test on A[1/t]. -/
def meromorphicTest : CommAlgCat.{0} E := by
  let f : E →+* MeromorphicRing p E d U Q := meromorphicScalars p E d U Q
  letI : Algebra E (MeromorphicRing p E d U Q) := f.toAlgebra
  exact CommAlgCat.of E (MeromorphicRing p E d U Q)

/-- Native E-algebra test on the original completed parameter localization. -/
def completedTest : CommAlgCat.{0} E := by
  let f : E →+* MeromorphicHeckeModels.GenericRing p E d U Q :=
    MeromorphicHeckeModels.genericScalars p E d U Q
  letI : Algebra E (MeromorphicHeckeModels.GenericRing p E d U Q) := f.toAlgebra
  exact CommAlgCat.of E (MeromorphicHeckeModels.GenericRing p E d U Q)

/-- Restriction of the finite-pole test to the original punctured coefficient test. -/
def punctureTestMap : meromorphicTest p E d U Q ⟶
    puncturedCoefficientTest p E d U Q := by
  let f : E →+* MeromorphicRing p E d U Q := meromorphicScalars p E d U Q
  let g : E →+* SectionRing p E Q.puncture.space := coefficients p E Q.puncture.space
  letI := f.toAlgebra
  letI := g.toAlgebra
  exact CommAlgCat.ofHom
    { __ := puncturedMap p E d U Q h
      commutes' := fun a ↦
        (puncturedMap_coefficients p E d U Q h (coefficients p E Q.space a)).trans
          (DFunLike.congr_fun (sectionMap_coefficients p E Q.puncture.map) a) }

/-- The actual coefficient-preserving completion arrow on those original tests. -/
def completionTestMap : meromorphicTest p E d U Q ⟶ completedTest p E d U Q := by
  let f : E →+* MeromorphicRing p E d U Q := meromorphicScalars p E d U Q
  let g : E →+* MeromorphicHeckeModels.GenericRing p E d U Q :=
    MeromorphicHeckeModels.genericScalars p E d U Q
  letI := f.toAlgebra
  letI := g.toAlgebra
  exact CommAlgCat.ofHom
    { __ := completedMap p E d U Q
      commutes' := completedMap_scalars p E d U Q }

end MathlibExt.AlgebraicGeometry.MeromorphicCoefficientCompletion
