/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AlgebraicGroupPointRepresentations
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Actual formal loop coefficients on every algebra test

The positive ring is the full R[[z]], and the loop ring is its actual
localization at z. Every map is the original coefficientwise
power-series map followed by that localization. All coefficient
algebras, including nonreduced and zero algebras, are retained.

For the classical complex Satake geometry take the base B to be C.
The sheaf coefficient ring is a separate parameter; integral coefficients
do not change the complex geometric base. These ring/test constructors
also make sense over other original coefficient bases.

Reference: Mirkovic--Vilonen, arXiv:math/0401222v5, Section 2 and
Sections 4--5. This is the formal loop model, distinct from Witt loops.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ClassicalLoopCoefficientTests

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (B : Type) [CommRing B]

/-- The original full formal power-series coefficient ring. -/
abbrev PositiveRing (R : CommAlgCat.{0} B) := PowerSeries R

/-- The genuine formal Laurent localization; no fraction field is substituted. -/
abbrev LoopRing (R : CommAlgCat.{0} B) := Localization.Away (PowerSeries.X : PositiveRing B R)

/-- Original B scalars in the formal positive ring. -/
def positiveScalars (R : CommAlgCat.{0} B) : B →+* PositiveRing B R :=
  PowerSeries.C.comp (algebraMap B R)

def loopScalars (R : CommAlgCat.{0} B) : B →+* LoopRing B R :=
  (algebraMap (PositiveRing B R) (LoopRing B R)).comp (positiveScalars B R)

/-- The actual positive coefficient algebra over the original B. -/
def positiveTest (R : CommAlgCat.{0} B) : CommAlgCat.{0} B := by
  letI := (positiveScalars B R).toAlgebra
  exact CommAlgCat.of B (PositiveRing B R)

/-- Its actual z-localized coefficient test. -/
def loopTest (R : CommAlgCat.{0} B) : CommAlgCat.{0} B := by
  letI := (loopScalars B R).toAlgebra
  exact CommAlgCat.of B (LoopRing B R)

/-- The positive test map acts coefficientwise on every original series. -/
def positiveMap {R S : CommAlgCat.{0} B} (f : R ⟶ S) :
    positiveTest B R ⟶ positiveTest B S := by
  letI := (positiveScalars B R).toAlgebra
  letI := (positiveScalars B S).toAlgebra
  exact CommAlgCat.ofHom
    { __ := PowerSeries.map f.hom.toRingHom
      commutes' := fun a ↦ by
        change PowerSeries.map f.hom.toRingHom (PowerSeries.C (algebraMap B R a)) =
          PowerSeries.C (algebraMap B S a)
        rw [PowerSeries.map_C]
        exact congrArg PowerSeries.C (f.hom.commutes a) }

/-- The original positive test functor on all B-algebras. -/
def positiveTests : CommAlgCat.{0} B ⥤ CommAlgCat.{0} B where
  obj := positiveTest B
  map := positiveMap B
  map_id R := by
    ext x
    change PowerSeries.map (RingHom.id R) x = x
    rw [PowerSeries.map_id]
    rfl
  map_comp f g := by
    ext x
    change PowerSeries.map (g.hom.toRingHom.comp f.hom.toRingHom) x =
      PowerSeries.map g.hom.toRingHom (PowerSeries.map f.hom.toRingHom x)
    rw [PowerSeries.map_comp]
    rfl

/-- The coefficientwise map sends z to the genuine unit z in the target loop ring. -/
theorem loop_parameter_unit {R S : CommAlgCat.{0} B} (f : R ⟶ S) :
    IsUnit (((algebraMap (PositiveRing B S) (LoopRing B S)).comp
      (PowerSeries.map f.hom.toRingHom)) PowerSeries.X) := by
  change IsUnit (algebraMap (PositiveRing B S) (LoopRing B S)
    (PowerSeries.map f.hom.toRingHom PowerSeries.X))
  rw [PowerSeries.map_X]
  exact IsLocalization.Away.algebraMap_isUnit (S := LoopRing B S) PowerSeries.X

/-- The coefficientwise series map induces this actual z-localization ring map. -/
def loopRingMap {R S : CommAlgCat.{0} B} (f : R ⟶ S) :
    LoopRing B R →+* LoopRing B S :=
  Localization.awayLift
    ((algebraMap (PositiveRing B S) (LoopRing B S)).comp (PowerSeries.map f.hom.toRingHom))
    PowerSeries.X (loop_parameter_unit B f)

/-- Every original positive coefficient has its original localized image. -/
theorem loopRingMap_coefficients {R S : CommAlgCat.{0} B} (f : R ⟶ S)
    (a : PositiveRing B R) :
    loopRingMap B f (algebraMap (PositiveRing B R) (LoopRing B R) a) =
      algebraMap (PositiveRing B S) (LoopRing B S) (PowerSeries.map f.hom.toRingHom a) :=
  IsLocalization.Away.lift_eq PowerSeries.X (loop_parameter_unit B f) a

/-- The original loop-ring map is the identity on an identity coefficient map. -/
theorem loopRingMap_id (R : CommAlgCat.{0} B) :
    loopRingMap B (𝟙 R) = RingHom.id (LoopRing B R) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (PowerSeries.X : PositiveRing B R))
  ext a
  rw [RingHom.comp_apply, RingHom.comp_apply, loopRingMap_coefficients]
  simp

/-- Composition preserves the original coefficientwise/localization maps. -/
theorem loopRingMap_comp {R S T : CommAlgCat.{0} B} (f : R ⟶ S) (g : S ⟶ T) :
    loopRingMap B (f ≫ g) = (loopRingMap B g).comp (loopRingMap B f) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (PowerSeries.X : PositiveRing B R))
  ext a
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
    loopRingMap_coefficients, loopRingMap_coefficients, loopRingMap_coefficients]
  change algebraMap (PositiveRing B T) (LoopRing B T)
    (PowerSeries.map (g.hom.toRingHom.comp f.hom.toRingHom) a) = _
  rw [PowerSeries.map_comp]
  rfl

/-- The actual B-algebra map on the full formal loop rings. -/
def loopMap {R S : CommAlgCat.{0} B} (f : R ⟶ S) : loopTest B R ⟶ loopTest B S := by
  letI := (loopScalars B R).toAlgebra
  letI := (loopScalars B S).toAlgebra
  exact CommAlgCat.ofHom
    { __ := loopRingMap B f
      commutes' := fun a ↦ by
        change loopRingMap B f (algebraMap (PositiveRing B R) (LoopRing B R)
          (PowerSeries.C (algebraMap B R a))) = _
        rw [loopRingMap_coefficients, PowerSeries.map_C]
        exact congrArg (fun b : S ↦
          algebraMap (PositiveRing B S) (LoopRing B S) (PowerSeries.C b))
          (f.hom.commutes a) }

/-- The actual loop test functor, with all original coefficient arrows. -/
def loopTests : CommAlgCat.{0} B ⥤ CommAlgCat.{0} B where
  obj := loopTest B
  map := loopMap B
  map_id R := by
    apply CommAlgCat.hom_ext
    apply AlgHom.toRingHom_injective
    change loopRingMap B (𝟙 R) = RingHom.id (LoopRing B R)
    exact loopRingMap_id B R
  map_comp {R S T} f g := by
    apply CommAlgCat.hom_ext
    apply AlgHom.toRingHom_injective
    change loopRingMap B (f ≫ g) = (loopRingMap B g).comp (loopRingMap B f)
    exact loopRingMap_comp B f g

/-- The original formal positive-to-loop localization map. -/
def localizationTest (R : CommAlgCat.{0} B) : positiveTest B R ⟶ loopTest B R := by
  letI := (positiveScalars B R).toAlgebra
  letI := (loopScalars B R).toAlgebra
  exact CommAlgCat.ofHom
    { __ := algebraMap (PositiveRing B R) (LoopRing B R)
      commutes' := fun _ ↦ rfl }

/-- Its native coefficientwise naturality on every algebra test. -/
def testLocalizations : positiveTests B ⟶ loopTests B where
  app := localizationTest B
  naturality {R S} f := by
    ext a
    change algebraMap (PositiveRing B S) (LoopRing B S)
      (PowerSeries.map f.hom.toRingHom a) =
        loopRingMap B f (algebraMap (PositiveRing B R) (LoopRing B R) a)
    exact (loopRingMap_coefficients B f a).symm

variable (G : Over (Spec (.of B))) [GrpObj G]

/-- Actual positive-loop group-scheme points on all formal coefficient tests. -/
def positiveLoops : CommAlgCat.{0} B ⥤ GrpCat :=
  positiveTests B ⋙ AlgebraicGroupPointRepresentations.groups B G

/-- Actual loop group-scheme points on their original z-localizations. -/
def loops : CommAlgCat.{0} B ⥤ GrpCat :=
  loopTests B ⋙ AlgebraicGroupPointRepresentations.groups B G

/-- The actual positive-loop inclusion, before any quotient or geometry. -/
def positiveToLoop : positiveLoops B G ⟶ loops B G :=
  _root_.CategoryTheory.Functor.whiskerRight (testLocalizations B)
    (AlgebraicGroupPointRepresentations.groups B G)

end MathlibExt.AlgebraicGeometry.ClassicalLoopCoefficientTests
