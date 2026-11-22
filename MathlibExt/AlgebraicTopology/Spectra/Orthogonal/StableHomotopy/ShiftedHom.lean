/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OperatorStabilizationK
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKPuppeHom
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKSourceLoopClassTransport
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKOriginalFiberComparison
import MathlibExt.CategoryTheory.Functor.Iteration

/-!
# Original orthogonal shifted Hom tests and chosen Puppe maps

Each target shift is an iteration of the actual scalar cotensor on the full
continuous orthogonal operator carrier. Every original degree pair retains
its original stabilization transpose and scalar coordinate interchange.

The original whole Arrow I replacement supplies all Puppe terms and their
actual restriction maps. The tests retain every source Arrow map, every
target map, every stage and every scalar loop shift. Exactness is derived
from the original chosen Puppe construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.ShiftedHomTests

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := OrthogonalCarrier.{u, v}
private abbrev scalarLoop := cotensor (I := O.{u, v}) PointedCGWH.sphereOne.{u, v}
private abbrev scalarSuspension :=
  EnrichedFunctorCat.tensorLeft (A := O.{u, v}) PointedCGWH.sphereOne.{u, v}
private abbrev scalarAdjunction :=
  ScalarLeibniz.adjunction (A := O.{u, v}) PointedCGWH.sphereOne.{u, v}

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

/-- Every nonnegative shift iterates the complete original scalar loop functor. -/
def loopTarget (r : ℕ) : C.{u, v} ⥤ C.{u, v} :=
  CategoryTheory.Functor.Iteration.iterate scalarLoop r

/-- Each successor retains the entire preceding shifted target and actual cotensor. -/
theorem loopTarget_succ (r : ℕ) :
    loopTarget.{u, v} (r + 1) = loopTarget r ⋙ scalarLoop := rfl

/-- Every full original target map retains the actual iterated scalar map. -/
theorem loopTarget_map_succ (r : ℕ) {E E' : C.{u, v}} (t : E ⟶ E') :
    (loopTarget (r + 1)).map t = scalarLoop.map ((loopTarget r).map t) := rfl

/-- All original source and added degrees retain their complete actual
coefficient and scalar coordinate interchange at every shifted target. -/
theorem loopTarget_adjoint_succ (r n a : ℕ) (E : C.{u, v}) :
    NativeK.adjoint orthogonalFamily (n, a) ((loopTarget (r + 1)).obj E) =
      (ihom PointedCGWH.sphereOne).map
        (NativeK.adjoint orthogonalFamily (n, a) ((loopTarget r).obj E)) ≫
          (scalarOperatorInterchangeNatIso PointedCGWH.sphereOne
            (orthogonalFamily.coefficient (n, a))).hom.app
              (((loopTarget r).obj E).toEnrichedFunctor.obj
                (orthogonalFamily.target (n, a))) :=
  SourceLoopClassTransport.scalarCotensor_adjointOperatorMap
    (orthogonalFamily.source (n, a)) (orthogonalFamily.target (n, a))
    PointedCGWH.sphereOne (orthogonalFamily.coefficient (n, a))
    (orthogonalFamily.inclusion (n, a)) ((loopTarget r).obj E)

/-- Every original continuous-index map retains the entire scalar image
of its original component at every target loop shift. -/
theorem loopTarget_component_succ (r : ℕ) {E E' : C.{u, v}} (t : E ⟶ E') (n : ℕ) :
    component ((loopTarget (r + 1)).map t)
        (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex n) =
      (ihom PointedCGWH.sphereOne).map
        (component ((loopTarget r).map t)
          (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex n)) :=
  cotensorMap_component PointedCGWH.sphereOne ((loopTarget r).map t) _

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev H := toHomotopyCategory C.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := O.{u, v})
private abbrev S := OriginalISuspension.suspension (B := B) (I := O.{u, v})

include B in
/-- Full original paired K locality is preserved at every actual target loop shift. -/
theorem loopTarget_isOmega (r : ℕ) (E : C.{u, v}) (hE : NativeK.IsOmega orthogonalFamily E) :
    NativeK.IsOmega orthogonalFamily ((loopTarget r).obj E) := by
  let _ : IsCofibrant PointedCGWH.sphereOne.{u, v} :=
    PointedCGWH.modelCategory.sphereOne_isCofibrant
  exact CategoryTheory.Functor.Iteration.preserves scalarLoop
    (NativeK.IsOmega orthogonalFamily)
    (fun X hX => NativeK.cotensor_isOmega (B := B) orthogonalFamily PointedCGWH.sphereOne X hX)
    r E hE

private theorem scalarQuillen : scalarAdjunction.{u, v}.IsQuillenAdjunction := by
  let _ : IsCofibrant PointedCGWH.sphereOne.{u, v} :=
    PointedCGWH.modelCategory.sphereOne_isCofibrant
  exact ScalarCompatibility.scalar_isQuillen (B := B) PointedCGWH.sphereOne

attribute [local instance] scalarQuillen

private theorem qCofibrant (X : C.{u, v}) : IsCofibrant (Q.obj X) :=
  Replacement.isCofibrant_cofibrantReplacement (B := B) X

private theorem nativeFibrant (X : C.{u, v}) : IsFibrant X :=
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant X

attribute [local instance] qCofibrant nativeFibrant

/-- Both original Q counit functions give the actual source endpoint comparison. -/
def epsilonHoIso (X : C.{u, v}) : H.obj (Q.obj X) ≅ H.obj X :=
  (Replacement.cofibrantReplacementProjectionIso (B := B) (A := O.{u, v})).app X

/-- The actual original I cone and native sphere give both suspension endpoint maps. -/
def suspensionHoIso (X : C.{u, v}) :
    H.obj (S.obj (Q.obj X)) ≅ H.obj (scalarSuspension.obj (Q.obj X)) :=
  (ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B) (I := O.{u, v})).app X

/-- Every shifted scalar Hom equivalence uses the actual Quillen adjunct
on the original Q source. -/
def scalarHomEquiv (r : ℕ) (X E : C.{u, v}) :
    (H.obj (scalarSuspension.obj (Q.obj X)) ⟶ H.obj ((loopTarget r).obj E)) ≃
      (H.obj (Q.obj X) ⟶ H.obj ((loopTarget (r + 1)).obj E)) :=
  QuillenOrdinaryHoHom.homEquiv scalarAdjunction (Q.obj X) ((loopTarget r).obj E)

/-- The original I suspension tests identify with the next actual scalar target shift.
No Omega, exactness or fiber-nullity result is supplied. -/
def suspensionHomEquiv (r : ℕ) (X E : C.{u, v}) :
    (H.obj (S.obj (Q.obj X)) ⟶ H.obj ((loopTarget r).obj E)) ≃
      (H.obj X ⟶ H.obj ((loopTarget (r + 1)).obj E)) :=
  (Iso.homCongr (suspensionHoIso X) (Iso.refl _)).trans
    ((scalarHomEquiv r X E).trans (Iso.homCongr (epsilonHoIso X) (Iso.refl _)))

/-- The forward function keeps both original endpoint maps and the entire actual scalar adjunct. -/
theorem suspensionHomEquiv_apply (r : ℕ) (X E : C.{u, v})
    (g : H.obj (S.obj (Q.obj X)) ⟶ H.obj ((loopTarget r).obj E)) :
    suspensionHomEquiv r X E g =
      (epsilonHoIso X).inv ≫ scalarHomEquiv r X E ((suspensionHoIso X).inv ≫ g) := by
  simp only [suspensionHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_hom, Category.comp_id]

/-- The inverse keeps the same original endpoints and the inverse actual scalar adjunct. -/
theorem suspensionHomEquiv_symm_apply (r : ℕ) (X E : C.{u, v})
    (g : H.obj X ⟶ H.obj ((loopTarget (r + 1)).obj E)) :
    (suspensionHomEquiv r X E).symm g =
      (suspensionHoIso X).hom ≫ (scalarHomEquiv r X E).symm ((epsilonHoIso X).hom ≫ g) := by
  simp only [suspensionHomEquiv, Equiv.symm_trans_apply, Iso.homCongr_symm,
    Iso.homCongr_apply, Iso.symm_hom, Iso.symm_inv, Iso.refl_inv, Category.comp_id]

/-- Every original Q source map retains the full scalar-adjunct naturality square. -/
theorem scalarHomEquiv_source (r : ℕ) {X X' : C.{u, v}} (f : X' ⟶ X) (E : C.{u, v})
    (g : H.obj (scalarSuspension.obj (Q.obj X)) ⟶ H.obj ((loopTarget r).obj E)) :
    scalarHomEquiv r X' E (H.map (scalarSuspension.map (Q.map f)) ≫ g) =
      H.map (Q.map f) ≫ scalarHomEquiv r X E g :=
  QuillenOrdinaryHoHom.homEquiv_naturality_left scalarAdjunction ((loopTarget r).obj E) (Q.map f) g

/-- Every entire target map retains both original iterated scalar map functions. -/
theorem scalarHomEquiv_target (r : ℕ) (X : C.{u, v}) {E E' : C.{u, v}} (t : E ⟶ E')
    (g : H.obj (scalarSuspension.obj (Q.obj X)) ⟶ H.obj ((loopTarget r).obj E)) :
    scalarHomEquiv r X E' (g ≫ H.map ((loopTarget r).map t)) =
      scalarHomEquiv r X E g ≫ H.map ((loopTarget (r + 1)).map t) :=
  QuillenOrdinaryHoHom.homEquiv_naturality_right scalarAdjunction (Q.obj X) g
    ((loopTarget r).map t)

/-- The actual forward suspension Hom function retains every whole original source map. -/
theorem suspensionHomEquiv_source (r : ℕ) {X X' : C.{u, v}} (f : X' ⟶ X) (E : C.{u, v})
    (g : H.obj (S.obj (Q.obj X)) ⟶ H.obj ((loopTarget r).obj E)) :
    suspensionHomEquiv r X' E (H.map (S.map (Q.map f)) ≫ g) =
      H.map f ≫ suspensionHomEquiv r X E g := by
  rw [suspensionHomEquiv_apply, suspensionHomEquiv_apply]
  have hS := (ScalarSphereSuspension.originalISuspensionQIsoSphereQ
    (B := B) (I := O.{u, v})).inv.naturality f
  have hQ : H.map f ≫ (epsilonHoIso X).inv =
      (epsilonHoIso X').inv ≫ H.map (Q.map f) :=
    (Replacement.cofibrantReplacementProjectionIso
      (B := B) (A := O.{u, v})).inv.naturality f
  have h : (suspensionHoIso X').inv ≫ (H.map (S.map (Q.map f)) ≫ g) =
      H.map (scalarSuspension.map (Q.map f)) ≫ ((suspensionHoIso X).inv ≫ g) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ g) hS.symm).trans (Category.assoc _ _ _))
  rw [h, scalarHomEquiv_source]
  simpa only [Category.assoc] using
    congrArg (fun a => a ≫ scalarHomEquiv r X E ((suspensionHoIso X).inv ≫ g)) hQ.symm

/-- The complete forward suspension Hom function retains every whole original target map. -/
theorem suspensionHomEquiv_target (r : ℕ) (X : C.{u, v}) {E E' : C.{u, v}} (t : E ⟶ E')
    (g : H.obj (S.obj (Q.obj X)) ⟶ H.obj ((loopTarget r).obj E)) :
    suspensionHomEquiv r X E' (g ≫ H.map ((loopTarget r).map t)) =
      suspensionHomEquiv r X E g ≫ H.map ((loopTarget (r + 1)).map t) := by
  rw [suspensionHomEquiv_apply, suspensionHomEquiv_apply,
    ← Category.assoc (suspensionHoIso X).inv g, scalarHomEquiv_target, Category.assoc]

/-- The same inverse suspension Hom function retains every original source action. -/
theorem suspensionHomEquiv_symm_source (r : ℕ) {X X' : C.{u, v}} (f : X' ⟶ X)
    (E : C.{u, v}) (g : H.obj X ⟶ H.obj ((loopTarget (r + 1)).obj E)) :
    (suspensionHomEquiv r X' E).symm (H.map f ≫ g) =
      H.map (S.map (Q.map f)) ≫ (suspensionHomEquiv r X E).symm g := by
  apply (suspensionHomEquiv r X' E).injective
  rw [Equiv.apply_symm_apply, suspensionHomEquiv_source, Equiv.apply_symm_apply]

/-- The same inverse retains every complete original target action. -/
theorem suspensionHomEquiv_symm_target (r : ℕ) (X : C.{u, v}) {E E' : C.{u, v}} (t : E ⟶ E')
    (g : H.obj X ⟶ H.obj ((loopTarget (r + 1)).obj E)) :
    (suspensionHomEquiv r X E').symm (g ≫ H.map ((loopTarget (r + 1)).map t)) =
      (suspensionHomEquiv r X E).symm g ≫ H.map ((loopTarget r).map t) := by
  apply (suspensionHomEquiv r X E').injective
  rw [Equiv.apply_symm_apply, suspensionHomEquiv_target, Equiv.apply_symm_apply]

private abbrev chosenCone := OriginalICone.cone (B := B) (I := O.{u, v})
private abbrev chosenInsertion := OriginalICone.inclusion (B := B) (I := O.{u, v})
private abbrev chosenCofiber := OriginalISuspension.cocone (B := B) (I := O.{u, v})
private abbrev chosenCofiberLimit :=
  OriginalISuspension.coconeIsColimit (B := B) (I := O.{u, v})

local notation "cone" => chosenCone
local notation "ι" => chosenInsertion
local notation "c" => chosenCofiber
local notation "hc" => chosenCofiberLimit

/-- Every pair of unbounded Puppe stage and actual scalar target shift has
the original full level homotopy Hom test. -/
abbrev testTerm (r n : ℕ) (F : Arrow C.{u, v}) (E : C.{u, v}) : Type (v + 1) :=
  H.obj ((NativeK.FiberHomTests.originalQPuppeTerm (B := B) n).obj F) ⟶
    H.obj ((loopTarget r).obj E)

/-- Consecutive test maps are the original chosen Puppe restriction functions. -/
def restriction (r n : ℕ) (F : Arrow C.{u, v}) (E : C.{u, v}) :
    testTerm r (n + 1) F E → testTerm r n F E :=
  OrdinaryHoChosenPuppeHomSequence.restriction cone ι c hc n (Q.mapArrow.obj F)
    ((loopTarget r).obj E)

/-- Every original Arrow square acts by its actual original Q and full
chosen Puppe map on each shifted test. -/
def sourceAction (r n : ℕ) {F G : Arrow C.{u, v}} (q : F ⟶ G) (E : C.{u, v}) :
    testTerm r n G E → testTerm r n F E :=
  OrdinaryHoChosenPuppeHomSequence.sourceAction cone ι c hc n (Q.mapArrow.map q)
    ((loopTarget r).obj E)

/-- Every whole target map acts through its actual scalar target shift. -/
def targetAction (r n : ℕ) (F : Arrow C.{u, v}) {E E' : C.{u, v}} (t : E ⟶ E') :
    testTerm r n F E → testTerm r n F E' :=
  OrdinaryHoChosenPuppeHomSequence.targetAction cone ι c hc n (Q.mapArrow.obj F)
    ((loopTarget r).map t)

/-- Every complete source square commutes with every original shifted restriction. -/
theorem restriction_source (r n : ℕ) {F G : Arrow C.{u, v}} (q : F ⟶ G) (E : C.{u, v}) :
    restriction r n F E ∘ sourceAction r (n + 1) q E =
      sourceAction r n q E ∘ restriction r n G E :=
  OrdinaryHoChosenPuppeHomSequence.restriction_source cone ι c hc n (Q.mapArrow.map q)
    ((loopTarget r).obj E)

/-- Every complete target map commutes with every original shifted restriction. -/
theorem restriction_target (r n : ℕ) (F : Arrow C.{u, v}) {E E' : C.{u, v}} (t : E ⟶ E') :
    restriction r n F E' ∘ targetAction r (n + 1) F t =
      targetAction r n F t ∘ restriction r n F E :=
  OrdinaryHoChosenPuppeHomSequence.restriction_target cone ι c hc n (Q.mapArrow.obj F)
    ((loopTarget r).map t)

/-- The entire actual Puppe sequence is exact at every stage and shifted target. -/
theorem shiftedPuppe_exact_at (r n : ℕ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (g : testTerm r (n + 1) F E) :
    (∃ h : testTerm r (n + 2) F E, restriction r (n + 1) F E h = g) ↔
      restriction r n F E g =
        OrdinaryHoCofiberKernel.nullHom
          ((NativeK.FiberHomTests.originalQPuppeTerm (B := B) n).obj F) ((loopTarget r).obj E) :=
  NativeK.FiberHomTests.originalQPuppe_exact_at (B := B) n F ((loopTarget r).obj E) g

/-- Every original positive source suspension and actual target scalar shift
retain the same null Hom class of the original chosen cofiber. -/
theorem shiftedCofiberHom_eq_null {X Y : C.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests orthogonalFamily f) (r n : ℕ) (E : C.{u, v})
    (hE : NativeK.IsOmega orthogonalFamily E)
    (g : H.obj ((NativeK.FiberHomTests.originalQSuspensionCofiber (B := B) n).obj (Arrow.mk f)) ⟶
      H.obj ((loopTarget r).obj E)) :
    g = OrdinaryHoCofiberKernel.nullHom
      ((NativeK.FiberHomTests.originalQSuspensionCofiber (B := B) n).obj (Arrow.mk f))
        ((loopTarget r).obj E) :=
  NativeK.FiberHomTests.originalQSuspensionCofiberHom_eq_null (B := B) orthogonalFamily
    f hf n ((loopTarget r).obj E) (loopTarget_isOmega r E hE) g

end PointedCGWH.Spectra.Orthogonal.ShiftedHomTests
