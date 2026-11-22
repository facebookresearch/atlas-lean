/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.NullHomTransport
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FunctionSpectrum.Delooping

/-!
# Actual orthogonal delooping targets and negative Hom tests

Every nonnegative delooping iterate uses the original full native right
shift. The original natural map to its one-sphere cotensor is level weak
on each actual Omega target. Its inverse in the original level Ho,
the original Q counit and the original I suspension comparison give both
full negative Hom functions. All source maps, target maps, null classes and
original comparison maps are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NegativeHomTests

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.Orthogonal.ShiftedHomTests

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := OrthogonalCarrier.{u, v}
private abbrev D := FunctionSpectrum.Delooping.firstDelooping.{u, v}
private abbrev scalarLoop := cotensor (I := O.{u, v}) PointedCGWH.sphereOne.{u, v}

/-- The public scalar loop is the unchanged original native cotensor record. -/
abbrev scalarLoopFunctor : C.{u, v} ⥤ C.{u, v} := scalarLoop.{u, v}

/-- The full public record is exactly the original scalar-loop record. -/
theorem scalarLoopFunctor_eq_original : scalarLoopFunctor.{u, v} = scalarLoop.{u, v} := rfl

/-- The original public record is the actual sphere-one cotensor, with all fields. -/
theorem scalarLoopFunctor_eq_cotensor :
    scalarLoopFunctor.{u, v} =
      cotensor (I := O.{u, v}) PointedCGWH.sphereOne.{u, v} := rfl

/-- Every public source object retains the original scalar-loop object. -/
theorem scalarLoopFunctor_obj (E : C.{u, v}) :
    scalarLoopFunctor.{u, v}.obj E = scalarLoop.{u, v}.obj E := rfl

/-- Every full public source arrow retains the original scalar-loop arrow. -/
theorem scalarLoopFunctor_map {E E' : C.{u, v}} (f : E ⟶ E') :
    scalarLoopFunctor.{u, v}.map f = scalarLoop.{u, v}.map f := rfl

/-- The target property is exactly the unchanged original paired Omega condition. -/
abbrev omegaProperty := NativeK.IsOmega orthogonalFamily.{u, v}

/-- Every actual negative target iterate retains the full original native right shift. -/
def deloopTarget (r : ℕ) : C.{u, v} ⥤ C.{u, v} :=
  CategoryTheory.Functor.Iteration.iterate D r

/-- Each successor keeps the entire previous target and original first right shift. -/
theorem deloopTarget_succ (r : ℕ) :
    deloopTarget.{u, v} (r + 1) = deloopTarget r ⋙ D := rfl

/-- Every target source map retains the actual full right-shift functor map. -/
theorem deloopTarget_map_succ (r : ℕ) {E E' : C.{u, v}} (t : E ⟶ E') :
    (deloopTarget (r + 1)).map t = D.map ((deloopTarget r).map t) := rfl

/-- Each actual delooping component retains its original shifted dimensional source. -/
theorem deloopTarget_component_succ (r n : ℕ) {E E' : C.{u, v}} (t : E ⟶ E') :
    component ((deloopTarget (r + 1)).map t)
        (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex n) =
      component ((deloopTarget r).map t)
        (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex (n + 1)) :=
  FunctionSpectrum.RightShift.shift_map_component 1 n ((deloopTarget r).map t)

/-- The first actual right shift retains the entire original shifted
evaluation functor, with both source-identification maps. -/
def firstDeloopEvaluationIso (n : ℕ) :
    D ⋙ evaluation (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex n) ≅
      evaluation (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex (n + 1)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro E E' t
    change component (D.map t) (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex n) ≫
        𝟙 _ = 𝟙 _ ≫ component t
          (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex (n + 1))
    rw [Category.comp_id, Category.id_comp]
    exact FunctionSpectrum.RightShift.shift_map_component 1 n t)

/-- Every complete actual iterate evaluation has both original source
identification maps. The full functor associator and each dimensional
normalization are retained throughout the unbounded iteration. -/
def deloopEvaluationIso (r n : ℕ) :
    deloopTarget.{u, v} r ⋙
        evaluation (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex n) ≅
      evaluation (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex (n + r)) :=
  Nat.rec (motive := fun r => ∀ n : ℕ,
    deloopTarget.{u, v} r ⋙
        evaluation (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex n) ≅
      evaluation (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex (n + r)))
    (fun _ => Functor.leftUnitor _)
    (fun r ih n =>
      eqToIso (congrArg
        (fun F => F ⋙ evaluation (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex n))
          (deloopTarget_succ r)) ≪≫
        Functor.associator (deloopTarget r) D
          (evaluation (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex n)) ≪≫
        Functor.isoWhiskerLeft (deloopTarget r) (firstDeloopEvaluationIso n) ≪≫
        ih (n + 1) ≪≫
        eqToIso (congrArg
          (fun m => evaluation (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex m))
            (by omega : (n + 1) + r = n + (r + 1)))) r n

/-- Every actual iterate map retains the original component at the
entire shifted dimensional source through both full source endpoint maps. -/
theorem deloopTarget_component (r n : ℕ) {E E' : C.{u, v}} (t : E ⟶ E') :
    component ((deloopTarget r).map t)
        (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex n) ≫
          (deloopEvaluationIso r n).hom.app E' =
      (deloopEvaluationIso r n).hom.app E ≫
        component t (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex (n + r)) :=
  (deloopEvaluationIso r n).hom.naturality t

/-- The same full dimensional source identification retains every
iterate map through both of its original inverse endpoint functions. -/
theorem deloopTarget_component_inverse (r n : ℕ) {E E' : C.{u, v}} (t : E ⟶ E') :
    component t (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex (n + r)) ≫
        (deloopEvaluationIso r n).inv.app E' =
      (deloopEvaluationIso r n).inv.app E ≫
        component ((deloopTarget r).map t)
          (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex n) :=
  (deloopEvaluationIso r n).inv.naturality t

/-- All actual right-shift iterates preserve every original source/added-degree Omega test. -/
theorem deloopTarget_isOmega (r : ℕ) (E : C.{u, v}) (hE : omegaProperty E) :
    omegaProperty ((deloopTarget r).obj E) :=
  CategoryTheory.Functor.Iteration.preserves D omegaProperty
    (fun X hX => FunctionSpectrum.Delooping.firstDelooping_isOmega X hX) r E hE

/-- The original comparison is whiskered on its unchanged full actual target functor. -/
def rawDeltaIterate (r : ℕ) :
    deloopTarget.{u, v} r ⟶ deloopTarget r ⋙ FunctionSpectrum.Delooping.firstDeloopingLoop :=
  Functor.whiskerLeft (deloopTarget r) FunctionSpectrum.Delooping.delta

/-- Both full original target normalization functions retain the actual
associator and the same original successor functor equality. -/
def deltaLoopTargetIso (r : ℕ) :
    deloopTarget.{u, v} r ⋙ FunctionSpectrum.Delooping.firstDeloopingLoop ≅
      deloopTarget (r + 1) ⋙ scalarLoop :=
  (Functor.associator (deloopTarget r) D scalarLoop).symm ≪≫
    eqToIso (congrArg (fun F => F ⋙ scalarLoop) (deloopTarget_succ r).symm)

/-- Each entire original structure comparison uses the actual delta
and both original target normalization endpoint maps. -/
def deltaIterate (r : ℕ) : deloopTarget.{u, v} r ⟶ deloopTarget (r + 1) ⋙ scalarLoop :=
  rawDeltaIterate r ≫ (deltaLoopTargetIso r).hom

/-- Every complete original comparison app retains the actual supplier
delta and the unchanged entire target normalization map. -/
theorem deltaIterate_app (r : ℕ) (E : C.{u, v}) :
    (deltaIterate r).app E =
      FunctionSpectrum.Delooping.delta.app ((deloopTarget r).obj E) ≫
        (deltaLoopTargetIso r).hom.app E := rfl

/-- Every original component is the original paired structure transpose,
the inverse sphere-one coefficient, and the full target normalization.
Both normalization endpoints remain present for every iterate and index. -/
theorem deltaIterate_component (r n : ℕ) (E : C.{u, v}) :
    component ((deltaIterate r).app E)
        (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex n) =
      (FunctionSpectrum.ShiftOmega.omegaMap ((deloopTarget r).obj E) n 1 ≫
        (MonoidalClosed.pre CategoryTheory.Spectra.orthogonalOneSphereIsoSphereOne.{u, v}.inv).app
          (((deloopTarget r).obj E).toEnrichedFunctor.obj
            (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex (n + 1)))) ≫
        component ((deltaLoopTargetIso r).hom.app E)
          (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex n) := by
  rw [deltaIterate_app, component_comp,
    FunctionSpectrum.Delooping.delta_component]
  rfl

/-- Every complete native target map retains both original delta components. -/
theorem deltaIterate_naturality (r : ℕ) {E E' : C.{u, v}} (t : E ⟶ E') :
    (deloopTarget r).map t ≫ (deltaIterate r).app E' =
      (deltaIterate r).app E ≫ scalarLoop.map ((deloopTarget (r + 1)).map t) :=
  (deltaIterate r).naturality t

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev H := toHomotopyCategory C.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := O.{u, v})
private abbrev S := OriginalISuspension.suspension (B := B) (I := O.{u, v})

/-- The actual original delta is weak in the same native level class for
every original cardinal bottom and every actual Omega target. -/
theorem deltaIterate_levelWeak (r : ℕ) (E : C.{u, v}) (hE : omegaProperty E) :
    weakEquivalences C.{u, v} ((deltaIterate r).app E) := by
  have h : weakEquivalences C.{u, v} ((rawDeltaIterate r).app E) :=
    FunctionSpectrum.Delooping.delta_weak ((deloopTarget r).obj E) (deloopTarget_isOmega r E hE)
  exact (weakEquivalences C.{u, v}).comp_mem _ _ h
    ((weakEquivalences C.{u, v}).of_isIso ((deltaLoopTargetIso r).hom.app E))

/-- Both original level Ho maps come from the actual weak delta; the
inverse is its genuine level Ho inverse. -/
def deltaHoIso (r : ℕ) (E : C.{u, v}) (hE : omegaProperty E) :
    H.obj ((deloopTarget r).obj E) ≅ H.obj (scalarLoop.obj ((deloopTarget (r + 1)).obj E)) := by
  let _ : IsIso (H.map ((deltaIterate r).app E)) :=
    Localization.inverts H (weakEquivalences C.{u, v}) _ (deltaIterate_levelWeak r E hE)
  exact asIso (H.map ((deltaIterate r).app E))

/-- The full forward level Ho comparison is the unchanged original delta map. -/
theorem deltaHoIso_hom (r : ℕ) (E : C.{u, v}) (hE : omegaProperty E) :
    (deltaHoIso r E hE).hom = H.map ((deltaIterate r).app E) := rfl

/-- Every actual target map retains the complete forward level Ho delta square. -/
theorem deltaHoIso_hom_naturality (r : ℕ) {E E' : C.{u, v}} (t : E ⟶ E')
    (hE : omegaProperty E) (hE' : omegaProperty E') :
    H.map ((deloopTarget r).map t) ≫ (deltaHoIso r E' hE').hom =
      (deltaHoIso r E hE).hom ≫ H.map (scalarLoop.map ((deloopTarget (r + 1)).map t)) :=
  (H.map_comp _ _).symm.trans
    ((H.congr_map (deltaIterate_naturality r t)).trans (H.map_comp _ _))

/-- Both complete actual level Ho inverse functions retain the same
full original target naturality square. -/
theorem deltaHoIso_inv_naturality (r : ℕ) {E E' : C.{u, v}} (t : E ⟶ E')
    (hE : omegaProperty E) (hE' : omegaProperty E') :
    H.map (scalarLoop.map ((deloopTarget (r + 1)).map t)) ≫ (deltaHoIso r E' hE').inv =
      (deltaHoIso r E hE).inv ≫ H.map ((deloopTarget r).map t) := by
  apply (cancel_epi (deltaHoIso r E hE).hom).mp
  rw [← Category.assoc, ← deltaHoIso_hom_naturality r t hE hE', Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- The original scalar suspension Hom equivalence is normalized at the
unchanged target before any actual right-shift target is substituted. -/
def unshiftedSuspensionHomEquiv (X E : C.{u, v}) :
    (H.obj (S.obj (Q.obj X)) ⟶ H.obj E) ≃ (H.obj X ⟶ H.obj (scalarLoop.obj E)) :=
  suspensionHomEquiv 0 X E

/-- Its complete forward function is the same original scalar suspension function. -/
theorem unshiftedSuspensionHomEquiv_apply (X E : C.{u, v})
    (g : H.obj (S.obj (Q.obj X)) ⟶ H.obj E) :
    unshiftedSuspensionHomEquiv X E g = suspensionHomEquiv 0 X E g := rfl

/-- Its entire inverse is the same original inverse scalar suspension function. -/
theorem unshiftedSuspensionHomEquiv_symm_apply (X E : C.{u, v})
    (g : H.obj X ⟶ H.obj (scalarLoop.obj E)) :
    (unshiftedSuspensionHomEquiv X E).symm g = (suspensionHomEquiv 0 X E).symm g := rfl

/-- Every original whole Q source map retains the same normalized scalar function. -/
theorem unshiftedSuspensionHomEquiv_source {X X' : C.{u, v}} (f : X' ⟶ X) (E : C.{u, v})
    (g : H.obj (S.obj (Q.obj X)) ⟶ H.obj E) :
    unshiftedSuspensionHomEquiv X' E (H.map (S.map (Q.map f)) ≫ g) =
      H.map f ≫ unshiftedSuspensionHomEquiv X E g :=
  suspensionHomEquiv_source 0 f E g

/-- Every original full target map retains the same normalized scalar cotensor map. -/
theorem unshiftedSuspensionHomEquiv_target (X : C.{u, v}) {E E' : C.{u, v}} (t : E ⟶ E')
    (g : H.obj (S.obj (Q.obj X)) ⟶ H.obj E) :
    unshiftedSuspensionHomEquiv X E' (g ≫ H.map t) =
      unshiftedSuspensionHomEquiv X E g ≫ H.map (scalarLoop.map t) :=
  suspensionHomEquiv_target 0 X t g

/-- The normalized function retains the actual original null class. -/
theorem unshiftedSuspensionHomEquiv_null (X E : C.{u, v}) :
    unshiftedSuspensionHomEquiv X E (OrdinaryHoCofiberKernel.nullHom (S.obj (Q.obj X)) E) =
      OrdinaryHoCofiberKernel.nullHom X (scalarLoop.obj E) :=
  NullHomTransport.suspensionHomEquiv_null 0 X E

/-- The original Q suspension test at the next actual delooping target
is the original test at the preceding target, by the actual delta inverse. -/
def negativeHomEquiv (r : ℕ) (X E : C.{u, v}) (hE : omegaProperty E) :
    (H.obj (S.obj (Q.obj X)) ⟶ H.obj ((deloopTarget (r + 1)).obj E)) ≃
      (H.obj X ⟶ H.obj ((deloopTarget r).obj E)) where
  toFun g := unshiftedSuspensionHomEquiv X ((deloopTarget (r + 1)).obj E) g ≫
    (deltaHoIso r E hE).inv
  invFun g := (unshiftedSuspensionHomEquiv X ((deloopTarget (r + 1)).obj E)).symm
    (g ≫ (deltaHoIso r E hE).hom)
  left_inv g := by
    apply (unshiftedSuspensionHomEquiv X ((deloopTarget (r + 1)).obj E)).injective
    dsimp only
    rw [Equiv.apply_symm_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  right_inv g := by
    dsimp only
    rw [Equiv.apply_symm_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The full forward function retains the actual original scalar
adjunct, both source comparisons and actual level Ho delta inverse. -/
theorem negativeHomEquiv_apply (r : ℕ) (X E : C.{u, v}) (hE : omegaProperty E)
    (g : H.obj (S.obj (Q.obj X)) ⟶ H.obj ((deloopTarget (r + 1)).obj E)) :
    negativeHomEquiv r X E hE g =
      unshiftedSuspensionHomEquiv X ((deloopTarget (r + 1)).obj E) g ≫
        (deltaHoIso r E hE).inv := rfl

/-- The full inverse retains the same original forward delta and the
actual inverse scalar suspension Hom function. -/
theorem negativeHomEquiv_symm_apply (r : ℕ) (X E : C.{u, v}) (hE : omegaProperty E)
    (g : H.obj X ⟶ H.obj ((deloopTarget r).obj E)) :
    (negativeHomEquiv r X E hE).symm g =
      (unshiftedSuspensionHomEquiv X ((deloopTarget (r + 1)).obj E)).symm
        (g ≫ (deltaHoIso r E hE).hom) := rfl

/-- Every complete original Q source action is retained by the negative Hom function. -/
theorem negativeHomEquiv_source (r : ℕ) {X X' : C.{u, v}} (f : X' ⟶ X)
    (E : C.{u, v}) (hE : omegaProperty E)
    (g : H.obj (S.obj (Q.obj X)) ⟶ H.obj ((deloopTarget (r + 1)).obj E)) :
    negativeHomEquiv r X' E hE (H.map (S.map (Q.map f)) ≫ g) =
      H.map f ≫ negativeHomEquiv r X E hE g := by
  rw [negativeHomEquiv_apply, negativeHomEquiv_apply]
  have h : unshiftedSuspensionHomEquiv X' ((deloopTarget (r + 1)).obj E)
      (H.map (S.map (Q.map f)) ≫ g) =
    H.map f ≫ unshiftedSuspensionHomEquiv X ((deloopTarget (r + 1)).obj E) g :=
    unshiftedSuspensionHomEquiv_source f ((deloopTarget (r + 1)).obj E) g
  exact (congrArg (fun t => t ≫ (deltaHoIso r E hE).inv) h).trans (Category.assoc _ _ _)

/-- Every entire original target action retains both actual right-shift
maps and the same level Ho delta inverse. -/
theorem negativeHomEquiv_target (r : ℕ) (X : C.{u, v}) {E E' : C.{u, v}} (t : E ⟶ E')
    (hE : omegaProperty E) (hE' : omegaProperty E')
    (g : H.obj (S.obj (Q.obj X)) ⟶ H.obj ((deloopTarget (r + 1)).obj E)) :
    negativeHomEquiv r X E' hE' (g ≫ H.map ((deloopTarget (r + 1)).map t)) =
      negativeHomEquiv r X E hE g ≫ H.map ((deloopTarget r).map t) := by
  rw [negativeHomEquiv_apply, negativeHomEquiv_apply]
  have h : unshiftedSuspensionHomEquiv X ((deloopTarget (r + 1)).obj E')
      (g ≫ H.map ((deloopTarget (r + 1)).map t)) =
    unshiftedSuspensionHomEquiv X ((deloopTarget (r + 1)).obj E) g ≫
      H.map (scalarLoop.map ((deloopTarget (r + 1)).map t)) :=
    unshiftedSuspensionHomEquiv_target X ((deloopTarget (r + 1)).map t) g
  exact (congrArg (fun a => a ≫ (deltaHoIso r E' hE').inv) h).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun a => unshiftedSuspensionHomEquiv X ((deloopTarget (r + 1)).obj E) g ≫ a)
        (deltaHoIso_inv_naturality r t hE hE')).trans (Category.assoc _ _ _).symm))

/-- The same full original source action is retained by the inverse negative test. -/
theorem negativeHomEquiv_symm_source (r : ℕ) {X X' : C.{u, v}} (f : X' ⟶ X)
    (E : C.{u, v}) (hE : omegaProperty E)
    (g : H.obj X ⟶ H.obj ((deloopTarget r).obj E)) :
    (negativeHomEquiv r X' E hE).symm (H.map f ≫ g) =
      H.map (S.map (Q.map f)) ≫ (negativeHomEquiv r X E hE).symm g := by
  apply (negativeHomEquiv r X' E hE).injective
  rw [Equiv.apply_symm_apply, negativeHomEquiv_source r f E hE, Equiv.apply_symm_apply]

/-- The entire inverse retains both actual delooping target actions. -/
theorem negativeHomEquiv_symm_target (r : ℕ) (X : C.{u, v}) {E E' : C.{u, v}} (t : E ⟶ E')
    (hE : omegaProperty E) (hE' : omegaProperty E')
    (g : H.obj X ⟶ H.obj ((deloopTarget r).obj E)) :
    (negativeHomEquiv r X E' hE').symm (g ≫ H.map ((deloopTarget r).map t)) =
      (negativeHomEquiv r X E hE).symm g ≫ H.map ((deloopTarget (r + 1)).map t) := by
  apply (negativeHomEquiv r X E' hE').injective
  rw [Equiv.apply_symm_apply, negativeHomEquiv_target r X t hE hE', Equiv.apply_symm_apply]

/-- Every actual negative Hom function retains the original null class,
by the same scalar adjunct and actual full level Ho target map. -/
theorem negativeHomEquiv_null (r : ℕ) (X E : C.{u, v}) (hE : omegaProperty E) :
    negativeHomEquiv r X E hE
        (OrdinaryHoCofiberKernel.nullHom (S.obj (Q.obj X)) ((deloopTarget (r + 1)).obj E)) =
      OrdinaryHoCofiberKernel.nullHom X ((deloopTarget r).obj E) := by
  rw [negativeHomEquiv_apply]
  have h : unshiftedSuspensionHomEquiv X ((deloopTarget (r + 1)).obj E)
      (OrdinaryHoCofiberKernel.nullHom (S.obj (Q.obj X)) ((deloopTarget (r + 1)).obj E)) =
    OrdinaryHoCofiberKernel.nullHom X (scalarLoop.obj ((deloopTarget (r + 1)).obj E)) :=
    unshiftedSuspensionHomEquiv_null X ((deloopTarget (r + 1)).obj E)
  exact (congrArg (fun t => t ≫ (deltaHoIso r E hE).inv) h).trans
    (NullHomTransport.nullHom_postcomp (deltaHoIso r E hE).inv)

/-- Both original inverse functions retain that same negative null test. -/
theorem negativeHomEquiv_symm_null (r : ℕ) (X E : C.{u, v}) (hE : omegaProperty E) :
    (negativeHomEquiv r X E hE).symm
        (OrdinaryHoCofiberKernel.nullHom X ((deloopTarget r).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (S.obj (Q.obj X)) ((deloopTarget (r + 1)).obj E) := by
  apply (negativeHomEquiv r X E hE).injective
  rw [Equiv.apply_symm_apply, negativeHomEquiv_null]

end PointedCGWH.Spectra.Orthogonal.NegativeHomTests
