/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.NegativeHom

/-!
# Every actual orthogonal integer target and shifted Hom function

Nonnegative integer targets are the original scalar loop iterates;
negative targets are the actual full native right-shift deloopings.
Every target retains the original paired Omega condition. Both entire
successor comparison maps are a tracked natural isomorphism. The original
Q suspension and actual negative Hom functions give the full test
equivalence in every integer degree, preserving all source and target
actions and the unchanged null classes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.IntegerTargetTests

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.Orthogonal.ShiftedHomTests
open PointedCGWH.Spectra.Orthogonal.NegativeHomTests

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := OrthogonalCarrier.{u, v}

/-- Every original integer target is an actual complete native functor. -/
def integerTarget : ℤ → C.{u, v} ⥤ C.{u, v}
  | .ofNat r => loopTarget r
  | .negSucc r => deloopTarget (r + 1)

/-- Every nonnegative target retains precisely the original scalar loop iterate. -/
theorem integerTarget_nonnegative (r : ℕ) : integerTarget.{u, v} (Int.ofNat r) = loopTarget r := rfl

/-- Every negative target is the actual full native first-right-shift iterate. -/
theorem integerTarget_negative (r : ℕ) :
    integerTarget.{u, v} (Int.negSucc r) = deloopTarget (r + 1) := rfl

/-- The original successor target before integer normalization retains its exact source functor. -/
def successorTarget : ℤ → C.{u, v} ⥤ C.{u, v}
  | .ofNat r => loopTarget (r + 1)
  | .negSucc r => deloopTarget r

/-- Both entire target comparison functions use the actual integer
successor equality, including the original zero-target functors. -/
def successorTargetIso : ∀ q : ℤ, successorTarget.{u, v} q ≅ integerTarget (q + 1)
  | .ofNat r => eqToIso (congrArg integerTarget
      (show Int.ofNat (r + 1) = Int.ofNat r + 1 from rfl))
  | .negSucc 0 => Iso.refl _
  | .negSucc (r + 1) => eqToIso (congrArg integerTarget
      (show Int.negSucc r = Int.negSucc (r + 1) + 1 by omega))

/-- Every actual native target map retains the full forward successor comparison. -/
theorem successorTargetIso_hom_naturality (q : ℤ) {E E' : C.{u, v}} (t : E ⟶ E') :
    (successorTarget q).map t ≫ (successorTargetIso q).hom.app E' =
      (successorTargetIso q).hom.app E ≫ (integerTarget (q + 1)).map t :=
  (successorTargetIso q).hom.naturality t

/-- Its entire inverse retains the same original target square. -/
theorem successorTargetIso_inv_naturality (q : ℤ) {E E' : C.{u, v}} (t : E ⟶ E') :
    (integerTarget (q + 1)).map t ≫ (successorTargetIso q).inv.app E' =
      (successorTargetIso q).inv.app E ≫ (successorTarget q).map t :=
  (successorTargetIso q).inv.naturality t

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev H := toHomotopyCategory C.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := O.{u, v})
private abbrev S := OriginalISuspension.suspension (B := B) (I := O.{u, v})

/-- Every integer target preserves each original source/added-degree Omega test. -/
theorem integerTarget_isOmega (q : ℤ) (E : C.{u, v}) (hE : omegaProperty E) :
    omegaProperty ((integerTarget q).obj E) := by
  cases q with
  | ofNat r => exact loopTarget_isOmega r E hE
  | negSucc r => exact deloopTarget_isOmega (r + 1) E hE

/-- The original unnormalized successor target retains the full same Omega condition. -/
theorem successorTarget_isOmega (q : ℤ) (E : C.{u, v}) (hE : omegaProperty E) :
    omegaProperty ((successorTarget q).obj E) := by
  cases q with
  | ofNat r => exact loopTarget_isOmega (r + 1) E hE
  | negSucc r => exact deloopTarget_isOmega r E hE

/-- Both actual Hom functions use the original scalar or genuine
delooping comparison at every original integer target. -/
def shiftHomEquivCore : ∀ (q : ℤ) (X E : C.{u, v}), omegaProperty E →
    (H.obj (S.obj (Q.obj X)) ⟶ H.obj ((integerTarget q).obj E)) ≃
      (H.obj X ⟶ H.obj ((successorTarget q).obj E))
  | .ofNat r, X, E, _ => suspensionHomEquiv r X E
  | .negSucc r, X, E, hE => negativeHomEquiv r X E hE

/-- Every full native source map retains the original Q suspension action. -/
theorem shiftHomEquivCore_source (q : ℤ) {X X' : C.{u, v}} (f : X' ⟶ X)
    (E : C.{u, v}) (hE : omegaProperty E)
    (g : H.obj (S.obj (Q.obj X)) ⟶ H.obj ((integerTarget q).obj E)) :
    shiftHomEquivCore q X' E hE (H.map (S.map (Q.map f)) ≫ g) =
      H.map f ≫ shiftHomEquivCore q X E hE g := by
  cases q with
  | ofNat r => exact suspensionHomEquiv_source r f E g
  | negSucc r => exact negativeHomEquiv_source r f E hE g

/-- Every complete original target action retains the actual integer and successor maps. -/
theorem shiftHomEquivCore_target (q : ℤ) (X : C.{u, v}) {E E' : C.{u, v}} (t : E ⟶ E')
    (hE : omegaProperty E) (hE' : omegaProperty E')
    (g : H.obj (S.obj (Q.obj X)) ⟶ H.obj ((integerTarget q).obj E)) :
    shiftHomEquivCore q X E' hE' (g ≫ H.map ((integerTarget q).map t)) =
      shiftHomEquivCore q X E hE g ≫ H.map ((successorTarget q).map t) := by
  cases q with
  | ofNat r => exact suspensionHomEquiv_target r X t g
  | negSucc r => exact negativeHomEquiv_target r X t hE hE' g

/-- The original core function retains the same actual null class in every integer degree. -/
theorem shiftHomEquivCore_null (q : ℤ) (X E : C.{u, v}) (hE : omegaProperty E) :
    shiftHomEquivCore q X E hE
        (OrdinaryHoCofiberKernel.nullHom (S.obj (Q.obj X)) ((integerTarget q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom X ((successorTarget q).obj E) := by
  cases q with
  | ofNat r => exact NullHomTransport.suspensionHomEquiv_null r X E
  | negSucc r => exact negativeHomEquiv_null r X E hE

/-- The complete integer test equivalence retains both original
successor endpoint functions as well as the actual core Hom functions. -/
def shiftHomEquiv (q : ℤ) (X E : C.{u, v}) (hE : omegaProperty E) :
    (H.obj (S.obj (Q.obj X)) ⟶ H.obj ((integerTarget q).obj E)) ≃
      (H.obj X ⟶ H.obj ((integerTarget (q + 1)).obj E)) :=
  (shiftHomEquivCore q X E hE).trans
    (Iso.homCongr (Iso.refl _) (H.mapIso ((successorTargetIso q).app E)))

/-- Every entire forward integer test function keeps the original successor comparison map. -/
theorem shiftHomEquiv_apply (q : ℤ) (X E : C.{u, v}) (hE : omegaProperty E)
    (g : H.obj (S.obj (Q.obj X)) ⟶ H.obj ((integerTarget q).obj E)) :
    shiftHomEquiv q X E hE g =
      shiftHomEquivCore q X E hE g ≫ H.map ((successorTargetIso q).hom.app E) := by
  simp only [shiftHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_inv, Functor.mapIso_hom, Iso.app_hom, Category.id_comp]

/-- Every entire inverse integer test function keeps the original inverse comparison map. -/
theorem shiftHomEquiv_symm_apply (q : ℤ) (X E : C.{u, v}) (hE : omegaProperty E)
    (g : H.obj X ⟶ H.obj ((integerTarget (q + 1)).obj E)) :
    (shiftHomEquiv q X E hE).symm g =
      (shiftHomEquivCore q X E hE).symm (g ≫ H.map ((successorTargetIso q).inv.app E)) := by
  simp only [shiftHomEquiv, Equiv.symm_trans_apply, Iso.homCongr_symm,
    Iso.homCongr_apply, Iso.symm_inv, Iso.symm_hom, Iso.refl_hom,
    Functor.mapIso_inv, Iso.app_inv, Category.id_comp]

/-- Every unchanged full native Q source map retains both complete integer Hom functions. -/
theorem shiftHomEquiv_source (q : ℤ) {X X' : C.{u, v}} (f : X' ⟶ X)
    (E : C.{u, v}) (hE : omegaProperty E)
    (g : H.obj (S.obj (Q.obj X)) ⟶ H.obj ((integerTarget q).obj E)) :
    shiftHomEquiv q X' E hE (H.map (S.map (Q.map f)) ≫ g) =
      H.map f ≫ shiftHomEquiv q X E hE g := by
  rw [shiftHomEquiv_apply, shiftHomEquiv_apply, shiftHomEquivCore_source, Category.assoc]

/-- Every full original target map retains the whole integer successor square. -/
theorem shiftHomEquiv_target (q : ℤ) (X : C.{u, v}) {E E' : C.{u, v}} (t : E ⟶ E')
    (hE : omegaProperty E) (hE' : omegaProperty E')
    (g : H.obj (S.obj (Q.obj X)) ⟶ H.obj ((integerTarget q).obj E)) :
    shiftHomEquiv q X E' hE' (g ≫ H.map ((integerTarget q).map t)) =
      shiftHomEquiv q X E hE g ≫ H.map ((integerTarget (q + 1)).map t) := by
  rw [shiftHomEquiv_apply, shiftHomEquiv_apply, shiftHomEquivCore_target q X t hE hE']
  have h : H.map ((successorTarget q).map t) ≫
      H.map ((successorTargetIso q).hom.app E') =
    H.map ((successorTargetIso q).hom.app E) ≫ H.map ((integerTarget (q + 1)).map t) :=
    (H.map_comp _ _).symm.trans
      ((H.congr_map (successorTargetIso_hom_naturality q t)).trans (H.map_comp _ _))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => shiftHomEquivCore q X E hE g ≫ a) h).trans (Category.assoc _ _ _).symm)

/-- The same original full source action is retained by the inverse integer function. -/
theorem shiftHomEquiv_symm_source (q : ℤ) {X X' : C.{u, v}} (f : X' ⟶ X)
    (E : C.{u, v}) (hE : omegaProperty E)
    (g : H.obj X ⟶ H.obj ((integerTarget (q + 1)).obj E)) :
    (shiftHomEquiv q X' E hE).symm (H.map f ≫ g) =
      H.map (S.map (Q.map f)) ≫ (shiftHomEquiv q X E hE).symm g := by
  apply (shiftHomEquiv q X' E hE).injective
  rw [Equiv.apply_symm_apply, shiftHomEquiv_source q f E hE, Equiv.apply_symm_apply]

/-- The entire inverse integer function retains every original target map. -/
theorem shiftHomEquiv_symm_target (q : ℤ) (X : C.{u, v}) {E E' : C.{u, v}} (t : E ⟶ E')
    (hE : omegaProperty E) (hE' : omegaProperty E')
    (g : H.obj X ⟶ H.obj ((integerTarget (q + 1)).obj E)) :
    (shiftHomEquiv q X E' hE').symm (g ≫ H.map ((integerTarget (q + 1)).map t)) =
      (shiftHomEquiv q X E hE).symm g ≫ H.map ((integerTarget q).map t) := by
  apply (shiftHomEquiv q X E' hE').injective
  rw [Equiv.apply_symm_apply, shiftHomEquiv_target q X t hE hE', Equiv.apply_symm_apply]

/-- Every complete integer Hom function retains the unchanged ordinary null class. -/
theorem shiftHomEquiv_null (q : ℤ) (X E : C.{u, v}) (hE : omegaProperty E) :
    shiftHomEquiv q X E hE
        (OrdinaryHoCofiberKernel.nullHom (S.obj (Q.obj X)) ((integerTarget q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom X ((integerTarget (q + 1)).obj E) := by
  rw [shiftHomEquiv_apply, shiftHomEquivCore_null,
    OrdinaryHoCofiberKernel.nullHom_postcomp_map]

/-- The complete inverse integer function preserves the original null class in every degree. -/
theorem shiftHomEquiv_symm_null (q : ℤ) (X E : C.{u, v}) (hE : omegaProperty E) :
    (shiftHomEquiv q X E hE).symm
        (OrdinaryHoCofiberKernel.nullHom X ((integerTarget (q + 1)).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (S.obj (Q.obj X)) ((integerTarget q).obj E) := by
  apply (shiftHomEquiv q X E hE).injective
  rw [Equiv.apply_symm_apply, shiftHomEquiv_null]

/-- The actual original precomposition function at every integer target shift. -/
def precomposition (q : ℤ) {X Y : C.{u, v}} (f : X ⟶ Y) (E : C.{u, v}) :
    (H.obj Y ⟶ H.obj ((integerTarget q).obj E)) →
      (H.obj X ⟶ H.obj ((integerTarget q).obj E)) := fun g => H.map f ≫ g

/-- The original weak tests give every unbounded actual integer target test. -/
theorem precomposition_bijective (q : ℤ) {X Y : C.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests orthogonalFamily f) (E : C.{u, v}) (hE : omegaProperty E) :
    Function.Bijective (precomposition q f E) :=
  hf ((integerTarget q).obj E) (integerTarget_isOmega q E hE)

/-- These are exactly the same original all-target weak tests, retaining
every integer degree rather than requiring either source endpoint to be local. -/
theorem omegaTests_iff_integerTests {X Y : C.{u, v}} (f : X ⟶ Y) :
    NativeK.omegaTests orthogonalFamily f ↔
      ∀ q : ℤ, ∀ E : C.{u, v}, omegaProperty E → Function.Bijective (precomposition q f E) := by
  constructor
  · intro hf q E hE
    exact precomposition_bijective q f hf E hE
  · intro h E hE
    exact h 0 E hE

end PointedCGWH.Spectra.Orthogonal.IntegerTargetTests
