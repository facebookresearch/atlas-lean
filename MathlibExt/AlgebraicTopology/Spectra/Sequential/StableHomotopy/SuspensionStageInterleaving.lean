/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.SuspensionCoefficientInterchange
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.SuspensionLoopShift

/-!
# Original suspension maps on every integer-diagonal stage

The actual scalar tensor successor map contains the complete coefficient
swap. Its action on the original suspension image supplies the negative
structure square. Alternating the same original group inversions produces
the two actual interleaving maps, with the original level and degree
indices and scalar-unit forward map retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Topology
open scoped MonoidalClosed CGWH.limits unitInterval

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStageGeometry

open PointedCGWH.SuspensionCoefficientInterchangeGeometry
open PointedCGWH.SuspensionReflectionGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionLoopShiftGeometry
open PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The original equal-circle coefficient swap has its actual strict second inverse. -/
theorem coefficientSwap_comp_self (A : PointedCGWH.{u, v}) :
    coefficientSwap A ≫ coefficientSwap A = 𝟙 _ := by
  have hb : (β_ PointedCGWH.sphereOne PointedCGWH.sphereOne).inv ≫
      (β_ PointedCGWH.sphereOne PointedCGWH.sphereOne).inv = 𝟙 _ :=
    (congrArg (fun f => f ≫ (β_ PointedCGWH.sphereOne PointedCGWH.sphereOne).inv)
      (SymmetricCategory.braiding_swap_eq_inv_braiding
        PointedCGWH.sphereOne PointedCGWH.sphereOne).symm).trans
      (β_ PointedCGWH.sphereOne PointedCGWH.sphereOne).hom_inv_id
  rw [coefficientSwap]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, hb, id_whiskerRight, Category.id_comp, Iso.inv_hom_id]

private theorem scalarTensorSuccessorCoefficient (A H : PointedCGWH.{u, v})
    (s : PointedCGWH.sphereOne ⟶ H) :
    s ▷ (PointedCGWH.sphereOne ⊗ A) ≫
        (β_ (PointedCGWH.sphereOne ⊗ A) H).inv ≫
          (α_ PointedCGWH.sphereOne A H).hom =
      coefficientSwap A ≫ PointedCGWH.sphereOne ◁ (s ▷ A ≫ (β_ A H).inv) := by
  have h := MonoidalClosed.scalarOperatorInterchange_tensorSwapEvaluation
    PointedCGWH.sphereOne PointedCGWH.sphereOne A H (PointedCGWH.sphereOne ⊗ A) s (𝟙 _)
  have h' : PointedCGWH.sphereOne ◁ (s ▷ A ≫ (β_ A H).inv) ≫
      (α_ PointedCGWH.sphereOne A H).inv =
      coefficientSwap A ≫ s ▷ (PointedCGWH.sphereOne ⊗ A) ≫
        (β_ (PointedCGWH.sphereOne ⊗ A) H).inv := by
    simpa only [coefficientSwap, whiskerLeft_id, id_whiskerRight,
      Category.id_comp, Category.comp_id, Category.assoc] using h
  have h'' := congrArg (fun f => coefficientSwap A ≫ f ≫
    (α_ PointedCGWH.sphereOne A H).hom) h'
  have hs : coefficientSwap A ≫ coefficientSwap A = 𝟙 _ := coefficientSwap_comp_self A
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h''
  rw [← Category.assoc (coefficientSwap A) (coefficientSwap A), hs, Category.id_comp] at h''
  exact h''.symm

/-- The full actual scalar suspension successor retains the original coefficient swap and map. -/
theorem scalarSuspension_structureMap (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    (SuspensionGeometry.suspension.obj X).structureMap n =
      coefficientSwap (X.level n) ≫ PointedCGWH.sphereOne ◁ (X.structureMap n) := by
  let a := CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne n
  let b := CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne (n + 1)
  let H := a ⟶[PointedCGWH] b
  let A := X.level n
  let s := (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso
    PointedCGWH.sphereOne n).inv
  let e := CategoryTheory.Spectra.Sequential.action X a b
  let p := s ▷ (PointedCGWH.sphereOne ⊗ A) ≫
    (β_ (PointedCGWH.sphereOne ⊗ A) H).inv
  have ha := EnrichedFunctorCat.tensorLeftObject_map_uncurry PointedCGWH.sphereOne X a b
  have hp := congrArg (fun f => p ≫ f) ha
  have hc : p ≫ (α_ PointedCGWH.sphereOne A H).hom ≫ PointedCGWH.sphereOne ◁ e =
      coefficientSwap A ≫ PointedCGWH.sphereOne ◁ (s ▷ A ≫ (β_ A H).inv ≫ e) := by
    have h := congrArg (fun f => f ≫ PointedCGWH.sphereOne ◁ e)
      (scalarTensorSuccessorCoefficient A H s)
    simpa only [p, whiskerLeft_comp, Category.assoc] using h
  have hfinal := hp.trans hc
  simpa only [p, a, b, H, A, s, e, SuspensionGeometry.suspension,
    EnrichedFunctorCat.tensorLeft, EnrichedFunctorCat.tensorLeftObject,
    EnrichedFunctor.tensorLeft_obj, PointedCGWH.SequentialSpectrum.level,
    CategoryTheory.Spectra.Sequential.level, PointedCGWH.SequentialSpectrum.structureMap,
    CategoryTheory.Spectra.Sequential.structureMap, CategoryTheory.Spectra.Sequential.action,
    CategoryTheory.EnrichedCategory.Hom,
    CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory,
    tensorHom_id, Category.assoc] using hfinal

/-- The original spectrum-level suspension map is the complete actual space suspension map. -/
theorem suspensionGroupMap_eq_space (n k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (SuspensionGeometry.suspensionGroupMap n k).app X =
      (spaceSuspensionGroupMap k).app (X.level n) := by
  have hu := SuspensionGeometry.unit_levelMap X n
  have hc := MonoidalClosed.curry_id_eq_coev PointedCGWH.sphereOne (X.level n)
  have hm := congrArg (fun f => (piNPositiveFunctor k).map f) (hu.trans hc)
  have h := congrArg (fun f => f ≫
    (PointedCGWH.NativeLoopShiftGeometry.nativeLoopGroupShiftNatIso k).hom.app
      (PointedCGWH.sphereOne ⊗ X.level n)) hm
  exact (SuspensionGeometry.suspensionGroupMap_app n k X).trans
    (h.trans (spaceSuspensionGroupMap_app k (X.level n)).symm)

/-- The suspended spectrum transition is the negative original structure/suspension square. -/
theorem scalarSuspension_groupStructure_apply (n k : ℕ) (X : SequentialSpectrum.{u, v})
    (a : piN (k + 2) (PointedCGWH.sphereOne ⊗ X.level n)) :
    (((groupStructureNatTrans n (k + 1)).app (SuspensionGeometry.suspension.obj X)).hom a) =
      (((spaceSuspensionGroupMap (k + 1)).app (X.level (n + 1))).hom
        ((piNPositiveMap (k + 1) (X.structureMap n)).hom a))⁻¹ := by
  let Y := SuspensionGeometry.suspension.obj X
  let e := (spaceSuspensionGroupMap (k + 1)).app (PointedCGWH.sphereOne ⊗ X.level n)
  let t := piNPositiveMap (k + 2) (coefficientSwap (X.level n))
  let s := piNPositiveMap (k + 2) (PointedCGWH.sphereOne ◁ X.structureMap n)
  let f := piNPositiveMap (k + 1) (X.structureMap n)
  let d := (spaceSuspensionGroupMap (k + 1)).app (X.level (n + 1))
  have hfactor := congrArg (fun j => j.app Y)
    (SuspensionGeometry.suspensionGroupMap_comp_structure n (k + 1))
  have hfactor' : (SuspensionGeometry.suspensionGroupMap n (k + 1)).app Y ≫
      piNPositiveMap (k + 2) (Y.structureMap n) = (groupStructureNatTrans n (k + 1)).app Y :=
    hfactor
  have hstruct := (piNPositiveFunctor (k + 2)).congr_map (scalarSuspension_structureMap X n)
  rw [(piNPositiveFunctor (k + 2)).map_comp] at hstruct
  have hgroup : ((groupStructureNatTrans n (k + 1)).app Y).hom a =
      s.hom (t.hom (e.hom a)) := by
    rw [← hfactor', suspensionGroupMap_eq_space]
    exact congrArg (fun j => j.hom (e.hom a)) hstruct
  have hi : t.hom (e.hom a) = (e.hom a)⁻¹ :=
    coefficientSwap_suspensionImage (k + 1) (X.level n) a
  have hn := (spaceSuspensionGroupMap (k + 1)).naturality (X.structureMap n)
  have hn' : s.hom (e.hom a) = d.hom (f.hom a) :=
    (congrArg (fun j => j.hom a) hn).symm
  exact hgroup.trans ((congrArg s.hom hi).trans
    ((map_inv s.hom (e.hom a)).trans (congrArg Inv.inv hn')))

/-- Inversion is an actual homomorphism on the original groups in degrees at least two. -/
def positiveGroupInversion (k : ℕ) (A : PointedCGWH.{u, v}) :
    (piNPositiveFunctor (k + 1)).obj A ⟶ (piNPositiveFunctor (k + 1)).obj A := by
  let _ : CommGroup (piN (k + 2) A) := inferInstance
  exact GrpCat.ofHom
    { toFun := Inv.inv
      map_one' := inv_one
      map_mul' := fun a b => by rw [mul_inv_rev, mul_comm] }

/-- The entire original positive inversion family has both natural inverse maps. -/
def positiveGroupInversionNatIso (k : ℕ) :
    piNPositiveFunctor.{u, v} (k + 1) ≅ piNPositiveFunctor (k + 1) :=
  NatIso.ofComponents (fun A =>
    { hom := positiveGroupInversion k A
      inv := positiveGroupInversion k A
      hom_inv_id := by ext a; exact inv_inv a
      inv_hom_id := by ext a; exact inv_inv a }) (fun f => by
        ext a
        exact (map_inv (piNPositiveMap (k + 1) f).hom a).symm)

/-- Every entire original level group in degree at least two retains the same inversion Iso. -/
def levelPositiveInversionNatIso (n k : ℕ) :
    levelCubeGroupFunctor.{u, v} n (k + 1) ≅ levelCubeGroupFunctor n (k + 1) :=
  Functor.isoWhiskerLeft (CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne n)
    (positiveGroupInversionNatIso k)

/-- The complete original target degree transport retains its actual inversion comparison. -/
def stageTargetInversionNatIso (n m k : ℕ) :
    SuspensionGeometry.suspension.{u, v} ⋙ levelCubeGroupFunctor (m + n) ((k + 1) + n) ≅
      SuspensionGeometry.suspension ⋙ levelCubeGroupFunctor (m + n) ((k + 1) + n) :=
  Functor.isoWhiskerLeft SuspensionGeometry.suspension
    ((stageDegreeNatIso n m k).symm ≪≫
      levelPositiveInversionNatIso (m + n) (k + n) ≪≫ stageDegreeNatIso n m k)

/-- Every original transported inversion function is inversion of the same actual group element. -/
theorem stageTargetInversionNatIso_apply (n m k : ℕ) (X : SequentialSpectrum.{u, v})
    (a : (levelCubeGroupFunctor (m + n) ((k + 1) + n)).obj
      (SuspensionGeometry.suspension.obj X)) :
    ((stageTargetInversionNatIso n m k).hom.app X).hom a = a⁻¹ := by
  let c := (stageDegreeNatIso n m k).app (SuspensionGeometry.suspension.obj X)
  change c.hom.hom ((c.inv.hom a)⁻¹) = _
  rw [map_inv]
  have h := congrArg (fun f => f.hom a) c.inv_hom_id
  exact congrArg Inv.inv h

/-- The unsigned stage forward map keeps the actual scalar unit, native shift and original cast. -/
def unsignedStageForward (n m k : ℕ) : levelCubeGroupFunctor.{u, v} (m + n) (k + n) ⟶
    SuspensionGeometry.suspension ⋙ levelCubeGroupFunctor (m + n) ((k + 1) + n) :=
  SuspensionGeometry.suspensionGroupMap (m + n) (k + n) ≫
    Functor.whiskerLeft SuspensionGeometry.suspension (stageDegreeNatIso n m k).hom

/-- The actual signed stage forward map is induced by the original scalar unit and loop Iso. -/
def stageForward (n m k : ℕ) : levelCubeGroupFunctor.{u, v} (m + n) (k + n) ⟶
    SuspensionGeometry.suspension ⋙ levelCubeGroupFunctor (m + n) ((k + 1) + n) :=
  Functor.whiskerRight SuspensionGeometry.unit (levelCubeGroupFunctor (m + n) (k + n)) ≫
    (Functor.associator SuspensionGeometry.suspension SuspensionGeometry.loop
      (levelCubeGroupFunctor (m + n) (k + n))).hom ≫
        Functor.whiskerLeft SuspensionGeometry.suspension (signedStageShiftNatIso n m k).hom

/-- Every full forward stage component keeps the original unit group map and signed native shift. -/
theorem stageForward_app (n m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (stageForward n m k).app X =
      (levelCubeGroupFunctor (m + n) (k + n)).map (SuspensionGeometry.unit.app X) ≫
        (signedStageShiftNatIso n m k).hom.app (SuspensionGeometry.suspension.obj X) := by
  change _ ≫ 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  rfl

/-- The entire unsigned component is the same unit group map and original unsigned degree shift. -/
theorem unsignedStageForward_app (n m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (unsignedStageForward n m k).app X =
      (levelCubeGroupFunctor (m + n) (k + n)).map (SuspensionGeometry.unit.app X) ≫
        (unsignedStageShiftNatIso n m k).hom.app (SuspensionGeometry.suspension.obj X) := by
  change (SuspensionGeometry.suspensionGroupMap (m + n) (k + n)).app X ≫
    (stageDegreeNatIso n m k).hom.app (SuspensionGeometry.suspension.obj X) = _
  rw [SuspensionGeometry.suspensionGroupMap_app, unsignedStageShiftNatIso_hom_app]
  simp only [Category.assoc]
  rfl

/-- Every original even-stage forward component is the complete unsigned suspension map. -/
theorem stageForward_even (n m k : ℕ) (hn : n % 2 = 0) (X : SequentialSpectrum.{u, v}) :
    (stageForward n m k).app X = (unsignedStageForward n m k).app X := by
  rw [stageForward_app, signedStageShiftNatIso_hom_even n m k hn, unsignedStageForward_app]

/-- Each odd-stage forward function is the inverse of the unsigned suspension image. -/
theorem stageForward_odd_apply (n m k : ℕ) (hn : n % 2 ≠ 0) (X : SequentialSpectrum.{u, v})
    (a : (levelCubeGroupFunctor (m + n) (k + n)).obj X) :
    ((stageForward n m k).app X).hom a =
      (((unsignedStageForward n m k).app X).hom a)⁻¹ := by
  let u := (levelCubeGroupFunctor (m + n) (k + n)).map (SuspensionGeometry.unit.app X)
  let s := (unsignedStageShiftNatIso n m k).hom.app (SuspensionGeometry.suspension.obj X)
  have ha := congrArg (fun f => f.hom a) (stageForward_app n m k X)
  have hs := signedStageShiftNatIso_apply_odd n m k hn (SuspensionGeometry.suspension.obj X)
    (u.hom a)
  have hu := congrArg (fun f => f.hom a) (unsignedStageForward_app n m k X)
  exact ha.trans (hs.trans ((map_inv s.hom (u.hom a)).trans (congrArg Inv.inv hu.symm)))

/-- The actual reverse stage first uses the inverse original degree cast,
then the entire structure. -/
def unsignedStageBackward (n m k : ℕ) :
    SuspensionGeometry.suspension.{u, v} ⋙ levelCubeGroupFunctor (m + n) ((k + 1) + n) ⟶
      levelCubeGroupFunctor (m + (n + 1)) (k + (n + 1)) :=
  Functor.whiskerLeft SuspensionGeometry.suspension (stageDegreeNatIso n m k).inv ≫
    SuspensionGeometry.suspensionStructureGroupMap (m + n) (k + n)

/-- The full actual reverse stage alternates the same original group inversion. -/
def stageBackward (n m k : ℕ) :
    SuspensionGeometry.suspension.{u, v} ⋙ levelCubeGroupFunctor (m + n) ((k + 1) + n) ⟶
      levelCubeGroupFunctor (m + (n + 1)) (k + (n + 1)) :=
  if n % 2 = 0 then unsignedStageBackward n m k
  else (stageTargetInversionNatIso n m k).hom ≫ unsignedStageBackward n m k

/-- Every original even reverse stage is the actual unsigned structure/cast map. -/
theorem stageBackward_even (n m k : ℕ) (hn : n % 2 = 0) :
    stageBackward.{u, v} n m k = unsignedStageBackward n m k := by
  rw [stageBackward, ite_eq_left hn]

/-- Every original odd reverse stage applies the same structure/cast map to the inverse element. -/
theorem stageBackward_odd_apply (n m k : ℕ) (hn : n % 2 ≠ 0) (X : SequentialSpectrum.{u, v})
    (a : (levelCubeGroupFunctor (m + n) ((k + 1) + n)).obj
      (SuspensionGeometry.suspension.obj X)) :
    ((stageBackward n m k).app X).hom a = ((unsignedStageBackward n m k).app X).hom (a⁻¹) := by
  rw [stageBackward, ite_eq_right hn, NatTrans.comp_app]
  exact congrArg ((unsignedStageBackward n m k).app X).hom
    (stageTargetInversionNatIso_apply n m k X a)

/-- The unsigned stage pair factors the complete original varying-degree
structure transformation. -/
theorem unsignedStageForward_comp_backward (n m k : ℕ) :
    unsignedStageForward.{u, v} n m k ≫ unsignedStageBackward n m k =
      groupStructureNatTrans (m + n) (k + n) := by
  apply NatTrans.ext
  funext X
  change (SuspensionGeometry.suspensionGroupMap (m + n) (k + n)).app X ≫
      ((stageDegreeNatIso n m k).app (SuspensionGeometry.suspension.obj X)).hom ≫
      ((stageDegreeNatIso n m k).app (SuspensionGeometry.suspension.obj X)).inv ≫
      (SuspensionGeometry.suspensionStructureGroupMap (m + n) (k + n)).app X = _
  rw [Iso.hom_inv_id_assoc]
  exact congrArg (fun f => f.app X)
    (SuspensionGeometry.suspensionGroupMap_comp_structure (m + n) (k + n))

/-- Both entire signed stage maps factor the same original varying-degree structure map. -/
theorem stageForward_comp_backward (n m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (stageForward n m k).app X ≫ (stageBackward n m k).app X =
      (groupStructureNatTrans (m + n) (k + n)).app X := by
  by_cases hn : n % 2 = 0
  · rw [stageForward_even n m k hn X, stageBackward_even n m k hn]
    exact congrArg (fun f => f.app X) (unsignedStageForward_comp_backward n m k)
  · ext a
    let u := (unsignedStageForward n m k).app X
    let b := (unsignedStageBackward n m k).app X
    have ha := stageForward_odd_apply n m k hn X a
    have hb := stageBackward_odd_apply n m k hn X (((stageForward n m k).app X).hom a)
    have hc := congrArg (fun x => b.hom (x⁻¹)) ha
    have hu := congrArg (fun f => f.hom a)
      (congrArg (fun f => f.app X) (unsignedStageForward_comp_backward n m k))
    exact hb.trans (hc.trans ((congrArg b.hom (inv_inv (u.hom a))).trans hu))

/-- The complete unsigned forward component is the original space map and degree transport. -/
theorem unsignedStageForward_space (n m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (unsignedStageForward n m k).app X =
      (spaceSuspensionGroupMap (k + n)).app (X.level (m + n)) ≫
        (stageDegreeNatIso n m k).hom.app (SuspensionGeometry.suspension.obj X) := by
  change (SuspensionGeometry.suspensionGroupMap (m + n) (k + n)).app X ≫ _ = _
  rw [suspensionGroupMap_eq_space]
  rfl

/-- The complete unsigned reverse component keeps the inverse cast and original coefficient map. -/
theorem unsignedStageBackward_app (n m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (unsignedStageBackward n m k).app X =
      (stageDegreeNatIso n m k).inv.app (SuspensionGeometry.suspension.obj X) ≫
        piNPositiveMap (k + n + 1) (X.structureMap (m + n)) := rfl

private theorem groupStructure_degree_reindex (n a b : ℕ) (h : a = b)
    (X : SequentialSpectrum.{u, v}) :
    eqToHom (congrArg (fun j => (piNPositiveFunctor j).obj (X.level n)) h) ≫
        (groupStructureNatTrans n b).app X =
      (groupStructureNatTrans n a).app X ≫
        eqToHom (congrArg (fun j => (piNPositiveFunctor (j + 1)).obj (X.level (n + 1))) h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The actual stage degree casts preserve the full original varying-degree structure square. -/
theorem stageDegree_structure_transport (n m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (stageDegreeNatIso n m k).hom.app X ≫
        (groupStructureNatTrans (m + n) ((k + 1) + n)).app X =
      (groupStructureNatTrans (m + n) (k + n + 1)).app X ≫
        (stageDegreeNatIso (n + 1) m k).hom.app X := by
  rw [stageDegreeNatIso_hom_app, stageDegreeNatIso_hom_app]
  exact groupStructure_degree_reindex (m + n) (k + n + 1) ((k + 1) + n) (by omega) X

private theorem suspendedDiagonalTransition_reindex (n m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (diagonalTransition n m (k + 1)).app (SuspensionGeometry.suspension.obj X) =
      (stageDegreeNatIso n m k).inv.app (SuspensionGeometry.suspension.obj X) ≫
        (groupStructureNatTrans (m + n) (k + n + 1)).app (SuspensionGeometry.suspension.obj X) ≫
          (stageDegreeNatIso (n + 1) m k).hom.app (SuspensionGeometry.suspension.obj X) := by
  let Y := SuspensionGeometry.suspension.obj X
  let c := (stageDegreeNatIso n m k).app Y
  let d := (stageDegreeNatIso (n + 1) m k).app Y
  let g := (groupStructureNatTrans (m + n) ((k + 1) + n)).app Y
  let g₀ := (groupStructureNatTrans (m + n) (k + n + 1)).app Y
  have ht : c.hom ≫ g = g₀ ≫ d.hom := stageDegree_structure_transport n m k Y
  have h := congrArg (fun f => c.inv ≫ f) ht
  rw [← Category.assoc c.inv c.hom, c.inv_hom_id, Category.id_comp] at h
  exact (diagonalTransition_eq_structure n m (k + 1) Y).trans h

private theorem unsignedStageBackward_forward_next_explicit (n m k : ℕ)
    (X : SequentialSpectrum.{u, v})
    (a : (levelCubeGroupFunctor (m + n) ((k + 1) + n)).obj
      (SuspensionGeometry.suspension.obj X)) :
    ((unsignedStageForward (n + 1) m k).app X).hom
        (((unsignedStageBackward n m k).app X).hom a) =
      ((stageDegreeNatIso (n + 1) m k).hom.app (SuspensionGeometry.suspension.obj X)).hom
        (((spaceSuspensionGroupMap (k + n + 1)).app (X.level (m + n + 1))).hom
          ((piNPositiveMap (k + n + 1) (X.structureMap (m + n))).hom
            (((stageDegreeNatIso n m k).inv.app
              (SuspensionGeometry.suspension.obj X)).hom a))) := by
  let Y := SuspensionGeometry.suspension.obj X
  let c := (stageDegreeNatIso n m k).inv.app Y
  let s := piNPositiveMap (k + n + 1) (X.structureMap (m + n))
  have hb := congrArg (fun f => f.hom a) (unsignedStageBackward_app n m k X)
  have hu := congrArg (fun f => f.hom (s.hom (c.hom a)))
    (unsignedStageForward_space (n + 1) m k X)
  exact (congrArg ((unsignedStageForward (n + 1) m k).app X).hom hb).trans hu

private theorem suspendedDiagonalTransition_explicit (n m k : ℕ)
    (X : SequentialSpectrum.{u, v})
    (a : (levelCubeGroupFunctor (m + n) ((k + 1) + n)).obj
      (SuspensionGeometry.suspension.obj X)) :
    ((diagonalTransition n m (k + 1)).app (SuspensionGeometry.suspension.obj X)).hom a =
      (((stageDegreeNatIso (n + 1) m k).hom.app (SuspensionGeometry.suspension.obj X)).hom
        (((spaceSuspensionGroupMap (k + n + 1)).app (X.level (m + n + 1))).hom
          ((piNPositiveMap (k + n + 1) (X.structureMap (m + n))).hom
            (((stageDegreeNatIso n m k).inv.app
              (SuspensionGeometry.suspension.obj X)).hom a))))⁻¹ := by
  let Y := SuspensionGeometry.suspension.obj X
  let c := (stageDegreeNatIso n m k).inv.app Y
  let d := (stageDegreeNatIso (n + 1) m k).hom.app Y
  let s := piNPositiveMap (k + n + 1) (X.structureMap (m + n))
  let e := (spaceSuspensionGroupMap (k + n + 1)).app (X.level (m + n + 1))
  have hd := congrArg (fun f => f.hom a) (suspendedDiagonalTransition_reindex n m k X)
  have hn := scalarSuspension_groupStructure_apply (m + n) (k + n) X (c.hom a)
  exact hd.trans ((congrArg d.hom hn).trans
    (map_inv d.hom (e.hom (s.hom (c.hom a)))))

/-- The unsigned reverse/next-forward functions retain the actual negative suspended transition. -/
theorem unsignedStageBackward_forward_next (n m k : ℕ) (X : SequentialSpectrum.{u, v})
    (a : (levelCubeGroupFunctor (m + n) ((k + 1) + n)).obj
      (SuspensionGeometry.suspension.obj X)) :
    ((unsignedStageForward (n + 1) m k).app X).hom
        (((unsignedStageBackward n m k).app X).hom a) =
      (((diagonalTransition n m (k + 1)).app (SuspensionGeometry.suspension.obj X)).hom a)⁻¹ := by
  have hforward := unsignedStageBackward_forward_next_explicit n m k X a
  have hdiag := suspendedDiagonalTransition_explicit n m k X a
  exact hforward.trans (((congrArg Inv.inv hdiag).trans (inv_inv _)).symm)

/-- The signed reverse and next-forward maps give the complete original suspended transition. -/
theorem stageBackward_forward_next (n m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (stageBackward n m k).app X ≫ (stageForward (n + 1) m k).app X =
      (diagonalTransition n m (k + 1)).app (SuspensionGeometry.suspension.obj X) := by
  by_cases hn : n % 2 = 0
  · have hn' : (n + 1) % 2 ≠ 0 := by omega
    rw [stageBackward_even n m k hn]
    ext a
    have ha := stageForward_odd_apply (n + 1) m k hn' X
      (((unsignedStageBackward n m k).app X).hom a)
    have hu := unsignedStageBackward_forward_next n m k X a
    exact ha.trans ((congrArg Inv.inv hu).trans (inv_inv
      (((diagonalTransition n m (k + 1)).app (SuspensionGeometry.suspension.obj X)).hom a)))
  · have hn' : (n + 1) % 2 = 0 := by omega
    rw [stageForward_even (n + 1) m k hn' X]
    ext a
    let u := (unsignedStageForward (n + 1) m k).app X
    let b := (unsignedStageBackward n m k).app X
    have hb := stageBackward_odd_apply n m k hn X a
    have h₁ := congrArg u.hom hb
    have h₂ := congrArg u.hom (map_inv b.hom a)
    have h₃ := map_inv u.hom (b.hom a)
    have hu := unsignedStageBackward_forward_next n m k X a
    exact h₁.trans (h₂.trans (h₃.trans ((congrArg Inv.inv hu).trans (inv_inv
      (((diagonalTransition n m (k + 1)).app (SuspensionGeometry.suspension.obj X)).hom a)))))

/-- The forward/reverse pair is the actual first original diagonal successor map. -/
theorem stageForward_comp_backward_step (n m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (stageForward n m k).app X ≫ (stageBackward n m k).app X =
      ((diagonalDiagramFunctor m k).obj X).map (homOfLE (Nat.le_succ n)) :=
  (stageForward_comp_backward n m k X).trans
    ((diagonalTransition_eq_structure n m k X).symm.trans
      (diagonalDiagram_map_succ X m k n).symm)

/-- The reverse/next-forward pair is the actual original suspended diagonal successor map. -/
theorem stageBackward_forward_next_step (n m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (stageBackward n m k).app X ≫ (stageForward (n + 1) m k).app X =
      ((diagonalDiagramFunctor m (k + 1)).obj (SuspensionGeometry.suspension.obj X)).map
        (homOfLE (Nat.le_succ n)) :=
  (stageBackward_forward_next n m k X).trans
    (diagonalDiagram_map_succ (SuspensionGeometry.suspension.obj X) m (k + 1) n).symm

end PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStageGeometry
