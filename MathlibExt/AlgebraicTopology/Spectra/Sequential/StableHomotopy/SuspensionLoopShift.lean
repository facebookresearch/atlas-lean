/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.SuspensionUnit
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.IntegerColimitNormalization
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.DoubleLoopInterchange

/-!
# The actual scalar-loop degree shift on the original stable homotopy groups

The original scalar cotensor successor transpose includes the actual closed
coordinate interchange. Its action is inversion on the original double-loop
group. The original native degree shifts therefore anticommute with the actual
varying-degree transition. Alternating those same inversions gives the complete
diagram comparison and its actual maps on the original filtered group quotient.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionLoopShiftGeometry

open PointedCGWH.DoubleLoopInterchangeGeometry
open PointedCGWH.NativeLoopShiftGeometry
open PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.OrderedLoop.GroupUnitCoherenceGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.IntegerColimitNormalization
open HomotopicalAlgebra.EnrichedProjective.Native.SourceLoopClassTransport

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- Both native degree shifts preserve the complete negative coordinate-interchange square. -/
theorem loopGroupShift_interchange (k : ℕ) {A B : PointedCGWH.{u, v}}
    (f : A ⟶ PointedCGWH.loop.obj B) (a : piN (k + 1) (PointedCGWH.loop.obj A)) :
    ((nativeLoopGroupShiftNatIso (k + 1)).hom.app B).hom
        (((nativeLoopGroupShiftNatIso k).hom.app (PointedCGWH.loop.obj B)).hom
          ((piNPositiveMap k (PointedCGWH.loop.map f ≫ interchange B)).hom a)) =
      (((nativeLoopGroupShiftNatIso (k + 1)).hom.app B).hom
        ((piNPositiveMap (k + 1) f).hom
          (((nativeLoopGroupShiftNatIso k).hom.app A).hom a)))⁻¹ := by
  let P := piNPositiveFunctor.{u, v} k
  let S := (nativeLoopGroupShiftNatIso k).hom.app A
  let U := (nativeLoopGroupShiftNatIso k).hom.app (PointedCGWH.loop.obj B)
  let T := (nativeLoopGroupShiftNatIso (k + 1)).hom.app B
  let m := piNPositiveMap k (PointedCGWH.loop.map f)
  let j := piNPositiveMap (k + 1) f
  let τ := piNPositiveMap k (interchange B)
  have hs := (nativeLoopGroupShiftNatIso k).hom.naturality f
  have ha : U.hom (m.hom a) = j.hom (S.hom a) :=
    congrArg (fun g => g.hom a) hs
  have hp : piNPositiveMap k (PointedCGWH.loop.map f ≫ interchange B) =
      piNPositiveMap k (PointedCGWH.loop.map f) ≫ piNPositiveMap k (interchange B) :=
    P.map_comp _ _
  have hc : (piNPositiveMap k (PointedCGWH.loop.map f ≫ interchange B)).hom a =
      τ.hom (m.hom a) := congrArg (fun g => g.hom a) hp
  have hi : τ.hom (m.hom a) = (m.hom a)⁻¹ :=
    interchange_piNPositiveMap_eq_inv k B (m.hom a)
  calc
    _ = T.hom (U.hom (τ.hom (m.hom a))) :=
      congrArg (fun b => T.hom (U.hom b)) hc
    _ = T.hom (U.hom ((m.hom a)⁻¹)) :=
      congrArg (fun b => T.hom (U.hom b)) hi
    _ = (T.hom (U.hom (m.hom a)))⁻¹ := by rw [map_inv, map_inv]
    _ = _ := congrArg (fun b => (T.hom b)⁻¹) ha

/-- The original scalar-loop successor transpose retains its actual complete closed interchange. -/
theorem scalarLoop_adjointStructureMap (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    adjointStructureMap (SuspensionGeometry.loop.obj X) n =
      PointedCGWH.loop.map (adjointStructureMap X n) ≫ interchange (X.level (n + 1)) :=
  scalarLoopSequential_adjointStructureMap PointedCGWH.sphereOne X n

/-- The original scalar-loop group transition anticommutes with both complete native shifts. -/
theorem scalarLoop_groupStructure_shift_apply (n k : ℕ) (X : SequentialSpectrum.{u, v})
    (a : piN (k + 1) (PointedCGWH.loop.obj (X.level n))) :
    ((nativeLoopGroupShiftNatIso (k + 1)).hom.app (X.level (n + 1))).hom
        (((groupStructureNatTrans n k).app (SuspensionGeometry.loop.obj X)).hom a) =
      (((groupStructureNatTrans n (k + 1)).app X).hom
        (((nativeLoopGroupShiftNatIso k).hom.app (X.level n)).hom a))⁻¹ := by
  let Y := SuspensionGeometry.loop.obj X
  let f : X.level n ⟶ PointedCGWH.loop.obj (X.level (n + 1)) := adjointStructureMap X n
  let g : Y.level n ⟶ PointedCGWH.loop.obj (Y.level (n + 1)) := adjointStructureMap Y n
  let S := (nativeLoopGroupShiftNatIso k).hom.app (X.level n)
  let U := (nativeLoopGroupShiftNatIso k).hom.app (PointedCGWH.loop.obj (X.level (n + 1)))
  let T := (nativeLoopGroupShiftNatIso (k + 1)).hom.app (X.level (n + 1))
  let P := piNPositiveFunctor.{u, v} k
  let Q := piNPositiveFunctor.{u, v} (k + 1)
  have hσ : g = PointedCGWH.loop.map f ≫ interchange (X.level (n + 1)) :=
    scalarLoop_adjointStructureMap X n
  have hg : ((groupStructureNatTrans n k).app Y).hom a = U.hom ((P.map g).hom a) :=
    groupStructureNatTrans_app n k Y a
  have hx : ((groupStructureNatTrans n (k + 1)).app X).hom (S.hom a) =
      T.hom ((Q.map f).hom (S.hom a)) := groupStructureNatTrans_app n (k + 1) X (S.hom a)
  have hp : (P.map g).hom a =
      (P.map (PointedCGWH.loop.map f ≫ interchange (X.level (n + 1)))).hom a :=
    congrArg (fun j => (P.map j).hom a) hσ
  have h₁ := congrArg T.hom hg
  have h₂ := congrArg (fun b => T.hom (U.hom b)) hp
  have h₃ := loopGroupShift_interchange k
    (A := X.level n) (B := X.level (n + 1)) f a
  have h₄ := congrArg Inv.inv hx.symm
  simpa only [Y, S, T] using h₁.trans (h₂.trans (h₃.trans h₄))

/-- The original simultaneous successor index map is identity at its equal successor indexes. -/
theorem groupUnitIndexNatIso_hom_id (n m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (groupUnitIndexNatIso n m k).hom.app X = 𝟙 _ := by
  rw [groupUnitIndexNatIso_hom_app]
  change 𝟙 _ ≫ (piNPositiveFunctor (k + (n + 1))).map (𝟙 _) = 𝟙 _
  rw [(piNPositiveFunctor (k + (n + 1))).map_id, Category.id_comp]

/-- The entire original diagonal step retains the literal original varying-degree structure map. -/
theorem diagonalTransition_eq_structure (n m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (diagonalTransition n m k).app X = (groupStructureNatTrans (m + n) (k + n)).app X := by
  rw [diagonalTransition_app]
  exact (congrArg (fun j => (groupStructureNatTrans (m + n) (k + n)).app X ≫ j)
    (groupUnitIndexNatIso_hom_id n m k X)).trans (Category.comp_id _)

private theorem groupStructure_degree_reindex (n a b : ℕ) (h : a = b)
    (X : SequentialSpectrum.{u, v}) :
    eqToHom (congrArg (fun j => (piNPositiveFunctor j).obj (X.level n)) h) ≫
        (groupStructureNatTrans n b).app X =
      (groupStructureNatTrans n a).app X ≫
        eqToHom (congrArg (fun j => (piNPositiveFunctor (j + 1)).obj (X.level (n + 1))) h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The original degree shift uses the actual arithmetic equality at every original stage. -/
def stageDegreeNatIso (n m k : ℕ) :
    levelCubeGroupFunctor.{u, v} (m + n) (k + n + 1) ≅
      levelCubeGroupFunctor (m + n) ((k + 1) + n) :=
  eqToIso (congrArg (levelCubeGroupFunctor (m + n))
    (show k + n + 1 = (k + 1) + n by omega))

/-- Every complete stage degree map is the actual equality map on the original positive group. -/
theorem stageDegreeNatIso_hom_app (n m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (stageDegreeNatIso n m k).hom.app X =
      eqToHom (congrArg (fun j => (piNPositiveFunctor j).obj (X.level (m + n)))
        (show k + n + 1 = (k + 1) + n by omega)) :=
  eqToHom_app (congrArg (levelCubeGroupFunctor (m + n))
    (show k + n + 1 = (k + 1) + n by omega)) X

/-- The entire actual native group shift is followed by its original stage degree transport. -/
def unsignedStageShiftNatIso (n m k : ℕ) :
    SuspensionGeometry.loop.{u, v} ⋙ levelCubeGroupFunctor (m + n) (k + n) ≅
      levelCubeGroupFunctor (m + n) ((k + 1) + n) :=
  SuspensionGeometry.loopGroupEvaluationIso (m + n) (k + n) ≪≫ stageDegreeNatIso n m k

/-- Its full forward function retains the original native group shift and actual degree map. -/
theorem unsignedStageShiftNatIso_hom_app (n m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (unsignedStageShiftNatIso n m k).hom.app X =
      (nativeLoopGroupShiftNatIso (k + n)).hom.app (X.level (m + n)) ≫
        (stageDegreeNatIso n m k).hom.app X := by
  change (SuspensionGeometry.loopGroupEvaluationIso (m + n) (k + n)).hom.app X ≫ _ = _
  rw [SuspensionGeometry.loopGroupEvaluationIso_hom_app]

/-- Its full inverse function retains both original inverse maps in their actual order. -/
theorem unsignedStageShiftNatIso_inv_app (n m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (unsignedStageShiftNatIso n m k).inv.app X =
      (stageDegreeNatIso n m k).inv.app X ≫
        (SuspensionGeometry.loopGroupEvaluationIso (m + n) (k + n)).inv.app X := rfl

/-- Each original scalar-loop level group has its complete actual inversion isomorphism. -/
def levelLoopInversionNatIso (n k : ℕ) :
    SuspensionGeometry.loop.{u, v} ⋙ levelCubeGroupFunctor n k ≅
      SuspensionGeometry.loop ⋙ levelCubeGroupFunctor n k :=
  NatIso.ofComponents (fun X => (loopGroupInversionNatIso k).app (X.level n)) (fun f => by
    ext a
    exact (map_inv
      (((SuspensionGeometry.loop ⋙ levelCubeGroupFunctor n k).map f).hom) a).symm)

/-- Every full inversion component is literal inversion on the original scalar-loop group. -/
theorem levelLoopInversionNatIso_hom_apply (n k : ℕ) (X : SequentialSpectrum.{u, v})
    (a : piN (k + 1) (PointedCGWH.loop.obj (X.level n))) :
    ((levelLoopInversionNatIso n k).hom.app X).hom a = a⁻¹ := rfl

/-- The actual signed comparison uses the original inversion exactly in the odd original stages. -/
def signedStageShiftNatIso (n m k : ℕ) :
    SuspensionGeometry.loop.{u, v} ⋙ levelCubeGroupFunctor (m + n) (k + n) ≅
      levelCubeGroupFunctor (m + n) ((k + 1) + n) :=
  if n % 2 = 0 then unsignedStageShiftNatIso n m k
  else levelLoopInversionNatIso (m + n) (k + n) ≪≫ unsignedStageShiftNatIso n m k

/-- Every even original stage retains the full unsigned native shift and original degree map. -/
theorem signedStageShiftNatIso_hom_even (n m k : ℕ) (h : n % 2 = 0)
    (X : SequentialSpectrum.{u, v}) :
    (signedStageShiftNatIso n m k).hom.app X =
      (unsignedStageShiftNatIso n m k).hom.app X := by
  rw [signedStageShiftNatIso, ite_eq_left h]

/-- Every odd stage retains the complete actual inversion before its original native shift. -/
theorem signedStageShiftNatIso_hom_odd (n m k : ℕ) (h : n % 2 ≠ 0)
    (X : SequentialSpectrum.{u, v}) :
    (signedStageShiftNatIso n m k).hom.app X =
      (levelLoopInversionNatIso (m + n) (k + n)).hom.app X ≫
        (unsignedStageShiftNatIso n m k).hom.app X := by
  rw [signedStageShiftNatIso, ite_eq_right h]
  rfl

/-- Every complete even-stage function is the actual unsigned original comparison function. -/
theorem signedStageShiftNatIso_apply_even (n m k : ℕ) (h : n % 2 = 0)
    (X : SequentialSpectrum.{u, v})
    (a : piN (k + n + 1) (PointedCGWH.loop.obj (X.level (m + n)))) :
    ((signedStageShiftNatIso n m k).hom.app X).hom a =
      ((unsignedStageShiftNatIso n m k).hom.app X).hom a :=
  congrArg (fun f => f.hom a) (signedStageShiftNatIso_hom_even n m k h X)

/-- Every complete odd-stage function is the actual original comparison after literal inversion. -/
theorem signedStageShiftNatIso_apply_odd (n m k : ℕ) (h : n % 2 ≠ 0)
    (X : SequentialSpectrum.{u, v})
    (a : piN (k + n + 1) (PointedCGWH.loop.obj (X.level (m + n)))) :
    ((signedStageShiftNatIso n m k).hom.app X).hom a =
      ((unsignedStageShiftNatIso n m k).hom.app X).hom (a⁻¹) := by
  rw [signedStageShiftNatIso_hom_odd n m k h X]
  rfl

/-- All actual original diagonal transitions retain the negative native-shift
square and its casts. -/
theorem unsignedStageShift_transition_apply (n m k : ℕ) (X : SequentialSpectrum.{u, v})
    (a : piN (k + n + 1) (PointedCGWH.loop.obj (X.level (m + n)))) :
    ((unsignedStageShiftNatIso (n + 1) m k).hom.app X).hom
        (((diagonalTransition n m k).app (SuspensionGeometry.loop.obj X)).hom a) =
      (((diagonalTransition n m (k + 1)).app X).hom
        (((unsignedStageShiftNatIso n m k).hom.app X).hom a))⁻¹ := by
  let Y := SuspensionGeometry.loop.obj X
  let S := (nativeLoopGroupShiftNatIso (k + n)).hom.app (X.level (m + n))
  let T := (nativeLoopGroupShiftNatIso (k + n + 1)).hom.app (X.level (m + n + 1))
  let c := (stageDegreeNatIso n m k).hom.app X
  let d := (stageDegreeNatIso (n + 1) m k).hom.app X
  let g := (groupStructureNatTrans (m + n) (k + n)).app Y
  let h := (groupStructureNatTrans (m + n) (k + n + 1)).app X
  let j := (groupStructureNatTrans (m + n) ((k + 1) + n)).app X
  have hc : c = eqToHom
      (congrArg (fun b => (piNPositiveFunctor b).obj (X.level (m + n)))
        (show k + n + 1 = (k + 1) + n by omega)) := stageDegreeNatIso_hom_app n m k X
  have hd : d = eqToHom
      (congrArg (fun b => (piNPositiveFunctor (b + 1)).obj (X.level (m + n + 1)))
        (show k + n + 1 = (k + 1) + n by omega)) :=
    stageDegreeNatIso_hom_app (n + 1) m k X
  have hcj : c ≫ j = h ≫ d := by
    rw [hc, hd]
    exact groupStructure_degree_reindex (m + n) (k + n + 1) ((k + 1) + n)
      (show k + n + 1 = (k + 1) + n by omega) X
  have hr : j.hom (c.hom (S.hom a)) = d.hom (h.hom (S.hom a)) :=
    congrArg (fun f => f.hom (S.hom a)) hcj
  have hseed := scalarLoop_groupStructure_shift_apply (m + n) (k + n) X a
  have hs : T.hom (g.hom a) = (h.hom (S.hom a))⁻¹ := by
    simpa only [Y, S, T, g, h] using hseed
  have hsrc : ((unsignedStageShiftNatIso (n + 1) m k).hom.app X).hom
      (((diagonalTransition n m k).app Y).hom a) = d.hom (T.hom (g.hom a)) := by
    rw [unsignedStageShiftNatIso_hom_app, diagonalTransition_eq_structure]
    rfl
  have htgt : ((diagonalTransition n m (k + 1)).app X).hom
      (((unsignedStageShiftNatIso n m k).hom.app X).hom a) = j.hom (c.hom (S.hom a)) := by
    rw [unsignedStageShiftNatIso_hom_app, diagonalTransition_eq_structure]
    rfl
  have h₁ := congrArg d.hom hs
  have h₂ : d.hom ((h.hom (S.hom a))⁻¹) = (d.hom (h.hom (S.hom a)))⁻¹ :=
    map_inv d.hom _
  have h₃ := congrArg Inv.inv hr.symm
  have h₄ := congrArg Inv.inv htgt.symm
  have hfinal := hsrc.trans (h₁.trans (h₂.trans (h₃.trans h₄)))
  simpa only [Y] using hfinal

/-- The complete signed original shifts commute with every actual successor transition. -/
theorem signedStageShift_transition (n m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (diagonalTransition n m k).app (SuspensionGeometry.loop.obj X) ≫
        (signedStageShiftNatIso (n + 1) m k).hom.app X =
      (signedStageShiftNatIso n m k).hom.app X ≫ (diagonalTransition n m (k + 1)).app X := by
  ext a
  have hu := unsignedStageShift_transition_apply n m k X a
  let l := (diagonalTransition n m k).app (SuspensionGeometry.loop.obj X)
  let r := (diagonalTransition n m (k + 1)).app X
  let s := (unsignedStageShiftNatIso n m k).hom.app X
  let t := (unsignedStageShiftNatIso (n + 1) m k).hom.app X
  by_cases hn : n % 2 = 0
  · have hn' : (n + 1) % 2 ≠ 0 := by omega
    have hnxt := signedStageShiftNatIso_apply_odd (n + 1) m k hn' X (l.hom a)
    have hcur := signedStageShiftNatIso_apply_even n m k hn X a
    have hi := map_inv t.hom (l.hom a)
    have hneg := congrArg Inv.inv hu
    exact hnxt.trans (hi.trans (hneg.trans
      ((inv_inv (r.hom (s.hom a))).trans (congrArg r.hom hcur.symm))))
  · have hn' : (n + 1) % 2 = 0 := by omega
    have hnxt := signedStageShiftNatIso_apply_even (n + 1) m k hn' X (l.hom a)
    have hcur := signedStageShiftNatIso_apply_odd n m k hn X a
    have hi := (map_inv r.hom (s.hom a)).symm
    have hs := congrArg r.hom (map_inv s.hom a).symm
    exact hnxt.trans (hu.trans (hi.trans (hs.trans (congrArg r.hom hcur.symm))))

/-- The complete original scalar-loop diagonal comparison retains all original successor maps. -/
def scalarLoopDiagonalNatTrans (m k : ℕ) :
    SuspensionGeometry.loop.{u, v} ⋙ diagonalDiagramFunctor m k ⟶
      diagonalDiagramFunctor m (k + 1) where
  app X := NatTrans.ofSequence (fun n => (signedStageShiftNatIso n m k).hom.app X)
    (fun n => by
      have hs : ((SuspensionGeometry.loop ⋙ diagonalDiagramFunctor m k).obj X).map
          (homOfLE (Nat.le_succ n)) =
        (diagonalTransition n m k).app (SuspensionGeometry.loop.obj X) :=
        diagonalDiagram_map_succ (SuspensionGeometry.loop.obj X) m k n
      have ht : ((diagonalDiagramFunctor m (k + 1)).obj X).map
          (homOfLE (Nat.le_succ n)) = (diagonalTransition n m (k + 1)).app X :=
        diagonalDiagram_map_succ X m (k + 1) n
      exact (congrArg (fun f => f ≫ (signedStageShiftNatIso (n + 1) m k).hom.app X) hs).trans
        ((signedStageShift_transition n m k X).trans
          (congrArg (fun f => (signedStageShiftNatIso n m k).hom.app X ≫ f) ht.symm)))
  naturality {X Y} f := by
    apply NatTrans.ext
    funext n
    exact (signedStageShiftNatIso n m k).hom.naturality f

/-- Every original finite-index map is retained by the genuine signed diagonal isomorphism. -/
def scalarLoopDiagonalNatIso (m k : ℕ) :
    SuspensionGeometry.loop.{u, v} ⋙ diagonalDiagramFunctor m k ≅
      diagonalDiagramFunctor m (k + 1) :=
  NatIso.ofComponents (fun X => NatIso.ofComponents
    (fun n => (signedStageShiftNatIso n m k).app X)
    (fun f => ((scalarLoopDiagonalNatTrans m k).app X).naturality f)) (fun f => by
      apply NatTrans.ext
      funext n
      exact (signedStageShiftNatIso n m k).hom.naturality f)

/-- Each complete original diagonal component is the same signed original stage isomorphism. -/
theorem scalarLoopDiagonalNatIso_app_app (m k : ℕ) (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    ((scalarLoopDiagonalNatIso m k).app X).app n = (signedStageShiftNatIso n m k).app X := rfl

/-- The forward comparison retains every actual original finite-index map. -/
@[reassoc]
theorem scalarLoopDiagonalNatIso_hom_index_naturality (m k : ℕ)
    (X : SequentialSpectrum.{u, v}) {i j : ℕ} (f : i ⟶ j) :
    (diagonalDiagram (SuspensionGeometry.loop.obj X) m k).map f ≫
        (signedStageShiftNatIso j m k).hom.app X =
      (signedStageShiftNatIso i m k).hom.app X ≫ (diagonalDiagram X m (k + 1)).map f :=
  ((scalarLoopDiagonalNatIso m k).hom.app X).naturality f

/-- The inverse comparison retains every actual original finite-index map. -/
@[reassoc]
theorem scalarLoopDiagonalNatIso_inv_index_naturality (m k : ℕ)
    (X : SequentialSpectrum.{u, v}) {i j : ℕ} (f : i ⟶ j) :
    (diagonalDiagram X m (k + 1)).map f ≫ (signedStageShiftNatIso j m k).inv.app X =
      (signedStageShiftNatIso i m k).inv.app X ≫
        (diagonalDiagram (SuspensionGeometry.loop.obj X) m k).map f :=
  ((scalarLoopDiagonalNatIso m k).inv.app X).naturality f

/-- The actual filtered group quotient carries both complete original signed diagonal maps. -/
def scalarLoopColimitNatIso (m k : ℕ) :
    SuspensionGeometry.loop.{u, v} ⋙ diagonalColimitFunctor m k ≅
      diagonalColimitFunctor m (k + 1) :=
  (Functor.associator SuspensionGeometry.loop (diagonalDiagramFunctor m k)
    GrpCat.FilteredColimits.colimitFunctor).symm ≪≫
      Functor.isoWhiskerRight (scalarLoopDiagonalNatIso m k) GrpCat.FilteredColimits.colimitFunctor

/-- The full forward function is the original induced map of actual filtered group quotients. -/
theorem scalarLoopColimitNatIso_hom_app (m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (scalarLoopColimitNatIso m k).hom.app X =
      GrpCat.FilteredColimits.colimitMap ((scalarLoopDiagonalNatIso m k).hom.app X) := by
  change 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  rfl

/-- The full inverse function is the original induced map of the inverse signed diagram. -/
theorem scalarLoopColimitNatIso_inv_app (m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (scalarLoopColimitNatIso m k).inv.app X =
      GrpCat.FilteredColimits.colimitMap ((scalarLoopDiagonalNatIso m k).inv.app X) := by
  change _ ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

/-- Every full forward quotient leg retains its actual original signed native stage map. -/
@[reassoc]
theorem scalarLoopColimitNatIso_hom_leg (m k : ℕ) (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    diagonalLeg m k (SuspensionGeometry.loop.obj X) n ≫
        (scalarLoopColimitNatIso m k).hom.app X =
      (signedStageShiftNatIso n m k).hom.app X ≫ diagonalLeg m (k + 1) X n := by
  rw [scalarLoopColimitNatIso_hom_app]
  exact GrpCat.FilteredColimits.colimitMap_ι ((scalarLoopDiagonalNatIso m k).hom.app X) n

/-- Every full inverse quotient leg retains its actual original inverse signed native stage map. -/
@[reassoc]
theorem scalarLoopColimitNatIso_inv_leg (m k : ℕ) (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    diagonalLeg m (k + 1) X n ≫ (scalarLoopColimitNatIso m k).inv.app X =
      (signedStageShiftNatIso n m k).inv.app X ≫
        diagonalLeg m k (SuspensionGeometry.loop.obj X) n := by
  rw [scalarLoopColimitNatIso_inv_app]
  exact GrpCat.FilteredColimits.colimitMap_ι ((scalarLoopDiagonalNatIso m k).inv.app X) n

/-- The original canonical starting indexes gain exactly one original integer degree. -/
theorem scalarLoop_integerDegree (q : ℤ) :
    integerDegree (integerTailLevel q) (integerTailPositiveIndex q + 1) = q + 1 := by
  have h := integerDegree_canonical q
  simp only [integerDegree] at h ⊢
  omega

/-- The full original scalar-loop shift in every integer degree has both genuine natural maps. -/
def scalarLoopIntegerPiNatIso (q : ℤ) :
    SuspensionGeometry.loop.{u, v} ⋙ integerStablePiFunctor q ≅ integerStablePiFunctor (q + 1) :=
  scalarLoopColimitNatIso (integerTailLevel q) (integerTailPositiveIndex q) ≪≫
    integerColimitNatIso (integerTailLevel q) (integerTailPositiveIndex q + 1) ≪≫
      eqToIso (congrArg integerStablePiFunctor (scalarLoop_integerDegree q))

end PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionLoopShiftGeometry
