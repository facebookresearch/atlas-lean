/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Quasicategory.Opposite
public import MathlibExt.AlgebraicTopology.SimplicialSet.LeftFibrationEquivalence
public import Mathlib.CategoryTheory.LiftingProperties.Limits

/-!
# Right fibrations and actual equivalence reflection

Right fibrations lift every positive horn whose missing face is not the
first face. Opposite transports these original horn squares to the
existing left-fibration API. In particular the source is a quasicategory
when the target is, and equivalences are reflected by the original map.
The native opposite edge retains its actual simplex and both endpoints.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SSet

/-- The original right-horn lifting condition, including one-dimensional right horns. -/
class RightFibration {X Y : SSet.{u}} (p : X ⟶ Y) : Prop where
  /-- Every original horn with a strictly positive missing-face index lifts. -/
  hasLiftingProperty_horn {n : ℕ} (i : Fin (n + 1)) (hi : 0 < i) :
    HasLiftingProperty (horn n i).ι p

/-- A right fibration has the original inner-horn lifting property. -/
instance RightFibration.innerFibration {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p] :
    InnerFibration p := by
  constructor
  intro A B i hi
  obtain @⟨n, k, h0, hn⟩ := hi
  exact RightFibration.hasLiftingProperty_horn k h0

/-- Base change retains each original right-horn lifting square. -/
instance RightFibration.pullback_fst {X Y Z : SSet.{u}} (g : Z ⟶ Y) (p : X ⟶ Y)
    [RightFibration p] : RightFibration (pullback.fst g p) where
  hasLiftingProperty_horn i hi := by
    have h : HasLiftingProperty (horn _ i).ι p :=
      RightFibration.hasLiftingProperty_horn i hi
    infer_instance

/-- Opposite sends each original right-horn square to the existing left-horn square. -/
instance RightFibration.leftFibration_op {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p] :
    LeftFibration (opFunctor.map p) := by
  apply leftFibration_of_hasLiftingProperty_horn
  intro n i hi
  have hr : 0 < i.rev := by
    rw [Fin.lt_def] at hi ⊢
    simp only [Fin.val_rev, Fin.val_zero, Fin.val_last] at hi ⊢
    omega
  have hbase : HasLiftingProperty (horn n i.rev).ι p :=
    RightFibration.hasLiftingProperty_horn i.rev hr
  have hm : HasLiftingProperty (opFunctor.map (horn n i.rev).ι) (opFunctor.map p) := by
    change HasLiftingProperty (SSet.opEquivalence.functor.map (horn n i.rev).ι)
      (SSet.opEquivalence.functor.map p)
    rw [CategoryTheory.Functor.hasLiftingProperty_iff_of_isEquivalence SSet.opEquivalence.functor]
    exact hbase
  have h : HasLiftingProperty (horn n i.rev.rev).ι (opFunctor.map p) :=
    (HasLiftingProperty.iff_of_arrow_iso_left (horn.opArrowIso n i.rev) (opFunctor.map p)).mp hm
  have hrev : i.rev.rev = i := Fin.rev_rev i
  rw [hrev] at h
  exact h

/-- The source of a right fibration with a quasicategory target is a quasicategory. -/
theorem quasicategory_of_rightFibration {X Y : SSet.{u}} (p : X ⟶ Y)
    [RightFibration p] [Quasicategory Y] : Quasicategory X :=
  quasicategory_of_innerFibration p

/-- A right fibration with quasicategory target reflects actual equivalence edges. -/
theorem RightFibration.isEquivalence_of_map {X Y : SSet.{u}} {p : X ⟶ Y}
    [RightFibration p] [Quasicategory Y] {x y : X _⦋0⦌} {e : Edge x y}
    (h : (e.map p).IsEquivalence) : e.IsEquivalence := by
  have hx : Quasicategory X := quasicategory_of_rightFibration p
  have hyop : Quasicategory Y.op := quasicategory_op Y
  have hyop' : Quasicategory (opFunctor.obj Y) := hyop
  have hxop : Quasicategory X.op := quasicategory_op X
  have he : ((e.op).map (opFunctor.map p)).edge = ((e.map p).op).edge := rfl
  have hop : ((e.op).map (opFunctor.map p)).IsEquivalence :=
    (Edge.isEquivalence_iff_of_edge_eq he).mpr h.op
  have hsource : e.op.IsEquivalence := LeftFibration.isEquivalence_of_map hop
  have hout : e.op.unop.IsEquivalence := hsource.unop
  exact (Edge.isEquivalence_iff_of_edge_eq (show e.op.unop.edge = e.edge from rfl)).mp hout

end SSet
