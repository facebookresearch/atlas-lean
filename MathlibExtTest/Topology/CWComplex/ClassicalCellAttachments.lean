/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.CWComplex.ClassicalCellAttachments
import MathlibExt.AlgebraicTopology.SimplicialComplex.Realization

/-!
# Actual classical attachment and subcomplex-extension consumers

The constructed weak polyhedron supplies its actual Hausdorff classical CW
model. These consumers recover that model's successor pushout and original
quotients, then extend a prescribed homotopy on its entire zero skeleton.
The zero-dimensional boundary is empty and its disk remains a point.
-/

open CategoryTheory Limits Topology
open Topology.CWComplex

noncomputable section

universe u v

namespace ClassicalCWConsumer

variable {V : Type u}

abbrev polyhedron (P : PreAbstractSimplicialComplex V) : TopCat.{u} :=
  TopCat.of (PreAbstractSimplicialComplex.Realization P)

def zeroSkeleton (P : PreAbstractSimplicialComplex V) :
    Subcomplex (Set.univ : Set (polyhedron P)) := skeletonLT (Set.univ : Set (polyhedron P)) 1

example (P : PreAbstractSimplicialComplex V) (n : ℕ) :
    IsPushout (sphereSumToSkeleton (polyhedron P) n) (sphereSumToDiskSum (polyhedron P) n)
      (skeletonTransition (polyhedron P) n) (diskSumToSkeleton (polyhedron P) n) :=
  isPushout_skeletonAttachment _ _

example (P : PreAbstractSimplicialComplex V) :
    IsQuotientMap (characteristicQuotient (polyhedron P)) :=
  isQuotientMap_characteristicQuotient _

example (P : PreAbstractSimplicialComplex V) :
    IsQuotientMap (skeletalUnionQuotient (polyhedron P)) :=
  isQuotientMap_skeletalUnionQuotient _

def extendZeroSkeleton (P : PreAbstractSimplicialComplex V) {Y : Type v} [TopologicalSpace Y]
    (f : C(polyhedron P, Y)) (H : C(unitInterval × (zeroSkeleton P : Set (polyhedron P)), Y))
    (h0 : ∀ a : (zeroSkeleton P : Set (polyhedron P)), H (0, a) = f a.val) :
    HomotopyExtensionData (subcomplexInclusion (zeroSkeleton P)).hom f H h0 :=
  subcomplexHomotopyExtension _ _ _ _

example (P : PreAbstractSimplicialComplex V) {Y : Type v} [TopologicalSpace Y]
    (f : C(polyhedron P, Y)) (H : C(unitInterval × (zeroSkeleton P : Set (polyhedron P)), Y))
    (h0 : ∀ a : (zeroSkeleton P : Set (polyhedron P)), H (0, a) = f a.val)
    (x : polyhedron P) : (extendZeroSkeleton P f H h0).extension (0, x) = f x :=
  (extendZeroSkeleton P f H h0).extension_zero x

example (P : PreAbstractSimplicialComplex V) {Y : Type v} [TopologicalSpace Y]
    (f : C(polyhedron P, Y)) (H : C(unitInterval × (zeroSkeleton P : Set (polyhedron P)), Y))
    (h0 : ∀ a : (zeroSkeleton P : Set (polyhedron P)), H (0, a) = f a.val)
    (t : unitInterval) (a : (zeroSkeleton P : Set (polyhedron P))) :
    (extendZeroSkeleton P f H h0).extension (t, a.val) = H (t, a) :=
  (extendZeroSkeleton P f H h0).extension_subspace t a

example : IsEmpty (classicalCellDiskPair.{u} 0).snd := by
  change IsEmpty (ULift.{u} (Metric.sphere (0 : Fin 0 → ℝ) 1))
  infer_instance

example : Subsingleton (classicalCellDiskPair.{u} 0).fst := by
  change Subsingleton (ULift.{u} (Metric.closedBall (0 : Fin 0 → ℝ) 1))
  infer_instance

example (P : PreAbstractSimplicialComplex V) :
    TopCat.IsHurewiczCofibration (subcomplexInclusion (zeroSkeleton P)) :=
  subcomplexInclusion_isHurewiczCofibration _

end ClassicalCWConsumer

#print axioms Topology.CWComplex.isQuotientMap_characteristicQuotient
#print axioms Topology.CWComplex.skeletonPushoutIsColimit
#print axioms Topology.CWComplex.isPushout_skeletonAttachment
#print axioms Topology.CWComplex.isQuotientMap_skeletalUnionQuotient
#print axioms Topology.CWComplex.subcomplexHomotopyExtension
#print axioms Topology.CWComplex.subcomplexInclusion_hasHomotopyExtensionProperty
#print axioms ClassicalCWConsumer.extendZeroSkeleton

end
