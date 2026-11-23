/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.KSpaceNatIsoUnitTrace
public import MathlibExt.Topology.Homotopy.HomotopyGroupMap
public import MathlibExt.Topology.Homotopy.TopCat.HomotopyTraceAction

/-!
# Actual maps on every original Quillen K-space homotopy-group carrier

The original continuous functor map is postcomposed on each original cube.
Positive degrees use basepoint transport along the original root unit contraction.
Degree zero uses the original path component map.
No convenience loop unit, new pointed model or trivial fundamental-group action
is assumed. Identity/composition and full additivity transports remain further
proof obligations.
-/

public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open scoped Topology Topology.Homotopy

universe uC vC uD vD uX uY

namespace AlgebraicKTheory

private def originalIndependentZerothMap
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : ZerothHomotopy X → ZerothHomotopy Y :=
  ZerothHomotopy.lift (fun x => ZerothHomotopy.mk (f x))
    (fun {_ _} p => ZerothHomotopy.sound (p.map f.continuous))

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

/-- EXACT original stock positive group data at any actual K-space point;
used locally, without installing a global instance or changing its law. -/
def NQKSpaceOriginalPositiveGroup
    (E : Type uC) [Category.{vC} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
    (n : ℕ) (x : NQKSpace E) : Group (HomotopyGroup.Pi (n + 1) (NQKSpace E) x) :=
  HomotopyGroup.group (X := NQKSpace E) (x := x) (Fin (n + 1))

private theorem originalPositiveGroupValueComputed
    (E : Type uC) [Category.{vC} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
    (n : ℕ) (x : NQKSpace E) :
    NQKSpaceOriginalPositiveGroup E n x =
      HomotopyGroup.group (X := NQKSpace E) (x := x) (Fin (n + 1)) := rfl

/-- The named original positive group is the same complete stock group structure. -/
theorem NQKSpaceOriginalPositiveGroup_value
    (E : Type uC) [Category.{vC} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
    (n : ℕ) (x : NQKSpace E) :
    NQKSpaceOriginalPositiveGroup E n x =
      HomotopyGroup.group (X := NQKSpace E) (x := x) (Fin (n + 1)) :=
  originalPositiveGroupValueComputed E n x

/-- The root unit contraction for the original K-space functor map, built from
its path from the mapped zero point to the chosen zero point. -/
def NQKSpaceFunctorKiUnitRootPath
    (F : C ⥤ D) [F.Additive] [F.IsExact] :
    Path ((NQKSpaceFunctorMap F) (Path.refl (NQReal.basepoint C)))
      (Path.refl (NQReal.basepoint D)) :=
  ((ContinuousMap.rootUnitContraction
    (fun p : Path ((NQRealFunctorWeaklyPointed F).hom (NQReal.basepoint C))
      (NQReal.basepoint D) => p) continuous_eval).evalAt
        (NQRealFunctorWeaklyPointed F).rootPath).cast
          (NQKSpaceFunctorMap_unit_eq_rootUnitLoopFamily F) rfl

/-- Every positive original K-space homotopy group is mapped by its actual cube
map then SAME original root-unit transport. All carrier worlds remain independent. -/
def NQKSpaceFunctorPositiveKiMap
    (F : C ⥤ D) [F.Additive] [F.IsExact] (n : ℕ) :
    letI := NQKSpaceOriginalPositiveGroup C n (Path.refl (NQReal.basepoint C))
    letI := NQKSpaceOriginalPositiveGroup D n (Path.refl (NQReal.basepoint D))
    HomotopyGroup.Pi (n + 1) (NQKSpace C) (Path.refl (NQReal.basepoint C)) →*
      HomotopyGroup.Pi (n + 1) (NQKSpace D) (Path.refl (NQReal.basepoint D)) :=
  by
    letI := NQKSpaceOriginalPositiveGroup C n (Path.refl (NQReal.basepoint C))
    letI := NQKSpaceOriginalPositiveGroup D n (Path.refl (NQReal.basepoint D))
    letI := NQKSpaceOriginalPositiveGroup D n
      (NQKSpaceFunctorMap F (Path.refl (NQReal.basepoint C)))
    letI : Group (HomotopyGroup.Pi (n + 1) (TopCat.of (NQKSpace D))
      (Path.refl (NQReal.basepoint D))) :=
      HomotopyGroup.group (X := TopCat.of (NQKSpace D))
        (x := Path.refl (NQReal.basepoint D)) (Fin (n + 1))
    letI : Group (HomotopyGroup.Pi (n + 1) (TopCat.of (NQKSpace D))
      (NQKSpaceFunctorMap F (Path.refl (NQReal.basepoint C)))) :=
      HomotopyGroup.group (X := TopCat.of (NQKSpace D))
        (x := NQKSpaceFunctorMap F (Path.refl (NQReal.basepoint C))) (Fin (n + 1))
    exact (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of (NQKSpace D))
      (NQKSpaceFunctorKiUnitRootPath F)).toMonoidHom.comp
        (HomotopyGroup.mapHom (NQKSpaceFunctorMap F))

/-- The all-degree map on the ORIGINAL cube-based K-space carriers, including degree zero.
The source/target objects, points and original functor maps are unchanged. -/
def NQKSpaceFunctorKiMap
    (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (n : ℕ) → HomotopyGroup.Pi n (NQKSpace C) (Path.refl (NQReal.basepoint C)) →
      HomotopyGroup.Pi n (NQKSpace D) (Path.refl (NQReal.basepoint D))
  | 0 => fun a =>
      (HomotopyGroup.pi0EquivZerothHomotopy
        (X := NQKSpace D) (x := Path.refl (NQReal.basepoint D))).symm
          (originalIndependentZerothMap (NQKSpaceFunctorMap F)
            (HomotopyGroup.pi0EquivZerothHomotopy
              (X := NQKSpace C) (x := Path.refl (NQReal.basepoint C)) a))
  | n + 1 => NQKSpaceFunctorPositiveKiMap F n

private theorem originalKFunctorKiMapSuccValueComputed
    (F : C ⥤ D) [F.Additive] [F.IsExact] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (NQKSpace C) (Path.refl (NQReal.basepoint C))) :
    NQKSpaceFunctorKiMap F (n + 1) a =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of (NQKSpace D))
        (NQKSpaceFunctorKiUnitRootPath F) (HomotopyGroup.map (NQKSpaceFunctorMap F) a) := by
  change NQKSpaceFunctorPositiveKiMap F n a = _
  rfl



/-- Every original positive cube class uses the SAME actual map and root transport. -/
theorem NQKSpaceFunctorKiMap_succ_apply
    (F : C ⥤ D) [F.Additive] [F.IsExact] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (NQKSpace C) (Path.refl (NQReal.basepoint C))) :
    NQKSpaceFunctorKiMap F (n + 1) a =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of (NQKSpace D))
        (NQKSpaceFunctorKiUnitRootPath F) (HomotopyGroup.map (NQKSpaceFunctorMap F) a) :=
  originalKFunctorKiMapSuccValueComputed F n a

/-- Positive degrees preserve the target's OWN original constant-cube group unit. -/
theorem NQKSpaceFunctorPositiveKiMap_one
    (F : C ⥤ D) [F.Additive] [F.IsExact] (n : ℕ) :
    letI := NQKSpaceOriginalPositiveGroup C n (Path.refl (NQReal.basepoint C))
    letI := NQKSpaceOriginalPositiveGroup D n (Path.refl (NQReal.basepoint D))
    NQKSpaceFunctorPositiveKiMap F n
      (1 : HomotopyGroup.Pi (n + 1) (NQKSpace C) (Path.refl (NQReal.basepoint C))) =
        (1 : HomotopyGroup.Pi (n + 1) (NQKSpace D) (Path.refl (NQReal.basepoint D))) := by
  letI := NQKSpaceOriginalPositiveGroup C n (Path.refl (NQReal.basepoint C))
  letI := NQKSpaceOriginalPositiveGroup D n (Path.refl (NQReal.basepoint D))
  exact (NQKSpaceFunctorPositiveKiMap F n).map_one

/-- Positive degrees preserve the existing original cube-concatenation group law. -/
theorem NQKSpaceFunctorPositiveKiMap_mul
    (F : C ⥤ D) [F.Additive] [F.IsExact] (n : ℕ)
    (a b : HomotopyGroup.Pi (n + 1) (NQKSpace C) (Path.refl (NQReal.basepoint C))) :
    letI := NQKSpaceOriginalPositiveGroup C n (Path.refl (NQReal.basepoint C))
    letI := NQKSpaceOriginalPositiveGroup D n (Path.refl (NQReal.basepoint D))
    NQKSpaceFunctorPositiveKiMap F n (a * b) =
      NQKSpaceFunctorPositiveKiMap F n a * NQKSpaceFunctorPositiveKiMap F n b := by
  letI := NQKSpaceOriginalPositiveGroup C n (Path.refl (NQReal.basepoint C))
  letI := NQKSpaceOriginalPositiveGroup D n (Path.refl (NQReal.basepoint D))
  exact (NQKSpaceFunctorPositiveKiMap F n).map_mul a b

/-- The all-degree zero map is on the same original path components, not a new K0 model. -/
theorem NQKSpaceFunctorKiMap_zero_components
    (F : C ⥤ D) [F.Additive] [F.IsExact]
    (a : HomotopyGroup.Pi 0 (NQKSpace C) (Path.refl (NQReal.basepoint C))) :
    HomotopyGroup.pi0EquivZerothHomotopy
        (X := NQKSpace D) (x := Path.refl (NQReal.basepoint D)) (NQKSpaceFunctorKiMap F 0 a) =
      ZerothHomotopy.lift
        (fun x : NQKSpace C => ZerothHomotopy.mk ((NQKSpaceFunctorMap F) x))
        (fun {_ _} p => ZerothHomotopy.sound (p.map (NQKSpaceFunctorMap F).continuous))
        (HomotopyGroup.pi0EquivZerothHomotopy
          (X := NQKSpace C) (x := Path.refl (NQReal.basepoint C)) a) :=
  (HomotopyGroup.pi0EquivZerothHomotopy
    (X := NQKSpace D) (x := Path.refl (NQReal.basepoint D))).apply_symm_apply _


private theorem originalKFunctorUnitPathValueComputed
    (F : C ⥤ D) [F.Additive] [F.IsExact] :
    NQKSpaceFunctorKiUnitRootPath F =
      ((ContinuousMap.rootUnitContraction
        (fun p : Path ((NQRealFunctorWeaklyPointed F).hom (NQReal.basepoint C))
          (NQReal.basepoint D) => p) continuous_eval).evalAt
            (NQRealFunctorWeaklyPointed F).rootPath).cast
              (NQKSpaceFunctorMap_unit_eq_rootUnitLoopFamily F) rfl := rfl

/-- The designated functor unit path is the contraction of its original root,
with the recorded source endpoint cast. -/
theorem NQKSpaceFunctorKiUnitRootPath_eq_rootUnitContraction
    (F : C ⥤ D) [F.Additive] [F.IsExact] :
    NQKSpaceFunctorKiUnitRootPath F =
      ((ContinuousMap.rootUnitContraction
        (fun p : Path ((NQRealFunctorWeaklyPointed F).hom (NQReal.basepoint C))
          (NQReal.basepoint D) => p) continuous_eval).evalAt
            (NQRealFunctorWeaklyPointed F).rootPath).cast
              (NQKSpaceFunctorMap_unit_eq_rootUnitLoopFamily F) rfl :=
  originalKFunctorUnitPathValueComputed F

private theorem originalPositiveKMapValueComputed
    (F : C ⥤ D) [F.Additive] [F.IsExact] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (NQKSpace C) (Path.refl (NQReal.basepoint C))) :
    NQKSpaceFunctorPositiveKiMap F n a =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of (NQKSpace D))
        (NQKSpaceFunctorKiUnitRootPath F) (HomotopyGroup.map (NQKSpaceFunctorMap F) a) := rfl

/-- Every positive map class is the actual functor map followed by transport
along its designated root unit contraction. -/
theorem NQKSpaceFunctorPositiveKiMap_apply
    (F : C ⥤ D) [F.Additive] [F.IsExact] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (NQKSpace C) (Path.refl (NQReal.basepoint C))) :
    NQKSpaceFunctorPositiveKiMap F n a =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of (NQKSpace D))
        (NQKSpaceFunctorKiUnitRootPath F) (HomotopyGroup.map (NQKSpaceFunctorMap F) a) :=
  originalPositiveKMapValueComputed F n a

private theorem originalAllKMapSuccPositiveComputed
    (F : C ⥤ D) [F.Additive] [F.IsExact] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (NQKSpace C) (Path.refl (NQReal.basepoint C))) :
    NQKSpaceFunctorKiMap F (n + 1) a = NQKSpaceFunctorPositiveKiMap F n a := rfl

/-- Original ALLdegree successor map is EXACT original positive map,
with its original group/root/carrier choices retained. -/
theorem NQKSpaceFunctorKiMap_succ_eq_positive
    (F : C ⥤ D) [F.Additive] [F.IsExact] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (NQKSpace C) (Path.refl (NQReal.basepoint C))) :
    NQKSpaceFunctorKiMap F (n + 1) a = NQKSpaceFunctorPositiveKiMap F n a :=
  originalAllKMapSuccPositiveComputed F n a

end AlgebraicKTheory

end
