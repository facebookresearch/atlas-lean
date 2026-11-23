/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.OriginalConullScalarReturnCalibration
public import MathlibExt.KTheory.Exact.Quillen.KSpaceFunctorAllKiMap
public import MathlibExt.Topology.Homotopy.OriginalLoopOwnUnitCalibration
public import MathlibExt.Topology.Homotopy.WeaklyPointedPositiveHomotopyGroupMap

/-!
# Original mixed Quillen maps and the canonical connective-group maps

The mixed realization map and the current exact-functor realization map use
the same Quillen functor and the same original zero-comparison edge. Their
whole weakly pointed and loop maps therefore agree. The original conull unit
and the canonical connective-map unit agree at every pair of interval times,
by the existing equality of the two original unit constructions.

Consequently their genuine positive group homomorphisms and successor
connective-group functions agree on every original cube class. Category
object and morphism universes remain independent; only the original stock
group dictionaries are selected locally. No map, root or inverse family is
replaced, and no stationary root or trivial basepoint action is assumed.
-/

public section

noncomputable section

open CategoryTheory Limits
open AlgebraicKTheory.QuillenMixedUniverseTransport
open AlgebraicKTheory.OriginalQZeroComparison
open scoped Topology

universe uC vC uD vD uX uY

namespace AlgebraicKTheory

private theorem weaklyPointedExtOfRootCast
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} {f g : ContinuousMap.WeaklyPointed x y}
    (h : f.hom = g.hom)
    (hp : f.rootPath = g.rootPath.cast (congrArg (fun k : C(X, Y) => k x) h) rfl) :
    f = g := by
  cases f with
  | mk fm fp =>
    cases g with
    | mk gm gp =>
      dsimp only at h hp
      cases h
      have hRoots : fp = gp := hp.trans (Path.cast_rfl_rfl gp)
      cases hRoots
      rfl

private theorem monoidHomGroupCast_apply
    {A : Type uX} {B : Type uY} {s s' : Group A} {t t' : Group B}
    (hs : s = s') (ht : t = t')
    (f : letI : Group A := s; letI : Group B := t; A →* B) (a : A) :
    (Eq.mp (congrArg₂ (fun (source : Group A) (target : Group B) =>
      letI : Group A := source
      letI : Group B := target
      A →* B) hs ht) f) a = f a := by
  cases hs
  cases ht
  rfl

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- Both original weakly pointed constructions retain the same whole
Quillen-functor realization and every value of the same zero-comparison root. -/
theorem mixedNQWeaklyPointedMap_eq_functorWeaklyPointed :
    mixedNQWeaklyPointedMap F = NQRealFunctorWeaklyPointed F := by
  have hHom : (mixedNQWeaklyPointedMap F).hom = (NQRealFunctorWeaklyPointed F).hom :=
    (congrArg ContinuousMap.WeaklyPointed.hom (mixedNQWeaklyPointedMap_value F)).trans
      ((mixedNQRealMap_value F).trans (NQRealFunctorWeaklyPointed_hom F).symm)
  refine weaklyPointedExtOfRootCast hHom ?_
  apply Path.ext
  funext t
  have hMixed := congrArg
    (fun w : ContinuousMap.WeaklyPointed (NQReal.basepoint C) (NQReal.basepoint D) =>
      w.rootPath.toContinuousMap.toFun t)
    (mixedNQWeaklyPointedMap_value F)
  have hCurrent := congrArg
    (fun p : Path ((NQRealFunctorWeaklyPointed F).hom (NQReal.basepoint C))
        (NQReal.basepoint D) => p.toContinuousMap.toFun t)
    (NQRealFunctorWeaklyPointed_rootPath_eq F)
  exact hMixed.trans ((mixedNQRootPath_value F t).trans hCurrent.symm)

/-- The original mixed loop map is the whole canonical exact-functor K-space map. -/
theorem mixedNQKSpaceMap_eq_functorMap :
    mixedNQKSpaceMap F = NQKSpaceFunctorMap F := by
  apply ContinuousMap.ext
  intro gamma
  have hMixed := DFunLike.congr_fun (mixedNQKSpaceMap_wholeWeak_value F) gamma
  have hWeak := congrArg
    (fun w : ContinuousMap.WeaklyPointed (NQReal.basepoint C) (NQReal.basepoint D) =>
      w.loopMap gamma)
    (mixedNQWeaklyPointedMap_eq_functorWeaklyPointed F)
  exact hMixed.trans (hWeak.trans
    ((ContinuousMap.WeaklyPointed.loopMap_apply (NQRealFunctorWeaklyPointed F) gamma).trans
      (NQKSpaceFunctorMap_apply F gamma).symm))

/-- Every original conull-unit and loop time agrees with the corresponding
canonical functor-unit time, retaining both original unit programs. -/
theorem originalConullScalarCanonicalLoopUnit_functorValue (t s : unitInterval) :
    ((originalConullScalarCanonicalLoopUnit F).toContinuousMap.toFun
      t).toContinuousMap.toFun s =
      ((NQKSpaceFunctorKiUnitRootPath F).toContinuousMap.toFun t).toContinuousMap.toFun s := by
  have hOriginal := congrArg
    (fun gamma : NQKSpace D => gamma.toContinuousMap.toFun s)
    (originalConullScalarCanonicalLoopUnit_value F t)
  have hWeak := congrArg
    (fun w : ContinuousMap.WeaklyPointed (NQReal.basepoint C) (NQReal.basepoint D) =>
      ((ContinuousMap.WeaklyPointed.loopUnitRootPath w).toContinuousMap.toFun
        t).toContinuousMap.toFun s)
    (mixedNQWeaklyPointedMap_eq_functorWeaklyPointed F)
  have hCalibration := congrArg
    (fun p : Path ((NQRealFunctorWeaklyPointed F).loopMap
        (Path.refl (NQReal.basepoint C))) (Path.refl (NQReal.basepoint D)) =>
      (p.toContinuousMap.toFun t).toContinuousMap.toFun s)
    (ContinuousMap.WeaklyPointed.originalLoopOwnUnit_eq201 (NQRealFunctorWeaklyPointed F))
  have hCurrent := congrArg
    (fun p : Path (NQKSpaceFunctorMap F (Path.refl (NQReal.basepoint C)))
        (Path.refl (NQReal.basepoint D)) =>
      (p.toContinuousMap.toFun t).toContinuousMap.toFun s)
    (NQKSpaceFunctorKiUnitRootPath_eq_rootUnitContraction F)
  exact hOriginal.trans (hWeak.trans (hCalibration.trans hCurrent.symm))

/-- The two actual unit paths are equal after the source cast earned from
the equality of the whole original loop maps. -/
theorem originalConullScalarCanonicalLoopUnit_eq_functorUnit :
    (originalConullScalarCanonicalLoopUnit F).cast
        (congrArg
          (fun m : C(NQKSpace C, NQKSpace D) => m (Path.refl (NQReal.basepoint C)))
          (mixedNQKSpaceMap_eq_functorMap F).symm) rfl =
      NQKSpaceFunctorKiUnitRootPath F := by
  apply Path.ext
  funext t
  apply Path.ext
  funext s
  exact originalConullScalarCanonicalLoopUnit_functorValue F t s

private theorem originalMixedLoopRecord_eq_functorRecord :
    (⟨mixedNQKSpaceMap F, originalConullScalarCanonicalLoopUnit F⟩ :
      ContinuousMap.WeaklyPointed (Path.refl (NQReal.basepoint C))
        (Path.refl (NQReal.basepoint D))) =
    (⟨NQKSpaceFunctorMap F, NQKSpaceFunctorKiUnitRootPath F⟩ :
      ContinuousMap.WeaklyPointed (Path.refl (NQReal.basepoint C))
        (Path.refl (NQReal.basepoint D))) := by
  refine weaklyPointedExtOfRootCast (mixedNQKSpaceMap_eq_functorMap F) ?_
  apply Path.ext
  funext t
  apply Path.ext
  funext s
  exact originalConullScalarCanonicalLoopUnit_functorValue F t s

/-- The original mixed map with its original conull unit is the genuine
canonical positive Ki homomorphism, for every degree and every original class. -/
theorem originalMixedPositiveKiMap_eq_functorMap (n : ℕ) :
    let A := HomotopyGroup.Pi (n + 1) (NQKSpace C) (Path.refl (NQReal.basepoint C));
    let B := HomotopyGroup.Pi (n + 1) (NQKSpace D) (Path.refl (NQReal.basepoint D));
    letI := NQKSpaceOriginalPositiveGroup C n (Path.refl (NQReal.basepoint C));
    letI := NQKSpaceOriginalPositiveGroup D n (Path.refl (NQReal.basepoint D));
    ContinuousMap.WeaklyPointed.positiveHomotopyGroupMap n
        (⟨mixedNQKSpaceMap F, originalConullScalarCanonicalLoopUnit F⟩ :
          ContinuousMap.WeaklyPointed (Path.refl (NQReal.basepoint C))
            (Path.refl (NQReal.basepoint D))) =
      Eq.mp (congrArg₂ (fun (source : Group A) (target : Group B) =>
        letI : Group A := source
        letI : Group B := target
        A →* B)
        (NQKSpaceOriginalPositiveGroup_value C n (Path.refl (NQReal.basepoint C)))
        (NQKSpaceOriginalPositiveGroup_value D n (Path.refl (NQReal.basepoint D))))
        (NQKSpaceFunctorPositiveKiMap F n) := by
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
  apply MonoidHom.ext
  intro a
  let current : ContinuousMap.WeaklyPointed (X := NQKSpace C) (Y := NQKSpace D)
      (Path.refl (NQReal.basepoint C)) (Path.refl (NQReal.basepoint D)) :=
    ⟨NQKSpaceFunctorMap F, NQKSpaceFunctorKiUnitRootPath F⟩
  have hRecord := congrArg
    (fun w : ContinuousMap.WeaklyPointed (X := NQKSpace C) (Y := NQKSpace D)
        (Path.refl (NQReal.basepoint C)) (Path.refl (NQReal.basepoint D)) =>
      ContinuousMap.WeaklyPointed.positiveHomotopyGroupMap n w a)
    (originalMixedLoopRecord_eq_functorRecord F)
  have hCurrent := ContinuousMap.WeaklyPointed.positiveHomotopyGroupMap_apply n current a
  have hCast := monoidHomGroupCast_apply
    (NQKSpaceOriginalPositiveGroup_value C n (Path.refl (NQReal.basepoint C)))
    (NQKSpaceOriginalPositiveGroup_value D n (Path.refl (NQReal.basepoint D)))
    (NQKSpaceFunctorPositiveKiMap F n) a
  exact hRecord.trans
    (hCurrent.trans ((NQKSpaceFunctorPositiveKiMap_apply F n a).symm.trans hCast.symm))

/-- Every successor of the original mixed group map is the actual canonical
all-degree Ki function on the same original cube classes. -/
theorem originalMixedSuccessorKiMap_eq_functorMap (n : ℕ) :
    letI := NQKSpaceOriginalPositiveGroup C n (Path.refl (NQReal.basepoint C));
    letI := NQKSpaceOriginalPositiveGroup D n (Path.refl (NQReal.basepoint D));
    (fun a : HomotopyGroup.Pi (n + 1) (NQKSpace C) (Path.refl (NQReal.basepoint C)) =>
      ContinuousMap.WeaklyPointed.positiveHomotopyGroupMap n
        (⟨mixedNQKSpaceMap F, originalConullScalarCanonicalLoopUnit F⟩ :
          ContinuousMap.WeaklyPointed (Path.refl (NQReal.basepoint C))
            (Path.refl (NQReal.basepoint D))) a) =
      NQKSpaceFunctorKiMap F (n + 1) := by
  letI := NQKSpaceOriginalPositiveGroup C n (Path.refl (NQReal.basepoint C))
  letI := NQKSpaceOriginalPositiveGroup D n (Path.refl (NQReal.basepoint D))
  funext a
  exact (DFunLike.congr_fun (originalMixedPositiveKiMap_eq_functorMap F n) a).trans
    ((monoidHomGroupCast_apply
      (NQKSpaceOriginalPositiveGroup_value C n (Path.refl (NQReal.basepoint C)))
      (NQKSpaceOriginalPositiveGroup_value D n (Path.refl (NQReal.basepoint D)))
      (NQKSpaceFunctorPositiveKiMap F n) a).trans
        (NQKSpaceFunctorKiMap_succ_eq_positive F n a).symm)

end AlgebraicKTheory

end
