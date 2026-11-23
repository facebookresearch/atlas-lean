/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.BasedSplitExactQLoopComparison
public import MathlibExt.CategoryTheory.Monoidal.CoreAdditivePairBasedRealization
public import MathlibExt.KTheory.Ring.K0.ComponentProduct
public import MathlibExt.Topology.Homotopy.PointRelativeComposition
public import MathlibExt.Algebra.Category.FGProjectiveCat.Basic

/-!
# The original projective Q loops and original native additive Pair space

Projective modules carry their canonical split exact structure, so the
original based Q-loop comparison has no splitting premise here. Its
actual loop inverse composes with the literal realized Core-to-Pair map
and the canonical native realization inverse. The based Core comparison
and all original point laws compose BOTH complete inverse families.
Every component and the original Ring/module/native universes are retained.
-/

noncomputable section

open CategoryTheory CategoryTheory.ExactCategory CategoryTheory.Limits Topology
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open CategoryTheory.CoreLocalizationComparison
open CategoryTheory.SInverseS.ComponentTranslation
open scoped ContinuousMap CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory

attribute [local instance] MonoidalActionCategory.diagonalAction

universe u v w

namespace AlgebraicKTheory.QuillenPlus

private theorem projectiveRowsSplit (R : Type u) [Ring R] :
    ∀ S : ShortComplex (FGProjectiveCat.{max u v} R),
      IsAdmissibleExact S → Nonempty S.Splitting := by
  intro S hS
  change Nonempty S.Splitting at hS
  exact hS

/-- The original full Q-loop return, followed by the literal Core-to-Pair
map and canonical native-realization inverse. This is an actual map, not
a comparison supplied by the caller. -/
public def projectiveQLoopToNativePair (R : Type u) [Ring R] :
    C(BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max u v} R),
      RingK0.projectiveOriginalSpace.{u, v, w} R) := by
  let C := FGProjectiveCat.{max u v} R
  let D := BasedSplitExactQLoop.comparison (C := C) (projectiveRowsSplit.{u, v} R)
  let I := nativeOriginalRealizationIso.{(max u v) + 1, max u v, w} (C := C)
  exact I.inv.hom.comp
    ((SSet.toTop.map (nerveMap (coreAdditivePairEquivalence (C := C)).functor)).hom.comp
      D.loopInverse)

/-- The SAME original Q-loop map is a based homotopy equivalence onto
the complete original native projective Pair space. Its literal forward
field and BOTH original point-relative inverse families are retained,
without any model, inverse or comparison input over the Ring. -/
public theorem projectiveQLoopNativePairEquivalence_exists (R : Type u) [Ring R] :
    let C := FGProjectiveCat.{max u v} R
    let Q := BasedSplitExactQLoop.originalQLoops (C := C)
    let q := BasedSplitExactQLoop.constantQLoop (C := C)
    let N := RingK0.projectiveOriginalSpace.{u, v, w} R
    let n := RingK0.projectiveOriginalPoint.{u, v, w} R
    ∃ e : Q ≃ₕ N, e.toFun = projectiveQLoopToNativePair.{u, v, w} R ∧
      e.toFun q = n ∧ e.invFun n = q ∧
      Nonempty (ContinuousMap.HomotopyRel (e.invFun.comp e.toFun) (ContinuousMap.id Q) {q}) ∧
      Nonempty (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun) (ContinuousMap.id N) {n}) := by
  let C := FGProjectiveCat.{max u v} R
  let A := BasedSplitExactQLoop.completedCoreSpace (C := C)
  let a := BasedSplitExactQLoop.completedCorePoint (C := C)
  let Q := BasedSplitExactQLoop.originalQLoops (C := C)
  let q := BasedSplitExactQLoop.constantQLoop (C := C)
  let Y := originalSpace (C := C)
  let y := originalSpacePoint (C := C)
  let N := RingK0.projectiveOriginalSpace.{u, v, w} R
  let n := RingK0.projectiveOriginalPoint.{u, v, w} R
  let hSplit := projectiveRowsSplit.{u, v} R
  let D := BasedSplitExactQLoop.comparison (C := C) hSplit
  let E := BasedSplitExactQLoop.homotopyEquiv (C := C) hSplit
  let eQ := E.symm
  have hEF := BasedSplitExactQLoop.homotopyEquiv_toFun (C := C) hSplit
  have hEI := BasedSplitExactQLoop.homotopyEquiv_invFun (C := C) hSplit
  have hQa : eQ.toFun q = a :=
    (congrArg (fun f : C(Q, A) => f q) hEI).trans D.loopInverse_point
  have hQq : eQ.invFun a = q :=
    (congrArg (fun f : C(A, Q) => f a) hEF).trans
      (BasedSplitExactQLoop.comparisonMap_point (C := C))
  let LQ : ContinuousMap.HomotopyRel
      (eQ.invFun.comp eQ.toFun) (ContinuousMap.id Q) {q} :=
    D.loopTargetHomotopy.cast
      (congrArg₂ (fun (f : C(A, Q)) (g : C(Q, A)) => f.comp g) hEF.symm hEI.symm) rfl
  let RQ : ContinuousMap.HomotopyRel
      (eQ.toFun.comp eQ.invFun) (ContinuousMap.id A) {a} :=
    D.loopSourceHomotopy.cast
      (congrArg₂ (fun (g : C(Q, A)) (f : C(A, Q)) => g.comp f) hEI.symm hEF.symm) rfl
  obtain ⟨eC, hCF, hCa, hCy, ⟨LC⟩, ⟨RC₀⟩⟩ :=
    coreAdditivePairRealizationBasedEquivalence_exists (C := C)
  have hCyForward : eC.toFun a = y :=
    hCa.trans (originalSpacePoint_eq_realizedVertex (C := C)).symm
  have hCyInverse : eC.invFun y = a :=
    (congrArg eC.invFun (originalSpacePoint_eq_realizedVertex (C := C))).trans hCy
  let RC : ContinuousMap.HomotopyRel
      (eC.toFun.comp eC.invFun) (ContinuousMap.id Y) {y} :=
    Eq.mp (congrArg (fun z : Y => ContinuousMap.HomotopyRel
      (eC.toFun.comp eC.invFun) (ContinuousMap.id Y) {z})
      (originalSpacePoint_eq_realizedVertex (C := C)).symm) RC₀
  let e₁ := eQ.trans eC
  have h₁q : e₁.toFun q = y := (congrArg eC.toFun hQa).trans hCyForward
  have h₁y : e₁.invFun y = q := (congrArg eQ.invFun hCyInverse).trans hQq
  let L₁ := eQ.transLeftHomotopyRel eC q a hQa LQ LC
  let R₁ := eQ.transRightHomotopyRel eC a y hCyInverse RQ RC
  let I := nativeOriginalRealizationIso.{(max u v) + 1, max u v, w} (C := C)
  let h : N ≃ₜ Y := TopCat.homeoOfIso I
  let eH := h.symm.toHomotopyEquiv
  have hHn : eH.toFun y = n := by
    change I.inv y = n
    exact (nativeOriginalRealizationIso_inv_point.{(max u v) + 1, max u v, w} (C := C)).trans
      (RingK0.projectiveOriginalPoint_eq_native.{u, v, w} R).symm
  have hHy : eH.invFun n = y := by
    change I.hom n = y
    exact (congrArg I.hom (RingK0.projectiveOriginalPoint_eq_native.{u, v, w} R)).trans
      (nativeOriginalRealizationIso_point.{(max u v) + 1, max u v, w} (C := C))
  have hHL : eH.invFun.comp eH.toFun = ContinuousMap.id Y := by
    apply ContinuousMap.ext
    intro z
    exact h.apply_symm_apply z
  have hHR : eH.toFun.comp eH.invFun = ContinuousMap.id N := by
    apply ContinuousMap.ext
    intro z
    exact h.symm_apply_apply z
  let LH : ContinuousMap.HomotopyRel
      (eH.invFun.comp eH.toFun) (ContinuousMap.id Y) {y} :=
    (ContinuousMap.HomotopyRel.refl (ContinuousMap.id Y) {y}).cast hHL.symm rfl
  let RH : ContinuousMap.HomotopyRel
      (eH.toFun.comp eH.invFun) (ContinuousMap.id N) {n} :=
    (ContinuousMap.HomotopyRel.refl (ContinuousMap.id N) {n}).cast hHR.symm rfl
  let e := e₁.trans eH
  let L := e₁.transLeftHomotopyRel eH q y h₁q L₁ LH
  let S := e₁.transRightHomotopyRel eH y n hHy R₁ RH
  have heq : e.toFun q = n := (congrArg eH.toFun h₁q).trans hHn
  have hen : e.invFun n = q := (congrArg e₁.invFun hHy).trans h₁y
  have hForward : e.toFun = projectiveQLoopToNativePair.{u, v, w} R := by
    change eH.toFun.comp (eC.toFun.comp E.invFun) =
      eH.toFun.comp
        ((SSet.toTop.map (nerveMap (coreAdditivePairEquivalence (C := C)).functor)).hom.comp
          D.loopInverse)
    exact congrArg (fun k => eH.toFun.comp k)
      (congrArg₂ (fun (f : C(A, Y)) (g : C(Q, A)) => f.comp g) hCF hEI)
  exact ⟨e, hForward, heq, hen, ⟨L⟩, ⟨S⟩⟩

end AlgebraicKTheory.QuillenPlus

end


noncomputable section

open CategoryTheory CategoryTheory.ExactCategory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open CategoryTheory.CoreLocalizationComparison
open CategoryTheory.SInverseS.ComponentTranslation
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory

attribute [local instance] MonoidalActionCategory.diagonalAction

universe u v w

namespace AlgebraicKTheory.QuillenPlus

private theorem projectiveQLoopToNativePair_apply_computation
    (R : Type u) [Ring R]
    (x : BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max u v} R)) :
    let C := FGProjectiveCat.{max u v} R
    let hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting :=
      fun S hS => by change Nonempty S.Splitting at hS; exact hS
    let D := BasedSplitExactQLoop.comparison (C := C) hSplit
    let I := nativeOriginalRealizationIso.{max u v + 1, max u v, w} (C := C)
    projectiveQLoopToNativePair.{u, v, w} R x =
      I.inv (SSet.toTop.map (nerveMap (coreAdditivePairEquivalence (C := C)).functor)
        (D.loopInverse x)) := by
  dsimp only
  unfold projectiveQLoopToNativePair
  rfl

/-- Every original Q-loop value follows the same stored Q-loop inverse,
realized positive-first Core-to-Pair map and native-realization inverse.
The splitting proof is the canonical projective exact structure, not input. -/
public theorem projectiveQLoopToNativePair_apply
    (R : Type u) [Ring R]
    (x : BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max u v} R)) :
    let C := FGProjectiveCat.{max u v} R
    let hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting :=
      fun S hS => by change Nonempty S.Splitting at hS; exact hS
    let D := BasedSplitExactQLoop.comparison (C := C) hSplit
    let I := nativeOriginalRealizationIso.{max u v + 1, max u v, w} (C := C)
    projectiveQLoopToNativePair.{u, v, w} R x =
      I.inv (SSet.toTop.map (nerveMap (coreAdditivePairEquivalence (C := C)).functor)
        (D.loopInverse x)) :=
  projectiveQLoopToNativePair_apply_computation.{u, v, w} R x

end AlgebraicKTheory.QuillenPlus

end
