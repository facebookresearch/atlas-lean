/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.Comparison.ScalarExtension
public import MathlibExt.KTheory.Exact.Quillen.OriginalMixedFunctorKiMap
public import MathlibExt.KTheory.Ring.Comparison.OriginalNormalizedQScalarNaturality
public import MathlibExt.Topology.Homotopy.BasedHomotopyGroupEquivalence
public import MathlibExt.Topology.Homotopy.MixedBasepointChangeNaturality

/-!
# The original scalar comparison and the canonical Quillen Ki maps

The original raw loop charts transport the actual exact-functor Ki program.
The chosen unit is compared at every unit and loop time. The original
independent plus maps and normalized comparison give both positive
naturality directions, with their existing inverse maps retained.

Degree zero uses the original fixed RingK0 evaluator on every component.
Degree one uses the unchanged original plus and native classical K1
dictionaries. Ring, module and native roles remain independent.
-/

public section

noncomputable section

open CategoryTheory Limits
open AlgebraicKTheory.QuillenMixedUniverseTransport
open AlgebraicKTheory.OriginalQuillenUnliftedTransport
open AlgebraicKTheory.OriginalQZeroComparison
open scoped Topology

universe uX uY uZ uR uS uMR uMS uNR uNS

namespace AlgebraicKTheory.QuillenPlus

private def chartLeftRelativeInverse
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    ContinuousMap.HomotopyRel
      (e.symm.toHomotopyEquiv.toFun.comp e.toHomotopyEquiv.toFun)
      (ContinuousMap.id X) {x} := by
  refine (ContinuousMap.HomotopyRel.refl (ContinuousMap.id X) {x}).cast ?_ rfl
  apply ContinuousMap.ext
  intro z
  exact (e.symm_apply_apply z).symm

private def chartRightRelativeInverse
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (y : Y) :
    ContinuousMap.HomotopyRel
      (e.toHomotopyEquiv.toFun.comp e.symm.toHomotopyEquiv.toFun)
      (ContinuousMap.id Y) {y} := by
  refine (ContinuousMap.HomotopyRel.refl (ContinuousMap.id Y) {y}).cast ?_ rfl
  apply ContinuousMap.ext
  intro z
  exact (e.apply_symm_apply z).symm

private theorem rootedPositiveStrictPrecompose
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {x : X} {y : Y} {z : Z} (n : ℕ) (f : C(X, Y)) (g : C(Y, Z))
    (hf : f x = y) (p : Path (g y) z) (a : HomotopyGroup.Pi (n + 1) X x) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Z)
        (p.cast (congrArg g hf) rfl) (HomotopyGroup.map (g.comp f) a) =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Z) p
        (HomotopyGroup.map g (HomotopyGroup.mapHomOfEq f hf n a)) := by
  subst y
  rw [HomotopyGroup.mapHomOfEq_apply]
  exact congrArg (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Z) p)
    (HomotopyGroup.map_comp f g a)

private theorem rootedPositiveStrictPostcompose
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {x : X} {y : Y} {z : Z} (n : ℕ) (f : C(X, Y)) (g : C(Y, Z))
    (hg : g y = z) (p : Path (f x) y) (a : HomotopyGroup.Pi (n + 1) X x) :
    HomotopyGroup.mapHomOfEq g hg n
        (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) p
          (HomotopyGroup.map f a)) =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Z)
        ((p.map g.continuous).cast rfl hg.symm) (HomotopyGroup.map (g.comp f) a) := by
  subst z
  rw [HomotopyGroup.mapHomOfEq_apply]
  exact (TopCat.homotopyGroupBasepointChangeMulEquiv_naturality_mixed n g p
    (HomotopyGroup.map f a)).trans
      (congrArg (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Z)
        (p.map g.continuous)) (HomotopyGroup.map_comp f g a).symm)

private theorem rootedPositiveMapEqOfWholeValues
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (n : ℕ) (f g : C(X, Y)) (h : f = g)
    (p : Path (f x) y) (q : Path (g x) y)
    (hp : p = q.cast (congrArg (fun m : C(X, Y) => m x) h) rfl)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) p
        (HomotopyGroup.map f a) =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) q
        (HomotopyGroup.map g a) := by
  cases h
  have hPaths : p = q := hp.trans (Path.cast_rfl_rfl q)
  cases hPaths
  rfl

/-- The original point chart sends its actual constant loop to the raw constant loop. -/
theorem canonicalOriginalQLoopChart_point.{uR', uMR'} (R : Type uR') [Ring R] :
    originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'} R)
        (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))) =
      BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR' uMR'} R) := by
  let CR := FGProjectiveCat.{max uR' uMR'} R
  let p := Path.refl (NQReal.basepoint CR)
  let e := originalNQLoopPointHomeomorph CR
  have h : e p 0 = NQReal.basepoint CR :=
    (originalNQLoopPointHomeomorph_value CR p 0).trans p.source
  have hZero : NQReal.basepoint CR = zeroQVertex (C := CR) := h.symm.trans (e p).source
  apply Path.ext
  funext t
  exact (originalNQLoopPointHomeomorph_value CR p t).trans hZero

/-- The inverse chart retains the same original constant point. -/
theorem canonicalOriginalQLoopChart_inverse_point.{uR', uMR'} (R : Type uR') [Ring R] :
    (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'} R)).symm
        (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR' uMR'} R)) =
      Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)) := by
  let e := originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'} R)
  exact (congrArg e.symm (canonicalOriginalQLoopChart_point.{uR', uMR'} R)).symm.trans
    (e.symm_apply_apply (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))))

/-- The positive group chart uses both actual original homeomorphism maps. -/
def canonicalOriginalQPositiveChart.{uR', uMR'} (R : Type uR') [Ring R] (n : ℕ) :
    letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
        (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)))) :=
      HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
        (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))) (Fin (n + 1));
    HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
        (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))) ≃*
      HomotopyGroup.Pi (n + 1)
        (BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR' uMR'} R))
        (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR' uMR'} R)) := by
  letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)))) :=
    HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
      (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))) (Fin (n + 1))
  exact HomotopyGroup.mulEquivOfBasedInverse n
    (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'} R)).toHomotopyEquiv.toFun
    (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'} R)).symm.toHomotopyEquiv.toFun
    (canonicalOriginalQLoopChart_point.{uR', uMR'} R)
    (canonicalOriginalQLoopChart_inverse_point.{uR', uMR'} R)
    (chartLeftRelativeInverse (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))))
    (chartRightRelativeInverse (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'} R))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR' uMR'} R)))

private theorem originalPositiveChartApplyComputed.{uR', uMR'}
    (R : Type uR') [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)))) :
    canonicalOriginalQPositiveChart.{uR', uMR'} R n a =
      HomotopyGroup.mapHomOfEq
        (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'} R)).toHomotopyEquiv.toFun
        (canonicalOriginalQLoopChart_point.{uR', uMR'} R) n a := by
  unfold canonicalOriginalQPositiveChart
  exact HomotopyGroup.mulEquivOfBasedInverse_apply _ _ _ _ _ _ _ a

/-- Every forward chart class is mapped by the original point homeomorphism. -/
theorem canonicalOriginalQPositiveChart_apply.{uR', uMR'}
    (R : Type uR') [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)))) :
    canonicalOriginalQPositiveChart.{uR', uMR'} R n a =
      HomotopyGroup.mapHomOfEq
        (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'} R)).toHomotopyEquiv.toFun
        (canonicalOriginalQLoopChart_point.{uR', uMR'} R) n a :=
  originalPositiveChartApplyComputed.{uR', uMR'} R n a

private theorem originalPositiveChartInverseComputed.{uR', uMR'}
    (R : Type uR') [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1)
      (BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR' uMR'} R))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR' uMR'} R))) :
    letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
        (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)))) :=
      HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
        (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))) (Fin (n + 1));
    (canonicalOriginalQPositiveChart.{uR', uMR'} R n).symm a =
      HomotopyGroup.mapHomOfEq
        (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'}
            R)).symm.toHomotopyEquiv.toFun
        (canonicalOriginalQLoopChart_inverse_point.{uR', uMR'} R) n a := by
  letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)))) :=
    HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
      (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))) (Fin (n + 1))
  unfold canonicalOriginalQPositiveChart
  exact HomotopyGroup.mulEquivOfBasedInverse_symm_apply _ _ _ _ _ _ _ a

/-- Every inverse chart class follows the original inverse homeomorphism. -/
theorem canonicalOriginalQPositiveChart_symm_apply.{uR', uMR'}
    (R : Type uR') [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1)
      (BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR' uMR'} R))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR' uMR'} R))) :
    letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
        (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)))) :=
      HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
        (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))) (Fin (n + 1));
    (canonicalOriginalQPositiveChart.{uR', uMR'} R n).symm a =
      HomotopyGroup.mapHomOfEq
        (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'}
            R)).symm.toHomotopyEquiv.toFun
        (canonicalOriginalQLoopChart_inverse_point.{uR', uMR'} R) n a := by
  letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)))) :=
    HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
      (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))) (Fin (n + 1))
  exact originalPositiveChartInverseComputed.{uR', uMR'} R n a

/-- The original normalized plus/raw comparison lands in the current original Q carrier. -/
def canonicalOriginalPlusQPositiveComparison.{uR', uMR', uNR'}
    (R : Type uR') [Ring R] (n : ℕ) :
    letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
        (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)))) :=
      HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
        (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))) (Fin (n + 1));
    HomotopyGroup.Pi (n + 1) (StableGL.independentBGLCellTarget R)
        (StableGL.independentBGLCellPoint R) ≃*
      HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
        (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))) := by
  letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)))) :=
    HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
      (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))) (Fin (n + 1))
  exact (originalNormalizedPlusQPositiveMulEquiv.{uR', uMR', uNR'} R n).trans
    (canonicalOriginalQPositiveChart.{uR', uMR'} R n).symm

private theorem originalPlusQComparisonApplyComputed.{uR', uMR', uNR'}
    (R : Type uR') [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (StableGL.independentBGLCellTarget R)
      (StableGL.independentBGLCellPoint R)) :
    letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
        (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)))) :=
      HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
        (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))) (Fin (n + 1));
    canonicalOriginalPlusQPositiveComparison.{uR', uMR', uNR'} R n a =
      (canonicalOriginalQPositiveChart.{uR', uMR'} R n).symm
        (originalNormalizedPlusQPositiveMulEquiv.{uR', uMR', uNR'} R n a) := by
  letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)))) :=
    HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
      (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))) (Fin (n + 1))
  unfold canonicalOriginalPlusQPositiveComparison
  rfl

/-- The comparison keeps the old normalized map and the actual inverse point chart. -/
theorem canonicalOriginalPlusQPositiveComparison_apply.{uR', uMR', uNR'}
    (R : Type uR') [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (StableGL.independentBGLCellTarget R)
      (StableGL.independentBGLCellPoint R)) :
    letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
        (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)))) :=
      HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
        (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))) (Fin (n + 1));
    canonicalOriginalPlusQPositiveComparison.{uR', uMR', uNR'} R n a =
      (canonicalOriginalQPositiveChart.{uR', uMR'} R n).symm
        (originalNormalizedPlusQPositiveMulEquiv.{uR', uMR', uNR'} R n a) := by
  letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)))) :=
    HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
      (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))) (Fin (n + 1))
  exact originalPlusQComparisonApplyComputed.{uR', uMR', uNR'} R n a

private theorem originalPlusQComparisonInverseComputed.{uR', uMR', uNR'}
    (R : Type uR') [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)))) :
    letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
        (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)))) :=
      HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
        (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))) (Fin (n + 1));
    (canonicalOriginalPlusQPositiveComparison.{uR', uMR', uNR'} R n).symm a =
      (originalNormalizedPlusQPositiveMulEquiv.{uR', uMR', uNR'} R n).symm
        (canonicalOriginalQPositiveChart.{uR', uMR'} R n a) := by
  letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)))) :=
    HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
      (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))) (Fin (n + 1))
  unfold canonicalOriginalPlusQPositiveComparison
  rfl

/-- The inverse retains the old raw-Q inverse and the original forward point chart. -/
theorem canonicalOriginalPlusQPositiveComparison_symm_apply.{uR', uMR', uNR'}
    (R : Type uR') [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)))) :
    letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
        (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)))) :=
      HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
        (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))) (Fin (n + 1));
    (canonicalOriginalPlusQPositiveComparison.{uR', uMR', uNR'} R n).symm a =
      (originalNormalizedPlusQPositiveMulEquiv.{uR', uMR', uNR'} R n).symm
        (canonicalOriginalQPositiveChart.{uR', uMR'} R n a) := by
  letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)))) :=
    HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR' uMR'} R))
      (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))) (Fin (n + 1))
  exact originalPlusQComparisonInverseComputed.{uR', uMR', uNR'} R n a

attribute [local instance] StableGL.nativeProjectiveZeroScalarFunctor_additive
attribute [local instance] StableGL.nativeProjectiveZeroScalarFunctor_isExact

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S)

/-- The entire original raw scalar map commutes with both original point charts. -/
theorem canonicalOriginalRawScalar_chart :
    (originalCanonicalQLoopScalarMap.{uR, uS, uMR, uMS} f).comp
        (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR uMR} R)).toHomotopyEquiv.toFun =
      (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uS uMS} S)).toHomotopyEquiv.toFun.comp
        (mixedNQKSpaceMap (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)) := by
  apply ContinuousMap.ext
  intro gamma
  let CR := FGProjectiveCat.{max uR uMR} R
  let CS := FGProjectiveCat.{max uS uMS} S
  let F := StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  let eR := originalNQLoopPointHomeomorph CR
  let eS := originalNQLoopPointHomeomorph CS
  have hRaw := DFunLike.congr_fun
    (originalCanonicalQLoopScalarMap_value.{uR, uS, uMR, uMS} f) (eR gamma)
  have hInner : (mixedNQWeaklyPointedMap F).loopMap (eR.symm (eR gamma)) =
      mixedNQKSpaceMap F gamma :=
    (congrArg (mixedNQWeaklyPointedMap F).loopMap (eR.symm_apply_apply gamma)).trans
      (DFunLike.congr_fun (mixedNQKSpaceMap_wholeWeak_value F) gamma).symm
  exact hRaw.trans (congrArg eS hInner)

/-- The raw scalar square uses the current canonical functor K-space map on all loops. -/
theorem canonicalOriginalRawScalar_current_chart :
    (originalCanonicalQLoopScalarMap.{uR, uS, uMR, uMS} f).comp
        (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR uMR} R)).toHomotopyEquiv.toFun =
      (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uS uMS} S)).toHomotopyEquiv.toFun.comp
        (NQKSpaceFunctorMap (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)) :=
  (canonicalOriginalRawScalar_chart.{uR, uS, uMR, uMS} f).trans
    (congrArg (fun m : C(NQKSpace (FGProjectiveCat.{max uR uMR} R),
      NQKSpace (FGProjectiveCat.{max uS uMS} S)) =>
      (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uS uMS} S)).toHomotopyEquiv.toFun.comp m)
      (mixedNQKSpaceMap_eq_functorMap
        (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)))

/-- Every designated unit and loop time is mapped through the original target chart. -/
theorem canonicalOriginalRawScalar_unit_value (t s : unitInterval) :
    (((originalCanonicalQScalarLoopUnit.{uR, uS, uMR, uMS}
        f).toContinuousMap.toFun t).toContinuousMap).toFun s =
      ((originalNQLoopPointHomeomorph (FGProjectiveCat.{max uS uMS} S))
        ((NQKSpaceFunctorKiUnitRootPath
          (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS}
            f)).toContinuousMap.toFun t)).toContinuousMap.toFun s := by
  let F := StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  have hOriginal := congrArg
    (fun gamma : NQKSpace (FGProjectiveCat.{max uS uMS} S) => gamma.toContinuousMap.toFun s)
    (originalConullScalarCanonicalLoopUnit_value F t)
  have hCurrent := originalConullScalarCanonicalLoopUnit_functorValue F t s
  have hChart := originalNQLoopPointHomeomorph_value (FGProjectiveCat.{max uS uMS} S)
    ((NQKSpaceFunctorKiUnitRootPath F).toContinuousMap.toFun t) s
  exact (originalCanonicalQScalarLoopUnit_value.{uR, uS, uMR, uMS} f t s).trans
    (hOriginal.symm.trans (hCurrent.trans hChart.symm))

/-- The entire designated unit square has only the earned strict chart-point casts. -/
theorem canonicalOriginalRawScalar_unit :
    let CR := FGProjectiveCat.{max uR uMR} R
    let CS := FGProjectiveCat.{max uS uMS} S
    let F := StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
    let eR := originalNQLoopPointHomeomorph CR
    let eS := originalNQLoopPointHomeomorph CS
    let xR := Path.refl (NQReal.basepoint CR)
    let hR := canonicalOriginalQLoopChart_point.{uR, uMR} R
    let hS := canonicalOriginalQLoopChart_point.{uS, uMS} S
    let A := originalCanonicalQLoopScalarMap.{uR, uS, uMR, uMS} f
    let hMap := canonicalOriginalRawScalar_current_chart.{uR, uS, uMR, uMS} f
    (originalCanonicalQScalarLoopUnit.{uR, uS, uMR, uMS} f).cast (congrArg A hR) rfl =
      (((NQKSpaceFunctorKiUnitRootPath F).map eS.continuous_toFun).cast rfl hS.symm).cast
        (congrArg (fun m : C(NQKSpace CR, BasedSplitExactQLoop.originalQLoops (C := CS)) =>
          m xR) hMap) rfl := by
  apply Path.ext
  funext t
  apply Path.ext
  funext s
  exact canonicalOriginalRawScalar_unit_value.{uR, uS, uMR, uMS} f t s

/-- Every actual current successor Ki map is the old raw scalar map in the original charts. -/
theorem canonicalOriginalScalarKi_positive_chart (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR uMR} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R)))) :
    originalCanonicalQPositiveScalarMap.{uR, uS, uMR, uMS} f n
        (canonicalOriginalQPositiveChart.{uR, uMR} R n a) =
      canonicalOriginalQPositiveChart.{uS, uMS} S n
        (NQKSpaceFunctorKiMap
          (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) (n + 1) a) := by
  let CR := FGProjectiveCat.{max uR uMR} R
  let CS := FGProjectiveCat.{max uS uMS} S
  let F := StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  let eR := originalNQLoopPointHomeomorph CR
  let eS := originalNQLoopPointHomeomorph CS
  let A := originalCanonicalQLoopScalarMap.{uR, uS, uMR, uMS} f
  let T := NQKSpaceFunctorMap F
  let U := originalCanonicalQScalarLoopUnit.{uR, uS, uMR, uMS} f
  let V := NQKSpaceFunctorKiUnitRootPath F
  let hR := canonicalOriginalQLoopChart_point.{uR, uMR} R
  let hS := canonicalOriginalQLoopChart_point.{uS, uMS} S
  let p := U.cast (congrArg A hR) rfl
  let q := (V.map eS.continuous_toFun).cast rfl hS.symm
  let hMap := canonicalOriginalRawScalar_current_chart.{uR, uS, uMR, uMS} f
  have hUnit : p = q.cast
      (congrArg (fun m : C(NQKSpace CR, BasedSplitExactQLoop.originalQLoops (C := CS)) =>
        m (Path.refl (NQReal.basepoint CR))) hMap) rfl :=
    canonicalOriginalRawScalar_unit.{uR, uS, uMR, uMS} f
  have hLeft := rootedPositiveStrictPrecompose n eR.toHomotopyEquiv.toFun A hR U a
  have hMiddle := rootedPositiveMapEqOfWholeValues n
    (A.comp eR.toHomotopyEquiv.toFun) (eS.toHomotopyEquiv.toFun.comp T) hMap p q hUnit a
  have hRight := rootedPositiveStrictPostcompose n T eS.toHomotopyEquiv.toFun hS V a
  have hKi := NQKSpaceFunctorKiMap_succ_apply F n a
  rw [canonicalOriginalQPositiveChart_apply, canonicalOriginalQPositiveChart_apply,
    originalCanonicalQPositiveScalarMap_apply]
  exact hLeft.symm.trans (hMiddle.trans (hRight.symm.trans
    (congrArg (HomotopyGroup.mapHomOfEq eS.toHomotopyEquiv.toFun hS n) hKi.symm)))

/-- The original normalized independent-plus comparison is natural for the actual current Ki map. -/
theorem canonicalOriginalScalarKi_plus (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (StableGL.independentBGLCellTarget R)
      (StableGL.independentBGLCellPoint R)) :
    letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR uMR} R))
        (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R)))) :=
      HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR uMR} R))
        (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R))) (Fin (n + 1));
    letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uS uMS} S))
        (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S)))) :=
      HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uS uMS} S))
        (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S))) (Fin (n + 1));
    NQKSpaceFunctorKiMap
        (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) (n + 1)
        (canonicalOriginalPlusQPositiveComparison.{uR, uMR, uNR} R n a) =
      canonicalOriginalPlusQPositiveComparison.{uS, uMS, uNS} S n
        (StableGL.originalIndependentPlusPositiveScalarMap f n a) := by
  letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR uMR} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R)))) :=
    HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR uMR} R))
      (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R))) (Fin (n + 1))
  letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uS uMS} S))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S)))) :=
    HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uS uMS} S))
      (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S))) (Fin (n + 1))
  apply (canonicalOriginalQPositiveChart.{uS, uMS} S n).injective
  have hChart := canonicalOriginalScalarKi_positive_chart.{uR, uS, uMR, uMS} f n
    (canonicalOriginalPlusQPositiveComparison.{uR, uMR, uNR} R n a)
  have hSource : canonicalOriginalQPositiveChart.{uR, uMR} R n
      (canonicalOriginalPlusQPositiveComparison.{uR, uMR, uNR} R n a) =
    originalNormalizedPlusQPositiveMulEquiv.{uR, uMR, uNR} R n a := by
    rw [canonicalOriginalPlusQPositiveComparison_apply, MulEquiv.apply_symm_apply]
  have hTarget : canonicalOriginalQPositiveChart.{uS, uMS} S n
      (canonicalOriginalPlusQPositiveComparison.{uS, uMS, uNS} S n
        (StableGL.originalIndependentPlusPositiveScalarMap f n a)) =
    originalNormalizedPlusQPositiveMulEquiv.{uS, uMS, uNS} S n
      (StableGL.originalIndependentPlusPositiveScalarMap f n a) := by
    rw [canonicalOriginalPlusQPositiveComparison_apply, MulEquiv.apply_symm_apply]
  rw [hSource] at hChart
  exact hChart.symm.trans
    ((originalNormalizedPlusQPositiveScalarNaturality.{uR, uS, uMR, uMS, uNR, uNS} f n a).trans
      hTarget.symm)

/-- The existing inverse comparison has its full current-Ki scalar square
in every positive degree. -/
theorem canonicalOriginalScalarKi_plus_inverse (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR uMR} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R)))) :
    letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR uMR} R))
        (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R)))) :=
      HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR uMR} R))
        (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R))) (Fin (n + 1));
    letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uS uMS} S))
        (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S)))) :=
      HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uS uMS} S))
        (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S))) (Fin (n + 1));
    (canonicalOriginalPlusQPositiveComparison.{uS, uMS, uNS} S n).symm
        (NQKSpaceFunctorKiMap
          (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) (n + 1) a) =
      StableGL.originalIndependentPlusPositiveScalarMap f n
        ((canonicalOriginalPlusQPositiveComparison.{uR, uMR, uNR} R n).symm a) := by
  letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR uMR} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R)))) :=
    HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR uMR} R))
      (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R))) (Fin (n + 1))
  letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uS uMS} S))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S)))) :=
    HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uS uMS} S))
      (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S))) (Fin (n + 1))
  rw [canonicalOriginalPlusQPositiveComparison_symm_apply,
    canonicalOriginalPlusQPositiveComparison_symm_apply]
  have h := canonicalOriginalScalarKi_positive_chart.{uR, uS, uMR, uMS} f n a
  exact (congrArg (originalNormalizedPlusQPositiveMulEquiv.{uS, uMS, uNS} S n).symm h.symm).trans
    (originalNormalizedPlusQPositiveScalarInverseNaturality.{uR, uS, uMR, uMS, uNR, uNS}
      f n (canonicalOriginalQPositiveChart.{uR, uMR} R n a))

/-- The original native comparison also follows the actual current map on every positive class. -/
theorem canonicalOriginalScalarKi_native (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (RingK0.projectiveZeroSpace.{uR, uMR, uNR} R)
      (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R)) :
    letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR uMR} R))
        (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R)))) :=
      HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR uMR} R))
        (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R))) (Fin (n + 1));
    letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uS uMS} S))
        (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S)))) :=
      HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uS uMS} S))
        (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S))) (Fin (n + 1));
    NQKSpaceFunctorKiMap
        (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) (n + 1)
        ((canonicalOriginalQPositiveChart.{uR, uMR} R n).symm
          (originalNativeZeroQPositiveMulEquiv.{uR, uMR, uNR} R n a)) =
      (canonicalOriginalQPositiveChart.{uS, uMS} S n).symm
        (originalNativeZeroQPositiveMulEquiv.{uS, uMS, uNS} S n
          (StableGL.originalNativePositiveScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f n a)) := by
  letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR uMR} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R)))) :=
    HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR uMR} R))
      (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R))) (Fin (n + 1))
  letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uS uMS} S))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S)))) :=
    HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uS uMS} S))
      (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S))) (Fin (n + 1))
  apply (canonicalOriginalQPositiveChart.{uS, uMS} S n).injective
  have h := canonicalOriginalScalarKi_positive_chart.{uR, uS, uMR, uMS} f n
    ((canonicalOriginalQPositiveChart.{uR, uMR} R n).symm
      (originalNativeZeroQPositiveMulEquiv.{uR, uMR, uNR} R n a))
  rw [MulEquiv.apply_symm_apply] at h ⊢
  exact h.symm.trans
    (originalNativeZeroQPositiveScalarNaturality.{uR, uS, uMR, uMS, uNR, uNS} f n a)

/-- The original native inverse follows the current Ki scalar map without changing its families. -/
theorem canonicalOriginalScalarKi_native_inverse (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uR uMR} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R)))) :
    (originalNativeZeroQPositiveMulEquiv.{uS, uMS, uNS} S n).symm
        (canonicalOriginalQPositiveChart.{uS, uMS} S n
          (NQKSpaceFunctorKiMap
            (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) (n + 1) a)) =
      StableGL.originalNativePositiveScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f n
        ((originalNativeZeroQPositiveMulEquiv.{uR, uMR, uNR} R n).symm
          (canonicalOriginalQPositiveChart.{uR, uMR} R n a)) := by
  have h := canonicalOriginalScalarKi_positive_chart.{uR, uS, uMR, uMS} f n a
  exact (congrArg (originalNativeZeroQPositiveMulEquiv.{uS, uMS, uNS} S n).symm h.symm).trans
    (originalNativeZeroQPositiveScalarInverseNaturality.{uR, uS, uMR, uMS, uNR, uNS}
      f n (canonicalOriginalQPositiveChart.{uR, uMR} R n a))

/-- Every current degree-zero class retains its canonical fixed RingK0 scalar value. -/
theorem canonicalOriginalScalarKi_zero
    (a : HomotopyGroup.Pi 0 (NQKSpace (FGProjectiveCat.{max uR uMR} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R)))) :
    StableGL.originalQProjectiveComponentsK0.{uS, uMS} S
        (HomotopyGroup.pi0EquivZerothHomotopy
          (X := NQKSpace (FGProjectiveCat.{max uS uMS} S))
          (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S)))
          (NQKSpaceFunctorKiMap
            (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) 0 a)) =
      FGProjectiveCat.scalarExtensionK0.{uR, uS} f
        (StableGL.originalQProjectiveComponentsK0.{uR, uMR} R
          (HomotopyGroup.pi0EquivZerothHomotopy
            (X := NQKSpace (FGProjectiveCat.{max uR uMR} R))
            (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R))) a)) := by
  let CR := FGProjectiveCat.{max uR uMR} R
  let CS := FGProjectiveCat.{max uS uMS} S
  let F := StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  let c := HomotopyGroup.pi0EquivZerothHomotopy
    (X := NQKSpace CR) (x := Path.refl (NQReal.basepoint CR)) a
  have hComponents (c : ZerothHomotopy (NQKSpace CR)) :
      ZerothHomotopy.lift
          (fun gamma : NQKSpace CR => ZerothHomotopy.mk (NQKSpaceFunctorMap F gamma))
          (fun {_ _} p => ZerothHomotopy.sound (p.map (NQKSpaceFunctorMap F).continuous)) c =
        mixedNQKSpacePiZeroMap F c := by
    induction c using ZerothHomotopy.rec with
    | mk gamma =>
      rw [ZerothHomotopy.lift_mk, mixedNQKSpacePiZeroMap_mk]
      exact congrArg ZerothHomotopy.mk
        (DFunLike.congr_fun (mixedNQKSpaceMap_eq_functorMap F) gamma).symm
  have hZero := (NQKSpaceFunctorKiMap_zero_components F a).trans (hComponents c)
  exact (congrArg (StableGL.originalQProjectiveComponentsK0.{uS, uMS} S) hZero).trans
    ((StableGL.mixedOriginalQEveryComponentK0Naturality.{uR, uS, uMR, uMS, 0, 0} f).2.2 c)

/-- The current degree-one map uses the unchanged original independent-plus K1 dictionary. -/
theorem canonicalOriginalScalarKi_one
    (a : HomotopyGroup.Pi 1 (NQKSpace (FGProjectiveCat.{max uR uMR} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R)))) :
    letI : Group (HomotopyGroup.Pi (0 + 1) (NQKSpace (FGProjectiveCat.{max uR uMR} R))
        (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R)))) :=
      HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR uMR} R))
        (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R))) (Fin (0 + 1));
    letI : Group (HomotopyGroup.Pi (0 + 1) (NQKSpace (FGProjectiveCat.{max uS uMS} S))
        (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S)))) :=
      HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uS uMS} S))
        (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S))) (Fin (0 + 1));
    StableGL.originalIndependentPlusK1Equiv S
        (Additive.ofMul (HomotopyGroup.pi1MulEquivFundamentalGroup
          (X := StableGL.independentBGLCellTarget S) (x := StableGL.independentBGLCellPoint S)
          ((canonicalOriginalPlusQPositiveComparison.{uS, uMS, uNS} S 0).symm
            (NQKSpaceFunctorKiMap
              (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) 1 a)))) =
      K1.mapRingHom f (StableGL.originalIndependentPlusK1Equiv R
        (Additive.ofMul (HomotopyGroup.pi1MulEquivFundamentalGroup
          (X := StableGL.independentBGLCellTarget R) (x := StableGL.independentBGLCellPoint R)
          ((canonicalOriginalPlusQPositiveComparison.{uR, uMR, uNR} R 0).symm a)))) := by
  letI : Group (HomotopyGroup.Pi (0 + 1) (NQKSpace (FGProjectiveCat.{max uR uMR} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R)))) :=
    HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uR uMR} R))
      (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R))) (Fin (0 + 1))
  letI : Group (HomotopyGroup.Pi (0 + 1) (NQKSpace (FGProjectiveCat.{max uS uMS} S))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S)))) :=
    HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uS uMS} S))
      (x := Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S))) (Fin (0 + 1))
  rw [canonicalOriginalPlusQPositiveComparison_symm_apply,
    canonicalOriginalPlusQPositiveComparison_symm_apply]
  have h := canonicalOriginalScalarKi_positive_chart.{uR, uS, uMR, uMS} f 0 a
  let k := fun b => StableGL.originalIndependentPlusK1Equiv S
    (Additive.ofMul (HomotopyGroup.pi1MulEquivFundamentalGroup
      (X := StableGL.independentBGLCellTarget S) (x := StableGL.independentBGLCellPoint S)
      ((originalNormalizedPlusQPositiveMulEquiv.{uS, uMS, uNS} S 0).symm b)))
  exact (congrArg k h.symm).trans
    (originalRawQPublicK1Naturality.{uR, uS, uMR, uMS, uNR, uNS} f
      (canonicalOriginalQPositiveChart.{uR, uMR} R 0 a))

/-- The same current map also uses the unchanged original native K1 dictionary. -/
theorem canonicalOriginalScalarKi_one_native
    (a : HomotopyGroup.Pi 1 (NQKSpace (FGProjectiveCat.{max uR uMR} R))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R)))) :
    StableGL.originalNativeK1Equiv.{uS, uMS, uNS} S
        (Additive.ofMul (HomotopyGroup.pi1MulEquivFundamentalGroup
          (X := RingK0.projectiveZeroSpace.{uS, uMS, uNS} S)
          (x := RingK0.projectiveZeroPoint.{uS, uMS, uNS} S)
          ((originalNativeZeroQPositiveMulEquiv.{uS, uMS, uNS} S 0).symm
            (canonicalOriginalQPositiveChart.{uS, uMS} S 0
              (NQKSpaceFunctorKiMap
                (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) 1 a))))) =
      K1.mapRingHom f (StableGL.originalNativeK1Equiv.{uR, uMR, uNR} R
        (Additive.ofMul (HomotopyGroup.pi1MulEquivFundamentalGroup
          (X := RingK0.projectiveZeroSpace.{uR, uMR, uNR} R)
          (x := RingK0.projectiveZeroPoint.{uR, uMR, uNR} R)
          ((originalNativeZeroQPositiveMulEquiv.{uR, uMR, uNR} R 0).symm
            (canonicalOriginalQPositiveChart.{uR, uMR} R 0 a))))) := by
  have h := canonicalOriginalScalarKi_positive_chart.{uR, uS, uMR, uMS} f 0 a
  let k := fun b => StableGL.originalNativeK1Equiv.{uS, uMS, uNS} S
    (Additive.ofMul (HomotopyGroup.pi1MulEquivFundamentalGroup
      (X := RingK0.projectiveZeroSpace.{uS, uMS, uNS} S)
      (x := RingK0.projectiveZeroPoint.{uS, uMS, uNS} S)
      ((originalNativeZeroQPositiveMulEquiv.{uS, uMS, uNS} S 0).symm b)))
  exact (congrArg k h.symm).trans
    (originalRawQNativePublicK1Naturality.{uR, uS, uMR, uMS, uNR, uNS} f
      (canonicalOriginalQPositiveChart.{uR, uMR} R 0 a))

end AlgebraicKTheory.QuillenPlus

end
