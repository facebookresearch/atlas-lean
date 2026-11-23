/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.Comparison.QuillenProjectivePairComparison
public import MathlibExt.KTheory.Ring.StableGeneralLinear.ProjectiveZeroPlusTransport
public import MathlibExt.KTheory.Ring.K0.ComponentProduct
public import MathlibExt.Topology.Homotopy.PointRelativeComposition
public import MathlibExt.KTheory.Exact.Extension.OriginalQK0ComparisonCompatibility
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Quillen's Q-construction and the plus construction for rings

For an associative unital ring `R`, this module constructs a based homotopy
equivalence from the Q-construction loop space on finitely generated
projective `R`-modules to `RingK0 R × StableGL.independentBGLCellTarget R`.
The K₀ factor has the discrete topology, and the plus factor is an
independently constructed cell model for the stable general linear group.

The forward and inverse maps preserve the chosen basepoints, and both
inverse homotopies fix these basepoints. The first coordinate of the
comparison agrees at each point with the canonical K₀ class from the Q/S
comparison. Projective and realization universe parameters are independent.

## Main results

* `quillenIndependentPlusEquivalence_exists`: the based Q/plus equivalence,
  with its forward and inverse maps.
* `projectiveQLoopToNativePair_first_eq_canonicalK0`: the canonical K₀
  coordinate of the projective comparison.
* `quillenIndependentPlusEquivalence_canonicalK0_exists`: the equivalence
  with this canonical K₀ coordinate.
-/

noncomputable section

open CategoryTheory Topology
open scoped ContinuousMap

universe u v w

namespace AlgebraicKTheory.QuillenPlus

variable (R : Type u) [Ring R]

private local instance fixedRingK0Topology : TopologicalSpace (RingK0 R) :=
  (RingK0.discreteSpace R).str

/-- The product of the discrete group `RingK0 R` with the independently
constructed cell-plus space. -/
public abbrev independentPlusProduct : TopCat.{u + 1} :=
  letI : TopologicalSpace (RingK0 R) := (RingK0.discreteSpace R).str
  TopCat.of (RingK0 R × StableGL.independentBGLCellTarget R)

/-- A based homotopy equivalence from the Q-construction loop space to the
product of K₀ with the cell-plus space. It specifies the forward and inverse
maps, both basepoint-relative inverse homotopies, and the K₀ coordinate at
every point. The ring is associative and unital; the projective and
realization universes are independent. -/
public theorem quillenIndependentPlusEquivalence_exists :
    letI : TopologicalSpace (RingK0 R) := (RingK0.discreteSpace R).str
    let C := FGProjectiveCat.{max u v} R
    let Q := BasedSplitExactQLoop.originalQLoops (C := C)
    let q := BasedSplitExactQLoop.constantQLoop (C := C)
    let N := RingK0.projectiveOriginalSpace.{u, v, w} R
    let n := RingK0.projectiveOriginalPoint.{u, v, w} R
    let Z := RingK0.projectiveZeroSpace.{u, v, w} R
    let z := RingK0.projectiveZeroPoint.{u, v, w} R
    let B := StableGL.independentBGLCellTarget R
    let b := StableGL.independentBGLCellPoint R
    let T := independentPlusProduct R
    let t : T := (0, b)
    ∃ d : Q ≃ₕ N, d.toFun = projectiveQLoopToNativePair.{u, v, w} R ∧
      d.toFun q = n ∧ d.invFun n = q ∧
      Nonempty (ContinuousMap.HomotopyRel (d.invFun.comp d.toFun) (ContinuousMap.id Q) {q}) ∧
      Nonempty (ContinuousMap.HomotopyRel (d.toFun.comp d.invFun) (ContinuousMap.id N) {n}) ∧
      ∃ a : Z ≃ₕ B, a.toFun z = b ∧ a.invFun b = z ∧
        Nonempty (ContinuousMap.HomotopyRel (a.invFun.comp a.toFun) (ContinuousMap.id Z) {z}) ∧
        Nonempty (ContinuousMap.HomotopyRel (a.toFun.comp a.invFun) (ContinuousMap.id B) {b}) ∧
        ∃ e : Q ≃ₕ T,
          e.toFun = ((ContinuousMap.id (RingK0 R)).prodMap a.toFun).comp
            ((RingK0.projectiveProductForward.{u, v, w} R).comp
              (projectiveQLoopToNativePair.{u, v, w} R)) ∧
          e.invFun = d.invFun.comp ((RingK0.projectiveProductInverse.{u, v, w} R).comp
            ((ContinuousMap.id (RingK0 R)).prodMap a.invFun)) ∧
          e.toFun q = t ∧ e.invFun t = q ∧
          Nonempty (ContinuousMap.HomotopyRel (e.invFun.comp e.toFun) (ContinuousMap.id Q) {q}) ∧
          Nonempty (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun) (ContinuousMap.id T) {t}) ∧
          ∀ x : Q, (e.toFun x).1 =
            (RingK0.projectiveProductForward.{u, v, w} R
              (projectiveQLoopToNativePair.{u, v, w} R x)).1 := by
  let C := FGProjectiveCat.{max u v} R
  let Q := BasedSplitExactQLoop.originalQLoops (C := C)
  let q := BasedSplitExactQLoop.constantQLoop (C := C)
  let N := RingK0.projectiveOriginalSpace.{u, v, w} R
  let n := RingK0.projectiveOriginalPoint.{u, v, w} R
  let Z := RingK0.projectiveZeroSpace.{u, v, w} R
  let z := RingK0.projectiveZeroPoint.{u, v, w} R
  let B := StableGL.independentBGLCellTarget R
  let b := StableGL.independentBGLCellPoint R
  let P := RingK0.projectiveProductSpace.{u, v, w} R
  let p := RingK0.projectiveProductPoint.{u, v, w} R
  let T := independentPlusProduct R
  let t : T := (0, b)
  obtain ⟨d, hdF, hdq, hdn, ⟨LD⟩, ⟨RD⟩⟩ :=
    projectiveQLoopNativePairEquivalence_exists.{u, v, w} R
  obtain ⟨a, haz, hab, ⟨LA⟩, ⟨RA⟩⟩ :=
    StableGL.nativeProjectiveZeroPlusEquivalence_exists.{u, v, w} R
  let E := RingK0.projectiveProductHomotopyEquiv.{u, v, w} R
  have hEF := RingK0.projectiveProductHomotopyEquiv_toFun.{u, v, w} R
  have hEI := RingK0.projectiveProductHomotopyEquiv_invFun.{u, v, w} R
  have hEn : E.toFun n = p :=
    (congrArg (fun f : C(N, P) => f n) hEF).trans
      (RingK0.projectiveProductForward_point.{u, v, w} R)
  have hEp : E.invFun p = n :=
    (congrArg (fun f : C(P, N) => f p) hEI).trans
      (RingK0.projectiveProductInverse_point.{u, v, w} R)
  let LE : ContinuousMap.HomotopyRel
      (E.invFun.comp E.toFun) (ContinuousMap.id N) {n} :=
    (RingK0.projectiveProductLeftHomotopyRel.{u, v, w} R).cast
      (congrArg₂ (fun (g : C(P, N)) (f : C(N, P)) => g.comp f) hEI.symm hEF.symm) rfl
  let RE : ContinuousMap.HomotopyRel
      (E.toFun.comp E.invFun) (ContinuousMap.id P) {p} :=
    (RingK0.projectiveProductRightHomotopyRel.{u, v, w} R).cast
      (congrArg₂ (fun (f : C(N, P)) (g : C(P, N)) => f.comp g) hEF.symm hEI.symm) rfl
  let e₁ := d.trans E
  have h₁q : e₁.toFun q = p := (congrArg E.toFun hdq).trans hEn
  have h₁p : e₁.invFun p = q := (congrArg d.invFun hEp).trans hdn
  let L₁ := d.transLeftHomotopyRel E q n hdq LD LE
  let R₁ := d.transRightHomotopyRel E n p hEp RD RE
  let K := ContinuousMap.HomotopyEquiv.refl (RingK0 R)
  let A := K.prodCongr a
  let LK : ContinuousMap.HomotopyRel
      (K.invFun.comp K.toFun) (ContinuousMap.id (RingK0 R)) {(0 : RingK0 R)} :=
    (ContinuousMap.HomotopyRel.refl (ContinuousMap.id (RingK0 R)) {(0 : RingK0 R)}).cast
      (by apply ContinuousMap.ext; intro x; rfl) rfl
  let RK : ContinuousMap.HomotopyRel
      (K.toFun.comp K.invFun) (ContinuousMap.id (RingK0 R)) {(0 : RingK0 R)} :=
    (ContinuousMap.HomotopyRel.refl (ContinuousMap.id (RingK0 R)) {(0 : RingK0 R)}).cast
      (by apply ContinuousMap.ext; intro x; rfl) rfl
  have hp : p = ((0 : RingK0 R), z) :=
    RingK0.projectiveProductPoint_eq_pair.{u, v, w} R
  have hAt : A.toFun p = t :=
    (congrArg A.toFun hp).trans (Prod.ext rfl haz)
  have hAp : A.invFun t = p := by
    have hAinv : A.invFun = (ContinuousMap.id (RingK0 R)).prodMap a.invFun := rfl
    have hpointEq : A.invFun t = ((0 : RingK0 R), a.invFun b) :=
      (congrArg (fun f : C(T, P) => f t) hAinv).trans
        (ContinuousMap.prodMap_apply (ContinuousMap.id (RingK0 R)) a.invFun t)
    have hpointPair : ((0 : RingK0 R), a.invFun b) = ((0 : RingK0 R), z) :=
      Prod.ext rfl hab
    exact hpointEq.trans (hpointPair.trans hp.symm)
  let LP₀ := K.prodCongrLeftHomotopyRel a (0 : RingK0 R) z LK LA
  let LP : ContinuousMap.HomotopyRel
      (A.invFun.comp A.toFun) (ContinuousMap.id P) {p} :=
    Eq.mp (congrArg (fun x : P => ContinuousMap.HomotopyRel
      (A.invFun.comp A.toFun) (ContinuousMap.id P) {x}) hp.symm) LP₀
  let RT := K.prodCongrRightHomotopyRel a (0 : RingK0 R) b RK RA
  let e := e₁.trans A
  let L := e₁.transLeftHomotopyRel A q p h₁q L₁ LP
  let S := e₁.transRightHomotopyRel A p t hAp R₁ RT
  have heq : e.toFun q = t := (congrArg A.toFun h₁q).trans hAt
  have het : e.invFun t = q := (congrArg e₁.invFun hAp).trans h₁p
  have hForward : e.toFun = ((ContinuousMap.id (RingK0 R)).prodMap a.toFun).comp
      ((RingK0.projectiveProductForward.{u, v, w} R).comp
        (projectiveQLoopToNativePair.{u, v, w} R)) := by
    change ((ContinuousMap.id (RingK0 R)).prodMap a.toFun).comp
        (E.toFun.comp d.toFun) = _
    exact congrArg (fun k => ((ContinuousMap.id (RingK0 R)).prodMap a.toFun).comp k)
      (congrArg₂ (fun (f : C(N, P)) (g : C(Q, N)) => f.comp g) hEF hdF)
  have hInverse : e.invFun = d.invFun.comp ((RingK0.projectiveProductInverse.{u, v, w} R).comp
      ((ContinuousMap.id (RingK0 R)).prodMap a.invFun)) := by
    change d.invFun.comp (E.invFun.comp
      ((ContinuousMap.id (RingK0 R)).prodMap a.invFun)) = _
    exact congrArg (fun k => d.invFun.comp
      (k.comp ((ContinuousMap.id (RingK0 R)).prodMap a.invFun))) hEI
  have hClass : ∀ x : Q, (e.toFun x).1 =
      (RingK0.projectiveProductForward.{u, v, w} R
        (projectiveQLoopToNativePair.{u, v, w} R x)).1 := by
    intro x
    exact congrArg (fun f : C(Q, T) => (f x).1) hForward
  exact ⟨d, hdF, hdq, hdn, ⟨LD⟩, ⟨RD⟩,
    a, haz, hab, ⟨LA⟩, ⟨RA⟩,
    e, hForward, hInverse, heq, het, ⟨L⟩, ⟨S⟩, hClass⟩

end AlgebraicKTheory.QuillenPlus

end


noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Topology
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open CategoryTheory.CoreLocalizationComparison
open CategoryTheory.SInverseS.ComponentTranslation
open scoped Simplicial ContinuousMap CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory

attribute [local instance] MonoidalActionCategory.diagonalAction

universe u v w

namespace AlgebraicKTheory.QuillenPlus

variable (R : Type u) [Ring R]

private local instance canonicalFixedK0Topology : TopologicalSpace (RingK0 R) :=
  (RingK0.discreteSpace R).str

private local instance canonicalFixedK0Discrete : DiscreteTopology (RingK0 R) := ⟨rfl⟩

/-- The canonical Q/S K₀ class expressed in the fixed ring K₀ group. -/
private abbrev originalQLoopFixedK0
    (x : BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max u v} R)) : RingK0 R :=
  RingK0.projectiveUniverseEquiv.{u, v} R
    (OriginalQK0Comparison.canonicalLoopComponentsK0 (C := FGProjectiveCat.{max u v} R) (ZerothHomotopy.mk x))

private def completedCoreFirstCoordinate :
    C(BasedSplitExactQLoop.completedCoreSpace (C := FGProjectiveCat.{max u v} R), RingK0 R) :=
  (ContinuousMap.fst :
    C(RingK0 R × RingK0.projectiveZeroSpace.{u, v, w} R, RingK0 R)).comp
    ((RingK0.projectiveProductForward.{u, v, w} R).comp
      ((nativeOriginalRealizationIso.{max u v + 1, max u v, w}
        (C := FGProjectiveCat.{max u v} R)).inv.hom.comp
        (SSet.toTop.map (nerveMap (coreAdditivePairEquivalence
          (C := FGProjectiveCat.{max u v} R)).functor)).hom))

private theorem completedCoreFirstCoordinate_vertex
    (a : SInverse (Core (FGProjectiveCat.{max u v} R))
      (Core (FGProjectiveCat.{max u v} R))) :
    completedCoreFirstCoordinate.{u, v, w} R
        (SSet.realizedVertex (ComposableArrows.mk₀ a)) =
      originalQLoopFixedK0.{u, v} R
        (BasedSplitExactQLoop.comparisonMap (C := FGProjectiveCat.{max u v} R)
          (SSet.realizedVertex (ComposableArrows.mk₀ a))) := by
  let C := FGProjectiveCat.{max u v} R
  let E := coreAdditivePairEquivalence (C := C)
  let P : CategoryTheory.SInverseS.Pair C := CoreLocalizationComparison.toPairObj a
  let Pc : Component (C := C) P.difference := ⟨P, rfl⟩
  let z : componentSpace (C := C) P.difference :=
    SSet.realizedVertex (ComposableArrows.mk₀ Pc)
  let I := nativeOriginalRealizationIso.{max u v + 1, max u v, w} (C := C)
  let f := SSet.toTop.map (nerveMap E.functor)
  let va : SSet.toTop.obj (nerve (SInverse (Core C) (Core C))) :=
    SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C))) (ComposableArrows.mk₀ a)
  have hObj : E.functor.obj a = P := coreAdditivePairEquivalence_functor_obj (C := C) a
  have hF : f va =
      SSet.realizedVertex (X := nerve (CategoryTheory.SInverseS.Pair C))
        (ComposableArrows.mk₀ P) :=
    (SSet.realizedVertex_naturality (nerveMap E.functor) (ComposableArrows.mk₀ a)).symm.trans
      ((congrArg
        (fun σ : (nerve (CategoryTheory.SInverseS.Pair C)) _⦋0⦌ =>
          SSet.realizedVertex (X := nerve (CategoryTheory.SInverseS.Pair C)) σ)
        (nerveMap_app_mk₀ E.functor a)).trans
          (congrArg (fun X : CategoryTheory.SInverseS.Pair C =>
            SSet.realizedVertex (X := nerve (CategoryTheory.SInverseS.Pair C))
              (ComposableArrows.mk₀ X)) hObj))
  have hι : SSet.toTop.map (nerveMap (componentProperty (C := C) P.difference).ι) z =
      SSet.realizedVertex (ComposableArrows.mk₀ P) :=
    (SSet.realizedVertex_naturality
      (nerveMap (componentProperty (C := C) P.difference).ι)
      (ComposableArrows.mk₀ Pc)).symm.trans
        (congrArg SSet.realizedVertex
          (nerveMap_app_mk₀ (componentProperty (C := C) P.difference).ι Pc))
  have hClass := congrArg
    (fun y : RingK0.projectiveProductSpace.{u, v, w} R => y.1)
    (RingK0.projectiveProductForward_class.{u, v, w} R P.difference z)
  have hNative : completedCoreFirstCoordinate.{u, v, w} R va =
      RingK0.projectiveGrothendieckEquiv.{u, v} R P.difference := by
    change (RingK0.projectiveProductForward.{u, v, w} R (I.inv (f va))).1 = _
    exact (congrArg (fun y =>
      (RingK0.projectiveProductForward.{u, v, w} R (I.inv y)).1) hF).trans
      (((congrArg (fun y =>
        (RingK0.projectiveProductForward.{u, v, w} R (I.inv y)).1) hι).symm).trans hClass)
  have hOld := OriginalQK0Comparison.projective_comparison_component_dictionary.{u, v} R a
  exact hNative.trans
    ((RingK0.projectiveGrothendieckEquiv_difference.{u, v} R P).trans hOld.symm)

private theorem path_values_equal_in_fixedK0
    {X : Type (max u v + 1)} [TopologicalSpace X]
    (f : C(X, RingK0 R)) {x y : X} (p : Path x y) : f x = f y := by
  let q := p.map (f := f) f.continuous
  have h : q 0 = q 1 :=
    (inferInstance : PreconnectedSpace unitInterval).constant q.continuous
  exact q.source.symm.trans (h.trans q.target)

private theorem completedCoreFirstCoordinate_canonical
    (x : BasedSplitExactQLoop.completedCoreSpace (C := FGProjectiveCat.{max u v} R)) :
    completedCoreFirstCoordinate.{u, v, w} R x =
      originalQLoopFixedK0.{u, v} R
        (BasedSplitExactQLoop.comparisonMap (C := FGProjectiveCat.{max u v} R) x) := by
  let C := FGProjectiveCat.{max u v} R
  let K : SSet.{max u v + 1} := nerve (SInverse (Core C) (Core C))
  obtain ⟨c, hc⟩ := SSet.piZeroToZerothHomotopy_surjective K (ZerothHomotopy.mk x)
  obtain ⟨v₀, rfl⟩ := SSet.π₀.mk_surjective c
  obtain ⟨a, rfl⟩ := (nerveEquiv (C := SInverse (Core C) (Core C))).symm.surjective v₀
  let va : SSet.toTop.obj K := SSet.realizedVertex (ComposableArrows.mk₀ a)
  have ha : ZerothHomotopy.mk va = ZerothHomotopy.mk x :=
    (SSet.piZeroToZerothHomotopy_mk K (nerveEquiv.symm a)).symm.trans hc
  obtain ⟨p⟩ := (show Joined va x from Quotient.exact ha)
  have hFirst : completedCoreFirstCoordinate.{u, v, w} R va =
      completedCoreFirstCoordinate.{u, v, w} R x :=
    path_values_equal_in_fixedK0.{u, v} R (completedCoreFirstCoordinate.{u, v, w} R) p
  let κ := BasedSplitExactQLoop.comparisonMap (C := C)
  have hQ : ZerothHomotopy.mk (κ va) = ZerothHomotopy.mk (κ x) :=
    Quotient.sound ⟨p.map (f := κ) κ.hom.continuous⟩
  exact hFirst.symm.trans
    ((completedCoreFirstCoordinate_vertex.{u, v, w} R a).trans
      (congrArg (fun c => RingK0.projectiveUniverseEquiv.{u, v} R
        (OriginalQK0Comparison.canonicalLoopComponentsK0 (C := FGProjectiveCat.{max u v} R) c)) hQ))

/-- The first coordinate of the projective Q-loop comparison is its
canonical Q/S K₀ class at each point. -/
public theorem projectiveQLoopToNativePair_first_eq_canonicalK0
    (x : BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max u v} R)) :
    (RingK0.projectiveProductForward.{u, v, w} R
      (projectiveQLoopToNativePair.{u, v, w} R x)).1 =
      RingK0.projectiveUniverseEquiv.{u, v} R
        (OriginalQK0Comparison.canonicalLoopComponentsK0 (C := FGProjectiveCat.{max u v} R) (ZerothHomotopy.mk x)) := by
  let C := FGProjectiveCat.{max u v} R
  let hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting :=
    fun S hS => by change Nonempty S.Splitting at hS; exact hS
  let D := BasedSplitExactQLoop.comparison (C := C) hSplit
  let a := D.loopInverse x
  have hActual : (RingK0.projectiveProductForward.{u, v, w} R
      (projectiveQLoopToNativePair.{u, v, w} R x)).1 =
      completedCoreFirstCoordinate.{u, v, w} R a :=
    congrArg (fun y => (RingK0.projectiveProductForward.{u, v, w} R y).1)
      (projectiveQLoopToNativePair_apply.{u, v, w} R x)
  have hQ : ZerothHomotopy.mk
      (BasedSplitExactQLoop.comparisonMap (C := C) a) = ZerothHomotopy.mk x :=
    Quotient.sound ⟨D.loopTargetHomotopy.toHomotopy.evalAt x⟩
  exact hActual.trans
    ((completedCoreFirstCoordinate_canonical.{u, v, w} R a).trans
      (congrArg (fun c => RingK0.projectiveUniverseEquiv.{u, v} R
        (OriginalQK0Comparison.canonicalLoopComponentsK0 (C := FGProjectiveCat.{max u v} R) c)) hQ))


/-- The based Q/plus equivalence with the first coordinate identified as the
canonical Q/S K₀ class on every component. The forward and inverse maps and
both basepoint-relative inverse homotopies are specified. -/
public theorem quillenIndependentPlusEquivalence_canonicalK0_exists :
    letI : TopologicalSpace (RingK0 R) := (RingK0.discreteSpace R).str
    let C := FGProjectiveCat.{max u v} R
    let Q := BasedSplitExactQLoop.originalQLoops (C := C)
    let q := BasedSplitExactQLoop.constantQLoop (C := C)
    let N := RingK0.projectiveOriginalSpace.{u, v, w} R
    let n := RingK0.projectiveOriginalPoint.{u, v, w} R
    let Z := RingK0.projectiveZeroSpace.{u, v, w} R
    let z := RingK0.projectiveZeroPoint.{u, v, w} R
    let B := StableGL.independentBGLCellTarget R
    let b := StableGL.independentBGLCellPoint R
    let T := independentPlusProduct R
    let t : T := (0, b)
    ∃ d : Q ≃ₕ N, d.toFun = projectiveQLoopToNativePair.{u, v, w} R ∧
      d.toFun q = n ∧ d.invFun n = q ∧
      Nonempty (ContinuousMap.HomotopyRel (d.invFun.comp d.toFun) (ContinuousMap.id Q) {q}) ∧
      Nonempty (ContinuousMap.HomotopyRel (d.toFun.comp d.invFun) (ContinuousMap.id N) {n}) ∧
      ∃ a : Z ≃ₕ B, a.toFun z = b ∧ a.invFun b = z ∧
        Nonempty (ContinuousMap.HomotopyRel (a.invFun.comp a.toFun) (ContinuousMap.id Z) {z}) ∧
        Nonempty (ContinuousMap.HomotopyRel (a.toFun.comp a.invFun) (ContinuousMap.id B) {b}) ∧
        ∃ e : Q ≃ₕ T,
          e.toFun = ((ContinuousMap.id (RingK0 R)).prodMap a.toFun).comp
            ((RingK0.projectiveProductForward.{u, v, w} R).comp
              (projectiveQLoopToNativePair.{u, v, w} R)) ∧
          e.invFun = d.invFun.comp ((RingK0.projectiveProductInverse.{u, v, w} R).comp
            ((ContinuousMap.id (RingK0 R)).prodMap a.invFun)) ∧
          e.toFun q = t ∧ e.invFun t = q ∧
          Nonempty (ContinuousMap.HomotopyRel (e.invFun.comp e.toFun) (ContinuousMap.id Q) {q}) ∧
          Nonempty (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun) (ContinuousMap.id T) {t}) ∧
          ∀ x : Q, (e.toFun x).1 =
            RingK0.projectiveUniverseEquiv.{u, v} R
              (OriginalQK0Comparison.canonicalLoopComponentsK0 (C := FGProjectiveCat.{max u v} R)
                (ZerothHomotopy.mk x)) := by
  obtain ⟨d, hdF, hdq, hdn, hLD, hRD, a, haz, hab, hLA, hRA,
      e, hF, hI, heq, het, hL, hR, hClass⟩ :=
    quillenIndependentPlusEquivalence_exists.{u, v, w} R
  exact ⟨d, hdF, hdq, hdn, hLD, hRD, a, haz, hab, hLA, hRA,
    e, hF, hI, heq, het, hL, hR, fun x => (hClass x).trans
      (projectiveQLoopToNativePair_first_eq_canonicalK0.{u, v, w} R x)⟩

end AlgebraicKTheory.QuillenPlus

end
