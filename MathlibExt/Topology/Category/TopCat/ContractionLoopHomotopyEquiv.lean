/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.PathLifting
public import MathlibExt.Topology.Category.TopCat.PointFiber
public import MathlibExt.Topology.Category.TopCat.SquareBoundaryLoopHomotopy
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Point fibers and based loop spaces from a contraction

For a TopCat morphism with continuous-family path lifting, a based
contraction of the total space identifies its literal point fiber with the
compact-open based loop space. The forward map is the projected contraction
path.

The construction assumes no unique or regular lifting, covering-space or
fibration instance, strict-fiber comparison, weak equivalence, bar, `EG`,
or `BG` data.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open CategoryTheory Limits Topology
open scoped Topology.Homotopy

universe u

namespace TopCat


/-- A contraction which fixes its chosen endpoint at every time. -/
structure BasedContraction (E : TopCat.{u}) (e : E) where
  /-- A continuous homotopy from the identity to the constant map at the chosen endpoint. -/
  homotopy : ContinuousMap.Homotopy
    (ContinuousMap.id E) (ContinuousMap.const E e)
  fixed : ∀ t : unitInterval, homotopy (t, e) = e

/-- The contraction path of a point in the literal fiber, projected to the
base. -/
private def contractionLoopPath
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (he : p e = b) (H : BasedContraction E e)
    (x : pointFiber p b) : LoopSpace B b where
  toContinuousMap :=
    { toFun := fun t => p (H.homotopy (t, x.1))
      continuous_toFun := p.hom.continuous.comp
        (H.homotopy.continuous.comp
          (continuous_id.prodMk continuous_const)) }
  source' := by
    change p (H.homotopy (0, x.1)) = b
    rw [H.homotopy.apply_zero]
    exact x.2
  target' := by
    change p (H.homotopy (1, x.1)) = b
    rw [H.homotopy.apply_one]
    exact he

/-- The continuous contraction-formula map from the literal point fiber to
the compact-open based loop space. -/
@[no_expose]
def contractionLoopMap
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (he : p e = b) (H : BasedContraction E e) :
    TopCat.of (pointFiber p b) ⟶ TopCat.of (LoopSpace B b) :=
  TopCat.ofHom
    { toFun := contractionLoopPath p b e he H
      continuous_toFun := by
        apply Path.continuous_uncurry_iff.mp
        exact p.hom.continuous.comp
          (H.homotopy.continuous.comp
            (continuous_snd.prodMk
              (continuous_subtype_val.comp continuous_fst))) }

private theorem contractionLoopMap_apply_private
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (he : p e = b) (H : BasedContraction E e)
    (x : pointFiber p b) (t : unitInterval) :
    contractionLoopMap p b e he H x t = p (H.homotopy (t, x.1)) :=
  rfl

@[simp]
theorem contractionLoopMap_apply
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (he : p e = b) (H : BasedContraction E e)
    (x : pointFiber p b) (t : unitInterval) :
    contractionLoopMap p b e he H x t = p (H.homotopy (t, x.1)) :=
  contractionLoopMap_apply_private p b e he H x t

/-- Reverse based loops and view them as paths on the TopCat interval. -/
private def basedLoopReverse (B : TopCat.{u}) (b : B) :
    TopCat.of (LoopSpace B b) ⟶ TopCat.pathObject B :=
  TopCat.ofHom
    { toFun := fun gamma => gamma.toContinuousMap.comp
        { toFun := fun t => unitInterval.symm (TopCat.I.homeomorph t)
          continuous_toFun := unitInterval.continuous_symm.comp
            TopCat.I.homeomorph.continuous }
      continuous_toFun :=
        (ContinuousMap.continuous_precomp _).comp continuous_induced_dom }

@[reassoc]
private theorem basedLoopReverse_zero (B : TopCat.{u}) (b : B) :
    basedLoopReverse B b ≫ TopCat.pathEvalZero B = TopCat.const b := by
  ext gamma
  rw [ConcreteCategory.comp_apply]
  calc
    TopCat.pathEvalZero B (basedLoopReverse B b gamma) = gamma 1 := by
      simp [TopCat.pathEvalZero, basedLoopReverse]
    _ = b := gamma.target
    _ = TopCat.const b gamma := rfl

/-- Restrict a path on the TopCat interval to the ordinary unit interval. -/
private def restrictPathToUnitInterval (E : TopCat.{u}) :
    TopCat.pathObject E ⟶ TopCat.of C(unitInterval, E) :=
  TopCat.ofHom
    { toFun := fun gamma => gamma.comp
        { toFun := TopCat.I.homeomorph.symm
          continuous_toFun := TopCat.I.homeomorph.symm.continuous }
      continuous_toFun := ContinuousMap.continuous_precomp _ }

/-- The derived continuous lift of the universal reversed based-loop
family. -/
private structure UniversalReversedLoopLift
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (he : p e = b) where
  lift : C(unitInterval × LoopSpace B b, E)
  lift_zero : ∀ gamma : LoopSpace B b, lift (0, gamma) = e
  lift_proj : ∀ (t : unitInterval) (gamma : LoopSpace B b),
    p (lift (t, gamma)) = gamma (unitInterval.symm t)

private theorem universalReversedLoopCompatibility
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (he : p e = b) :
    TopCat.const e ≫ p =
      basedLoopReverse B b ≫ TopCat.pathEvalZero B := by
  rw [basedLoopReverse_zero]
  ext gamma
  exact he

/-- The compact-open family of lifted reversed loops. -/
private noncomputable def liftedReversedLoopFamily
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p)
    (b : B) (e : E) (he : p e = b) :
    TopCat.of (LoopSpace B b) ⟶ TopCat.pathObject E :=
  L.liftFamily (TopCat.const e) (basedLoopReverse B b)
    (universalReversedLoopCompatibility p b e he)

@[reassoc]
private theorem liftedReversedLoopFamily_zero
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p)
    (b : B) (e : E) (he : p e = b) :
    liftedReversedLoopFamily L b e he ≫ TopCat.pathEvalZero E =
      TopCat.const e := by
  apply PathLiftingData.liftFamily_zero

@[reassoc]
private theorem liftedReversedLoopFamily_proj
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p)
    (b : B) (e : E) (he : p e = b) :
    liftedReversedLoopFamily L b e he ≫ TopCat.pathObjectMap p =
      basedLoopReverse B b := by
  apply PathLiftingData.liftFamily_proj

/-- A reviewed path-lifting operator derives the universal reversed-loop
lift; no extra lifting law is assumed. -/
private noncomputable def PathLiftingData.universalReversedLoopLift
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p)
    (b : B) (e : E) (he : p e = b) :
    UniversalReversedLoopLift p b e he where
  lift := ((liftedReversedLoopFamily L b e he ≫
    restrictPathToUnitInterval E).hom.uncurry).comp ContinuousMap.prodSwap
  lift_zero gamma := by
    have h := ConcreteCategory.congr_hom
      (liftedReversedLoopFamily_zero L b e he) gamma
    change (liftedReversedLoopFamily L b e he) gamma 0 = e at h
    have hz : TopCat.I.homeomorph.symm 0 = (0 : TopCat.I.{u}) := by
      apply TopCat.I.homeomorph.injective
      simp
    change (liftedReversedLoopFamily L b e he) gamma
      (TopCat.I.homeomorph.symm 0) = e
    rw [hz]
    exact h
  lift_proj t gamma := by
    have h := ConcreteCategory.congr_hom
      (liftedReversedLoopFamily_proj L b e he) gamma
    have ht := congrArg (fun q => q (TopCat.I.homeomorph.symm t)) h
    change p ((liftedReversedLoopFamily L b e he) gamma
        (TopCat.I.homeomorph.symm t)) =
      gamma (unitInterval.symm t) at ht
    exact ht

private theorem universalReversedLoopLift_one
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p)
    (b : B) (e : E) (he : p e = b)
    (gamma : LoopSpace B b) :
    (PathLiftingData.universalReversedLoopLift L b e he).lift
        (1, gamma) =
      liftedReversedLoopFamily L b e he gamma (1 : TopCat.I.{u}) := by
  change (liftedReversedLoopFamily L b e he) gamma
    (TopCat.I.homeomorph.symm 1) = _
  have ho : TopCat.I.homeomorph.symm 1 = (1 : TopCat.I.{u}) := by
    apply TopCat.I.homeomorph.injective
    simp
  rw [ho]

/-- Endpoint of the derived reversed-loop lift, in the literal point
fiber. -/
private def reversedLoopLiftEndpoint
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (he : p e = b) (U : UniversalReversedLoopLift p b e he) :
    C(LoopSpace B b, pointFiber p b) where
  toFun gamma := ⟨U.lift (1, gamma), by
    rw [U.lift_proj]
    simp⟩
  continuous_toFun := Continuous.subtype_mk
    (U.lift.continuous.comp (continuous_const.prodMk continuous_id)) _

/-- The inverse candidate obtained by taking the endpoint of the lifted
reversed loop. -/
private noncomputable def contractionLoopInverse
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (he : p e = b) (L : PathLiftingData p) :
    TopCat.of (LoopSpace B b) ⟶ TopCat.of (pointFiber p b) :=
  TopCat.ofHom (reversedLoopLiftEndpoint p b e he
    (PathLiftingData.universalReversedLoopLift L b e he))

/-- Square used to prove the loop-side composite homotopic to the identity. -/
private def loopComparisonSquare
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (he : p e = b) (H : BasedContraction E e)
    (U : UniversalReversedLoopLift p b e he) :
    C((LoopSpace B b × unitInterval) × unitInterval, B) where
  toFun z := p (H.homotopy (z.2, U.lift (z.1.2, z.1.1)))
  continuous_toFun := p.hom.continuous.comp
    (H.homotopy.continuous.comp
      (continuous_snd.prodMk
        (U.lift.continuous.comp
          ((continuous_snd.comp continuous_fst).prodMk
            (continuous_fst.comp continuous_fst)))))

/-- The right boundary of `loopComparisonSquare`. -/
private def loopComparisonRightEdge
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (he : p e = b) (H : BasedContraction E e)
    (U : UniversalReversedLoopLift p b e he) :
    C(LoopSpace B b × unitInterval, B) where
  toFun z := p (H.homotopy (z.2, U.lift (1, z.1)))
  continuous_toFun := p.hom.continuous.comp
    (H.homotopy.continuous.comp
      (continuous_snd.prodMk
        (U.lift.continuous.comp
          (continuous_const.prodMk continuous_fst))))

private theorem loopComparisonSquare_left
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (he : p e = b) (H : BasedContraction E e)
    (U : UniversalReversedLoopLift p b e he)
    (gamma : LoopSpace B b) (t : unitInterval) :
    loopComparisonSquare p b e he H U ((gamma, 0), t) = b := by
  change p (H.homotopy (t, U.lift (0, gamma))) = b
  rw [U.lift_zero, H.fixed, he]

private theorem loopComparisonSquare_right
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (he : p e = b) (H : BasedContraction E e)
    (U : UniversalReversedLoopLift p b e he)
    (gamma : LoopSpace B b) (t : unitInterval) :
    loopComparisonSquare p b e he H U ((gamma, 1), t) =
      loopComparisonRightEdge p b e he H U (gamma, t) :=
  rfl

private theorem loopComparisonSquare_bottom
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (he : p e = b) (H : BasedContraction E e)
    (U : UniversalReversedLoopLift p b e he)
    (gamma : LoopSpace B b) (s : unitInterval) :
    loopComparisonSquare p b e he H U ((gamma, s), 0) =
      gamma (unitInterval.symm s) := by
  change p (H.homotopy (0, U.lift (s, gamma))) = _
  rw [H.homotopy.apply_zero]
  exact U.lift_proj s gamma

private theorem loopComparisonSquare_top
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (he : p e = b) (H : BasedContraction E e)
    (U : UniversalReversedLoopLift p b e he)
    (gamma : LoopSpace B b) (s : unitInterval) :
    loopComparisonSquare p b e he H U ((gamma, s), 1) = b := by
  change p (H.homotopy (1, U.lift (s, gamma))) = b
  rw [H.homotopy.apply_one]
  exact he

/-- Inclusion of the literal point fiber. -/
private def pointFiberIncl
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) :
    TopCat.of (pointFiber p b) ⟶ E :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Insert a fixed deformation parameter. -/
private def fiberParameter
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B)
    (r : unitInterval) :
    TopCat.of (pointFiber p b) ⟶
      TopCat.of (pointFiber p b × unitInterval) :=
  TopCat.ofHom
    { toFun := fun x => (x, r)
      continuous_toFun := continuous_id.prodMk continuous_const }

/-- Reversed projected contraction path of a point in the fiber. -/
private def reversedContractionBasePath
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (H : BasedContraction E e) :
    TopCat.of (pointFiber p b) ⟶ TopCat.pathObject B :=
  TopCat.ofHom (ContinuousMap.curry
    { toFun := fun z => p (H.homotopy
        (unitInterval.symm (TopCat.I.homeomorph z.2), z.1.1))
      continuous_toFun := p.hom.continuous.comp
        (H.homotopy.continuous.comp
          ((unitInterval.continuous_symm.comp
            (TopCat.I.homeomorph.continuous.comp continuous_snd)).prodMk
              (continuous_subtype_val.comp continuous_fst))) })

/-- Starting points for the lifted two-parameter fiber deformation. -/
private def fiberDeformationStart
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (H : BasedContraction E e) :
    TopCat.of (pointFiber p b × unitInterval) ⟶ E :=
  TopCat.ofHom
    { toFun := fun z => H.homotopy (unitInterval.symm z.2, z.1.1)
      continuous_toFun := H.homotopy.continuous.comp
        ((unitInterval.continuous_symm.comp continuous_snd).prodMk
          (continuous_subtype_val.comp continuous_fst)) }

@[reassoc]
private theorem fiberDeformationStart_at_zero
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (H : BasedContraction E e) :
    fiberParameter p b 0 ≫ fiberDeformationStart p b e H =
      TopCat.const e := by
  ext x
  simp [fiberParameter, fiberDeformationStart, TopCat.const]

@[reassoc]
private theorem fiberDeformationStart_at_one
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (H : BasedContraction E e) :
    fiberParameter p b 1 ≫ fiberDeformationStart p b e H =
      pointFiberIncl p b := by
  ext x
  simp [fiberParameter, fiberDeformationStart, pointFiberIncl]

/-- Base paths for the lifted two-parameter fiber deformation. -/
private def fiberDeformationBasePath
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (H : BasedContraction E e) :
    TopCat.of (pointFiber p b × unitInterval) ⟶
      TopCat.pathObject B :=
  TopCat.ofHom (ContinuousMap.curry
    { toFun := fun z => p (H.homotopy
        (unitInterval.symm z.1.2 *
          unitInterval.symm (TopCat.I.homeomorph z.2), z.1.1.1))
      continuous_toFun := by
        have hr : Continuous (fun z :
            (pointFiber p b × unitInterval) × TopCat.I.{u} =>
            ((unitInterval.symm z.1.2 : unitInterval) : ℝ)) :=
          continuous_subtype_val.comp
            (unitInterval.continuous_symm.comp
              (continuous_snd.comp continuous_fst))
        have hs : Continuous (fun z :
            (pointFiber p b × unitInterval) × TopCat.I.{u} =>
            ((unitInterval.symm (TopCat.I.homeomorph z.2) :
              unitInterval) : ℝ)) :=
          continuous_subtype_val.comp
            (unitInterval.continuous_symm.comp
              (TopCat.I.homeomorph.continuous.comp continuous_snd))
        have ht : Continuous (fun z :
            (pointFiber p b × unitInterval) × TopCat.I.{u} =>
            unitInterval.symm z.1.2 *
              unitInterval.symm (TopCat.I.homeomorph z.2)) :=
          Continuous.subtype_mk (hr.mul hs) _
        have hx : Continuous (fun z :
            (pointFiber p b × unitInterval) × TopCat.I.{u} =>
            (z.1.1.1 : E)) :=
          continuous_subtype_val.comp
            (continuous_fst.comp continuous_fst)
        exact p.hom.continuous.comp
          (H.homotopy.continuous.comp (ht.prodMk hx)) })

@[reassoc]
private theorem fiberDeformationCompatibility
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (H : BasedContraction E e) :
    fiberDeformationStart p b e H ≫ p =
      fiberDeformationBasePath p b e H ≫ TopCat.pathEvalZero B := by
  ext z
  simp [fiberDeformationStart, fiberDeformationBasePath,
    TopCat.pathEvalZero]

private theorem fiberDeformationBasePath_one
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (H : BasedContraction E e)
    (z : pointFiber p b × unitInterval) :
    fiberDeformationBasePath p b e H z (1 : TopCat.I.{u}) = b := by
  simpa [fiberDeformationBasePath] using z.1.2

@[reassoc]
private theorem fiberDeformationBasePath_at_zero
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (H : BasedContraction E e) :
    fiberParameter p b 0 ≫ fiberDeformationBasePath p b e H =
      reversedContractionBasePath p b e H := by
  ext x t
  simp [fiberParameter, fiberDeformationBasePath,
    reversedContractionBasePath]

@[reassoc]
private theorem fiberDeformationBasePath_at_one
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (H : BasedContraction E e) :
    fiberParameter p b 1 ≫ fiberDeformationBasePath p b e H =
      pointFiberIncl p b ≫ constantBasePathFamily p := by
  ext x t
  simp [fiberParameter, fiberDeformationBasePath, pointFiberIncl,
    constantBasePathFamily]

/-- Continuous lifted paths used in the fiber-side deformation. -/
private noncomputable def PathLiftingData.fiberDeformationLift
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p)
    (b : B) (e : E) (H : BasedContraction E e) :
    TopCat.of (pointFiber p b × unitInterval) ⟶
      TopCat.pathObject E :=
  L.liftFamily (fiberDeformationStart p b e H)
    (fiberDeformationBasePath p b e H)
    (fiberDeformationCompatibility p b e H)

@[reassoc]
private theorem PathLiftingData.fiberDeformationLift_proj
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p)
    (b : B) (e : E) (H : BasedContraction E e) :
    PathLiftingData.fiberDeformationLift L b e H ≫
      TopCat.pathObjectMap p =
      fiberDeformationBasePath p b e H := by
  apply PathLiftingData.liftFamily_proj

/-- Endpoints of the lifted fiber deformation remain in the literal
fiber. -/
private noncomputable def PathLiftingData.fiberDeformationEndpoint
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p)
    (b : B) (e : E) (H : BasedContraction E e) :
    TopCat.of (pointFiber p b × unitInterval) ⟶
      TopCat.of (pointFiber p b) :=
  TopCat.ofHom
    { toFun := fun z =>
        ⟨PathLiftingData.fiberDeformationLift L b e H z 1, by
          have hp := ConcreteCategory.congr_hom
            (PathLiftingData.fiberDeformationLift_proj L b e H) z
          have hp1 := congrArg (fun q => q (1 : TopCat.I.{u})) hp
          change p (PathLiftingData.fiberDeformationLift L b e H z 1) =
            fiberDeformationBasePath p b e H z 1 at hp1
          exact hp1.trans (fiberDeformationBasePath_one p b e H z)⟩
      continuous_toFun := Continuous.subtype_mk
        ((continuous_eval_const (1 : TopCat.I.{u})).comp
          (PathLiftingData.fiberDeformationLift L b e H).hom.continuous) _ }

/-- Restriction of constant transport to the literal point fiber. -/
private def PathLiftingData.constantTransportOnFiber
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p)
    (b : B) : TopCat.of (pointFiber p b) ⟶
      TopCat.of (pointFiber p b) :=
  TopCat.ofHom
    { toFun := fun x => ⟨L.constantTransport x.1, by
          have hp := ConcreteCategory.congr_hom
            L.constantTransport_proj x.1
          exact hp.trans x.2⟩
      continuous_toFun := Continuous.subtype_mk
        (L.constantTransport.hom.continuous.comp continuous_subtype_val) _ }

/-- The constant lift restricted to one literal fiber. -/
private noncomputable def PathLiftingData.constantLiftFiberSquare
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p)
    (b : B) : C(pointFiber p b × TopCat.I.{u}, pointFiber p b) where
  toFun z := ⟨L.constantLift z.1.1 z.2, by
    have hp := ConcreteCategory.congr_hom L.constantLift_proj z.1.1
    have hpt := congrArg (fun q => q z.2) hp
    change p (L.constantLift z.1.1 z.2) =
      constantBasePathFamily p z.1.1 z.2 at hpt
    exact hpt.trans z.1.2⟩
  continuous_toFun := Continuous.subtype_mk
    (L.constantLift.hom.uncurry.continuous.comp
      (continuous_subtype_val.prodMap continuous_id)) _

private theorem PathLiftingData.constantLiftFiberSquare_zero
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p)
    (b : B) (x : pointFiber p b) :
    PathLiftingData.constantLiftFiberSquare L b (x, 0) = x := by
  apply Subtype.ext
  exact ConcreteCategory.congr_hom L.constantLift_zero x.1

private theorem PathLiftingData.constantLiftFiberSquare_one
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p)
    (b : B) (x : pointFiber p b) :
    PathLiftingData.constantLiftFiberSquare L b (x, 1) =
      PathLiftingData.constantTransportOnFiber L b x := by
  apply Subtype.ext
  rfl

private theorem contractionLoopMap_basedLoopReverse
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (he : p e = b) (H : BasedContraction E e) :
    contractionLoopMap p b e he H ≫ basedLoopReverse B b =
      reversedContractionBasePath p b e H := by
  ext x t
  rfl

private theorem fiberDeformationLift_at_zero
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p)
    (b : B) (e : E) (he : p e = b) (H : BasedContraction E e) :
    fiberParameter p b 0 ≫
        PathLiftingData.fiberDeformationLift L b e H =
      contractionLoopMap p b e he H ≫
        liftedReversedLoopFamily L b e he := by
  unfold PathLiftingData.fiberDeformationLift
  unfold liftedReversedLoopFamily
  unfold PathLiftingData.liftFamily
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    rw [fiberDeformationStart_at_zero]
    apply TopCat.ext
    intro x
    rfl
  · simp only [Category.assoc, pullback.lift_snd]
    rw [fiberDeformationBasePath_at_zero,
      contractionLoopMap_basedLoopReverse]

private theorem fiberDeformationLift_at_one
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p)
    (b : B) (e : E) (H : BasedContraction E e) :
    fiberParameter p b 1 ≫
        PathLiftingData.fiberDeformationLift L b e H =
      pointFiberIncl p b ≫ L.constantLift := by
  unfold PathLiftingData.fiberDeformationLift
  unfold PathLiftingData.constantLift PathLiftingData.liftFamily
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    rw [fiberDeformationStart_at_one]
    simp
  · simp only [Category.assoc, pullback.lift_snd]
    rw [fiberDeformationBasePath_at_one]

private theorem PathLiftingData.fiberDeformationEndpoint_zero
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p)
    (b : B) (e : E) (he : p e = b) (H : BasedContraction E e)
    (x : pointFiber p b) :
    PathLiftingData.fiberDeformationEndpoint L b e H (x, 0) =
      contractionLoopInverse p b e he L
        (contractionLoopMap p b e he H x) := by
  apply Subtype.ext
  have h := ConcreteCategory.congr_hom
    (fiberDeformationLift_at_zero L b e he H) x
  have h1 := congrArg (fun q => q (1 : TopCat.I.{u})) h
  change PathLiftingData.fiberDeformationLift L b e H (x, 0) 1 =
    liftedReversedLoopFamily L b e he
      (contractionLoopMap p b e he H x) 1 at h1
  change PathLiftingData.fiberDeformationLift L b e H (x, 0) 1 =
    (PathLiftingData.universalReversedLoopLift L b e he).lift
      (1, contractionLoopMap p b e he H x)
  rw [universalReversedLoopLift_one]
  exact h1

private theorem PathLiftingData.fiberDeformationEndpoint_one
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p)
    (b : B) (e : E) (H : BasedContraction E e)
    (x : pointFiber p b) :
    PathLiftingData.fiberDeformationEndpoint L b e H (x, 1) =
      PathLiftingData.constantTransportOnFiber L b x := by
  apply Subtype.ext
  have h := ConcreteCategory.congr_hom
    (fiberDeformationLift_at_one L b e H) x
  exact congrArg (fun q => q (1 : TopCat.I.{u})) h

/-- The first stage of the fiber-side inverse law. -/
private noncomputable def fiberDeformationHomotopy
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (he : p e = b) (H : BasedContraction E e)
    (L : PathLiftingData p) :
    ContinuousMap.Homotopy
      ((contractionLoopInverse p b e he L).hom.comp
        (contractionLoopMap p b e he H).hom)
      (PathLiftingData.constantTransportOnFiber L b).hom where
  toContinuousMap :=
    (PathLiftingData.fiberDeformationEndpoint L b e H).hom.comp
      ContinuousMap.prodSwap
  map_zero_left x :=
    PathLiftingData.fiberDeformationEndpoint_zero L b e he H x
  map_one_left x :=
    PathLiftingData.fiberDeformationEndpoint_one L b e H x

/-- Constant lifted base paths correct constant transport back to the
identity on the literal fiber. -/
private noncomputable def constantLiftFiberHomotopy
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p)
    (b : B) :
    ContinuousMap.Homotopy (ContinuousMap.id (pointFiber p b))
      (PathLiftingData.constantTransportOnFiber L b).hom where
  toFun z := PathLiftingData.constantLiftFiberSquare L b
    (z.2, TopCat.I.homeomorph.symm z.1)
  continuous_toFun :=
    (PathLiftingData.constantLiftFiberSquare L b).continuous.comp
    (continuous_snd.prodMk
      (TopCat.I.homeomorph.symm.continuous.comp continuous_fst))
  map_zero_left x := by
    have hz : TopCat.I.homeomorph.symm 0 = (0 : TopCat.I.{u}) := by
      apply TopCat.I.homeomorph.injective
      simp
    change PathLiftingData.constantLiftFiberSquare L b
      (x, TopCat.I.homeomorph.symm 0) = x
    rw [hz]
    exact PathLiftingData.constantLiftFiberSquare_zero L b x
  map_one_left x := by
    have ho : TopCat.I.homeomorph.symm 1 = (1 : TopCat.I.{u}) := by
      apply TopCat.I.homeomorph.injective
      simp
    change PathLiftingData.constantLiftFiberSquare L b
      (x, TopCat.I.homeomorph.symm 1) =
        PathLiftingData.constantTransportOnFiber L b x
    rw [ho]
    exact PathLiftingData.constantLiftFiberSquare_one L b x

/-- The square-boundary provider, reversed, gives the loop-side inverse
law in the `forward.comp inverse -> id` orientation. -/
private noncomputable def loopCompositeHomotopy
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (he : p e = b) (H : BasedContraction E e)
    (L : PathLiftingData p) :
    ContinuousMap.Homotopy
      ((contractionLoopMap p b e he H).hom.comp
        (contractionLoopInverse p b e he L).hom)
      (ContinuousMap.id (LoopSpace B b)) := by
  let U := PathLiftingData.universalReversedLoopLift L b e he
  let A := loopComparisonSquare p b e he H U
  let R := loopComparisonRightEdge p b e he H U
  let hLeft := loopComparisonSquare_left p b e he H U
  let hRight := loopComparisonSquare_right p b e he H U
  let hBottom := loopComparisonSquare_bottom p b e he H U
  let hTop := loopComparisonSquare_top p b e he H U
  have hTarget :
      squareRightEdgeLoop b A R hRight hBottom hTop =
        (contractionLoopMap p b e he H).hom.comp
          (contractionLoopInverse p b e he L).hom := by
    apply ContinuousMap.ext
    intro gamma
    apply Path.ext
    funext t
    rfl
  exact (squareBoundaryLoopHomotopy b A R hLeft hRight hBottom hTop).symm.cast
    hTarget rfl

/-- The actual homotopy equivalence from the literal point fiber to based
loops, using only a based contraction and the reviewed path-lifting data. -/
@[no_expose]
noncomputable def contractionLoopHomotopyEquiv
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (he : p e = b) (H : BasedContraction E e)
    (L : PathLiftingData p) :
    ContinuousMap.HomotopyEquiv (pointFiber p b) (LoopSpace B b) where
  toFun := (contractionLoopMap p b e he H).hom
  invFun := (contractionLoopInverse p b e he L).hom
  left_inv := ⟨(fiberDeformationHomotopy p b e he H L).trans
    (constantLiftFiberHomotopy L b).symm⟩
  right_inv := ⟨loopCompositeHomotopy p b e he H L⟩

private theorem contractionLoopHomotopyEquiv_apply_private
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (he : p e = b) (H : BasedContraction E e)
    (L : PathLiftingData p) (x : pointFiber p b)
    (t : unitInterval) :
    contractionLoopHomotopyEquiv p b e he H L x t =
      p (H.homotopy (t, x.1)) :=
  rfl

@[simp]
theorem contractionLoopHomotopyEquiv_apply
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (he : p e = b) (H : BasedContraction E e)
    (L : PathLiftingData p) (x : pointFiber p b)
    (t : unitInterval) :
    contractionLoopHomotopyEquiv p b e he H L x t =
      p (H.homotopy (t, x.1)) :=
  contractionLoopHomotopyEquiv_apply_private p b e he H L x t

/-- The point of the fiber represented by the fixed contraction endpoint is
sent to the constant based loop. -/
@[simp]
theorem contractionLoopMap_basepoint
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)
    (he : p e = b) (H : BasedContraction E e) :
    contractionLoopMap p b e he H ⟨e, he⟩ = Path.refl b := by
  apply Path.ext
  funext t
  rw [contractionLoopMap_apply, H.fixed, he]
  rfl


end TopCat

end
