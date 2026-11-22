/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.DoubleLoopInterchange
import MathlibExt.Topology.Category.CGWH.TensorComparison
import MathlibExt.Topology.Category.CGWH.IntervalActionHomotopy

/-!
# Native suspension coefficient geometry from the actual loop coreflection

Continuous families of based loops lift through the original compact-open
coreflection and its original comparison with native internal Hom. The complete
landing is the supplied continuous family. This permits native coefficient
homotopies to be constructed from the actual boundary-preserving square turn,
without an additional regularity condition on an arbitrary pointed factor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Topology
open scoped MonoidalClosed CGWH.limits unitInterval

namespace PointedCGWH.SuspensionCoefficientGeometry

open PointedCGWH.DoubleLoopInterchangeGeometry

/-- Lift an entire continuous based-loop family through the actual native coreflection. -/
def liftLoopFamily (S : CGWH.{u, v}) (A : PointedCGWH.{u, v})
    (f : CGWH.cgwhToTop.obj S ⟶ TopCat.of
      (LoopSpace (CGWH.cgwhToTop.obj A.right) (underlyingBasepoint A))) :
    S ⟶ (PointedCGWH.loop.obj A).right := by
  let Raw : TopCat.{v} := TopCat.of
    (LoopSpace (CGWH.cgwhToTop.obj A.right) (underlyingBasepoint A))
  let S' := CGWH.cgwhToCompactlyGenerated.obj S
  let mC : S' ⟶ TopCat.toCompactlyGenerated.{u, v}.obj Raw :=
    CompactlyGenerated.adj.{u, v}.homEquiv S' Raw f
  let m : S ⟶ (PointedCGWH.compactOpenLoopCoreflection.obj A).right :=
    CGWH.fullyFaithfulCgwhToCompactlyGenerated.preimage (by
      change S' ⟶ TopCat.toCompactlyGenerated.{u, v}.obj Raw
      exact mC)
  exact m ≫ (PointedCGWH.loopIsoCompactOpenCoreflection.inv.app A).right

/-- The entire landed native family is exactly the original supplied continuous map. -/
@[reassoc]
theorem liftLoopFamily_landing (S : CGWH.{u, v}) (A : PointedCGWH.{u, v})
    (f : CGWH.cgwhToTop.obj S ⟶ TopCat.of
      (LoopSpace (CGWH.cgwhToTop.obj A.right) (underlyingBasepoint A))) :
    CGWH.cgwhToTop.map (liftLoopFamily S A f) ≫ PointedCGWH.loopLanding A = f := by
  let Raw : TopCat.{v} := TopCat.of
    (LoopSpace (CGWH.cgwhToTop.obj A.right) (underlyingBasepoint A))
  let S' := CGWH.cgwhToCompactlyGenerated.obj S
  let mC : S' ⟶ TopCat.toCompactlyGenerated.{u, v}.obj Raw :=
    CompactlyGenerated.adj.{u, v}.homEquiv S' Raw f
  let m : S ⟶ (PointedCGWH.compactOpenLoopCoreflection.obj A).right :=
    CGWH.fullyFaithfulCgwhToCompactlyGenerated.preimage (by
      change S' ⟶ TopCat.toCompactlyGenerated.{u, v}.obj Raw
      exact mC)
  have hm : CGWH.cgwhToCompactlyGenerated.map m = mC :=
    CGWH.fullyFaithfulCgwhToCompactlyGenerated.map_preimage _
  have he : (PointedCGWH.loopIsoCompactOpenCoreflection.inv.app A).right ≫
      (PointedCGWH.loopIsoCompactOpenCoreflection.hom.app A).right =
        𝟙 (PointedCGWH.compactOpenLoopCoreflection.obj A).right :=
    congrArg (fun g => g.right) (PointedCGWH.loopIsoCompactOpenCoreflection.app A).inv_hom_id
  have he' := CGWH.cgwhToTop.congr_map he
  rw [CGWH.cgwhToTop.map_comp, CGWH.cgwhToTop.map_id] at he'
  have h := (CompactlyGenerated.adj.{u, v}.homEquiv S' Raw).symm_apply_apply f
  rw [CompactlyGenerated.adj.{u, v}.homEquiv_counit] at h
  change CGWH.cgwhToTop.map m ≫
      CGWH.cgwhToTop.map (PointedCGWH.loopIsoCompactOpenCoreflection.inv.app A).right ≫
        CGWH.cgwhToTop.map (PointedCGWH.loopIsoCompactOpenCoreflection.hom.app A).right ≫
          CompactlyGenerated.adj.{u, v}.counit.app Raw = f
  calc
    _ = CGWH.cgwhToTop.map m ≫ CompactlyGenerated.adj.{u, v}.counit.app Raw := by
      rw [← Category.assoc
        (CGWH.cgwhToTop.map (PointedCGWH.loopIsoCompactOpenCoreflection.inv.app A).right)
        (CGWH.cgwhToTop.map (PointedCGWH.loopIsoCompactOpenCoreflection.hom.app A).right),
        he', Category.id_comp]
    _ = CompactlyGenerated.compactlyGeneratedToTop.map mC ≫
        CompactlyGenerated.adj.{u, v}.counit.app Raw :=
      congrArg (fun g => CompactlyGenerated.compactlyGeneratedToTop.map g ≫
        CompactlyGenerated.adj.{u, v}.counit.app Raw) hm
    _ = f := h

/-- Every actual loop-family value and every original loop parameter are preserved. -/
theorem liftLoopFamily_apply (S : CGWH.{u, v}) (A : PointedCGWH.{u, v})
    (f : CGWH.cgwhToTop.obj S ⟶ TopCat.of
      (LoopSpace (CGWH.cgwhToTop.obj A.right) (underlyingBasepoint A)))
    (s : CGWH.cgwhToTop.obj S) (t : unitInterval) :
    PointedCGWH.loopLanding A (liftLoopFamily S A f s) t = f s t :=
  congrArg (fun γ => γ t)
    (ConcreteCategory.congr_hom (liftLoopFamily_landing S A f) s)

/-- The actual loop landing is injective because its coreflection counit is pointwise identity. -/
theorem loopLanding_injective (A : PointedCGWH.{u, v}) :
    Function.Injective (PointedCGWH.loopLanding A) := by
  intro γ δ h
  let Raw : TopCat.{v} := TopCat.of
    (LoopSpace (CGWH.cgwhToTop.obj A.right) (underlyingBasepoint A))
  have h' : (PointedCGWH.loopIsoCompactOpenCoreflection.hom.app A).right γ =
      (PointedCGWH.loopIsoCompactOpenCoreflection.hom.app A).right δ := by
    change CompactlyGenerated.adj.{u, v}.counit.app Raw
      ((PointedCGWH.loopIsoCompactOpenCoreflection.hom.app A).right γ) =
        CompactlyGenerated.adj.{u, v}.counit.app Raw
          ((PointedCGWH.loopIsoCompactOpenCoreflection.hom.app A).right δ) at h
    simpa only [CompactlyGenerated.adjCounit_apply] using h
  have heγ := congrArg (fun f : PointedCGWH.loop.obj A ⟶ PointedCGWH.loop.obj A => f.right γ)
    (PointedCGWH.loopIsoCompactOpenCoreflection.app A).hom_inv_id
  have heδ := congrArg (fun f : PointedCGWH.loop.obj A ⟶ PointedCGWH.loop.obj A => f.right δ)
    (PointedCGWH.loopIsoCompactOpenCoreflection.app A).hom_inv_id
  calc
    γ = (PointedCGWH.loopIsoCompactOpenCoreflection.inv.app A).right
        ((PointedCGWH.loopIsoCompactOpenCoreflection.hom.app A).right γ) := heγ.symm
    _ = (PointedCGWH.loopIsoCompactOpenCoreflection.inv.app A).right
        ((PointedCGWH.loopIsoCompactOpenCoreflection.hom.app A).right δ) :=
      congrArg (PointedCGWH.loopIsoCompactOpenCoreflection.inv.app A).right h'
    _ = δ := heδ

/-- A full constant raw-loop value lifts to the original selected native loop point. -/
theorem liftLoopFamily_eq_basepoint (S : CGWH.{u, v}) (A : PointedCGWH.{u, v})
    (f : CGWH.cgwhToTop.obj S ⟶ TopCat.of
      (LoopSpace (CGWH.cgwhToTop.obj A.right) (underlyingBasepoint A)))
    (s : CGWH.cgwhToTop.obj S) (hf : f s = Path.refl (underlyingBasepoint A)) :
    liftLoopFamily S A f s = underlyingBasepoint (PointedCGWH.loop.obj A) := by
  have hl := ConcreteCategory.congr_hom (liftLoopFamily_landing S A f) s
  exact (loopLanding_injective A)
    (hl.trans (hf.trans (PointedCGWH.loopLanding_basepoint A).symm))

private def rawLoopsOfBasedFamily {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (g : C(X × unitInterval, Y)) (y : Y)
    (h₀ : ∀ x, g (x, 0) = y) (h₁ : ∀ x, g (x, 1) = y) : C(X, LoopSpace Y y) :=
  ⟨fun x =>
    { toFun t := g (x, t)
      continuous_toFun := g.continuous.comp (continuous_const.prodMk continuous_id)
      source' := h₀ x
      target' := h₁ x }, Path.continuous_uncurry_iff.mp g.continuous⟩

private def evaluationInSquareCoordinates {X Y Z : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (m : C(X, Y)) (e : X ≃ₜ unitInterval × unitInterval) (h : Z ≃ₜ unitInterval) :
    C(Z × unitInterval, Y) :=
  m.comp ⟨fun z => e.symm (h z.1, z.2),
    e.symm.continuous.comp ((h.continuous.comp continuous_fst).prodMk continuous_snd)⟩

private theorem evaluationInSquareCoordinates_apply {X Y Z : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (m : C(X, Y)) (e : X ≃ₜ unitInterval × unitInterval) (h : Z ≃ₜ unitInterval)
    (x : Z) (s : unitInterval) :
    evaluationInSquareCoordinates m e h (x, s) = m (e.symm (h x, s)) := rfl

/-- Reverse the entire actual native loop through its genuine compact-open comparison. -/
def loopReflectionCarrier (A : PointedCGWH.{u, v}) :
    (PointedCGWH.loop.obj A).right ⟶ (PointedCGWH.loop.obj A).right :=
  liftLoopFamily (PointedCGWH.loop.obj A).right A
    (PointedCGWH.loopLanding A ≫ TopCat.ofHom ⟨Path.symm, Path.continuous_symm⟩)

/-- The full original loop reflection lands in the complete reversed based path. -/
theorem loopReflectionCarrier_landing (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj A).right) :
    PointedCGWH.loopLanding A (loopReflectionCarrier A γ) =
      (PointedCGWH.loopLanding A γ).symm :=
  ConcreteCategory.congr_hom
    (liftLoopFamily_landing (PointedCGWH.loop.obj A).right A
      (PointedCGWH.loopLanding A ≫ TopCat.ofHom ⟨Path.symm, Path.continuous_symm⟩)) γ

/-- The full reflected native loop preserves the actual selected constant-loop point. -/
theorem loopReflectionCarrier_basepoint (A : PointedCGWH.{u, v}) :
    loopReflectionCarrier A (underlyingBasepoint (PointedCGWH.loop.obj A)) =
      underlyingBasepoint (PointedCGWH.loop.obj A) := by
  have h : PointedCGWH.loopLanding A
      (loopReflectionCarrier A (underlyingBasepoint (PointedCGWH.loop.obj A))) =
        Path.refl (underlyingBasepoint A) :=
    (loopReflectionCarrier_landing A (underlyingBasepoint (PointedCGWH.loop.obj A))).trans
      (congrArg Path.symm (PointedCGWH.loopLanding_basepoint A))
  exact (loopLanding_injective A) (h.trans (PointedCGWH.loopLanding_basepoint A).symm)

/-- Reversal is an actual complete pointed native-loop morphism. -/
def loopReflection (A : PointedCGWH.{u, v}) :
    PointedCGWH.loop.obj A ⟶ PointedCGWH.loop.obj A :=
  Under.homMk (loopReflectionCarrier A) (by
    apply ConcreteCategory.hom_ext
    intro p
    change loopReflectionCarrier A ((PointedCGWH.loop.obj A).hom p) =
      (PointedCGWH.loop.obj A).hom p
    have hp : p = (show CGWH.point.{u, v} from PUnit.unit) := by
      change PUnit.{v + 1} at p
      cases p
      rfl
    subst p
    exact loopReflectionCarrier_basepoint A)

/-- The actual reflection reverses every complete original native loop parameter. -/
theorem loopReflection_landing_evaluation (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj A).right) (t : unitInterval) :
    PointedCGWH.loopLanding A ((loopReflection A).right γ) t =
      PointedCGWH.loopLanding A γ (σ t) :=
  congrArg (fun p => p t) (loopReflectionCarrier_landing A γ)

/-- The complete native identity loop is the actual curry of the right unit isomorphism. -/
def identityCircleLoop : (𝟙_ PointedCGWH.{u, v}) ⟶
    PointedCGWH.loop.obj PointedCGWH.sphereOne :=
  MonoidalClosed.curry (ρ_ PointedCGWH.sphereOne).hom

/-- Circle reflection is the original uncurrying of the reversed identity loop. -/
def circleReflection : PointedCGWH.sphereOne.{u, v} ⟶ PointedCGWH.sphereOne :=
  (ρ_ PointedCGWH.sphereOne).inv ≫
    MonoidalClosed.uncurry (identityCircleLoop ≫ loopReflection PointedCGWH.sphereOne)

/-- The original free-unit adjunction identifies complete pointed unit maps with their values. -/
def unitHomEquiv (A : PointedCGWH.{u, v}) :
    ((𝟙_ PointedCGWH.{u, v}) ⟶ A) ≃ A.right :=
  ((Under.costarAdjForget CGWH.point).homEquiv CGWH.point A).trans (CGWH.pointHomEquiv A.right)

/-- The actual free point of the original pointed unit is its adjunction unit value. -/
def unitFreePoint : (𝟙_ PointedCGWH.{u, v}).right :=
  (Under.costarAdjForget CGWH.point).unit.app CGWH.point PUnit.unit

/-- Every complete original unit map retains its underlying value at the actual free point. -/
theorem unitHomEquiv_apply (A : PointedCGWH.{u, v}) (f : (𝟙_ PointedCGWH) ⟶ A) :
    unitHomEquiv A f = f.right unitFreePoint := rfl

/-- The full pointed unit correspondence is the original adjunction followed by point evaluation. -/
theorem unitHomEquiv_eq_pointHomEquiv (A : PointedCGWH.{u, v})
    (f : (𝟙_ PointedCGWH) ⟶ A) :
    unitHomEquiv A f = CGWH.pointHomEquiv A.right
      ((Under.costarAdjForget CGWH.point).homEquiv CGWH.point A f) := rfl

/-- The original point correspondence preserves every entire native map composite. -/
theorem pointHomEquiv_comp {A B : CGWH.{u, v}} (i : CGWH.point ⟶ A) (f : A ⟶ B) :
    CGWH.pointHomEquiv B (i ≫ f) = f (CGWH.pointHomEquiv A i) := rfl

/-- The actual interval-point unit map has exactly its original native parameter value. -/
theorem unitHomEquiv_spherePoint (t : TopCat.I.{v}) :
    unitHomEquiv PointedCGWH.sphereOne (spherePoint t) = PointedCGWH.sphereOneParam t := by
  change CGWH.pointHomEquiv PointedCGWH.sphereOne.right
    (((Under.costarAdjForget CGWH.point).homEquiv CGWH.point PointedCGWH.sphereOne)
      (((Under.costarAdjForget CGWH.point).homEquiv CGWH.point PointedCGWH.sphereOne).symm
        (ConcreteCategory.ofHom (ContinuousMap.const _ (PointedCGWH.sphereOneParam t))))) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- Evaluation of a complete unit map retains the actual right-unit insertion and uncurrying. -/
theorem unitPoint_uncurry (K A : PointedCGWH.{u, v})
    (s : (𝟙_ PointedCGWH) ⟶ K) (f : (𝟙_ PointedCGWH) ⟶ (ihom K).obj A) :
    f ≫ CategoryTheory.MonoidalClosed.NativeEvaluationInterchange.pointEvaluation K A s =
      s ≫ (ρ_ K).inv ≫ MonoidalClosed.uncurry f := by
  rw [CategoryTheory.MonoidalClosed.NativeEvaluationInterchange.pointEvaluation_comp]
  have hunit : (λ_ (𝟙_ PointedCGWH.{u, v})).inv = (ρ_ (𝟙_ PointedCGWH)).inv :=
    congrArg (fun e : (𝟙_ PointedCGWH ⊗ 𝟙_ PointedCGWH) ≅ 𝟙_ PointedCGWH => e.inv)
      (Iso.ext (unitors_equal (C := PointedCGWH)))
  rw [hunit, ← rightUnitor_inv_naturality_assoc]

/-- Evaluating the entire native identity loop gives the actual original interval point map. -/
theorem identityCircleLoop_eval (t : TopCat.I.{v}) :
    identityCircleLoop ≫ PointedCGWH.loopEvalAt PointedCGWH.sphereOne t = spherePoint t := by
  rw [← pointEvaluation_eq_loopEvalAt, unitPoint_uncurry]
  change spherePoint t ≫ (ρ_ PointedCGWH.sphereOne).inv ≫
      MonoidalClosed.uncurry (MonoidalClosed.curry (ρ_ PointedCGWH.sphereOne).hom) = _
  rw [MonoidalClosed.uncurry_curry, Iso.inv_hom_id, Category.comp_id]

/-- The entire native identity-loop representative is the original circle parameterization. -/
theorem identityCircleLoop_landing_evaluation (t : unitInterval) :
    PointedCGWH.loopLanding PointedCGWH.sphereOne (identityCircleLoop.right unitFreePoint) t =
      PointedCGWH.sphereOneParam (TopCat.I.homeomorph.{v}.symm t) := by
  let t' := TopCat.I.homeomorph.{v}.symm t
  have ht : TopCat.I.homeomorph t' = t := TopCat.I.homeomorph.apply_symm_apply t
  rw [← ht, PointedCGWH.loopLanding_evaluation]
  have h := congrArg (unitHomEquiv PointedCGWH.sphereOne) (identityCircleLoop_eval t')
  exact h.trans (unitHomEquiv_spherePoint t')

/-- Reflection retains the original interval lift and the actual reversed ordinary parameter. -/
def reflectedInterval (t : TopCat.I.{v}) : TopCat.I.{v} :=
  TopCat.I.homeomorph.{v}.symm (σ (TopCat.I.homeomorph t))

/-- The original uncurried reflected identity loop retains every full unit-point evaluation. -/
theorem circleReflection_unit_eval (t : TopCat.I.{v}) :
    spherePoint t ≫ circleReflection.{u, v} =
      identityCircleLoop ≫ loopReflection PointedCGWH.sphereOne ≫
        PointedCGWH.loopEvalAt PointedCGWH.sphereOne t := by
  have h := unitPoint_uncurry PointedCGWH.sphereOne PointedCGWH.sphereOne (spherePoint t)
    (identityCircleLoop ≫ loopReflection PointedCGWH.sphereOne)
  rw [pointEvaluation_eq_loopEvalAt] at h
  simpa only [circleReflection, Category.assoc] using h.symm

/-- The complete circle reflection carries each original interval point to its reversed point. -/
theorem circleReflection_spherePoint (t : TopCat.I.{v}) :
    spherePoint t ≫ circleReflection.{u, v} = spherePoint (reflectedInterval t) := by
  apply (unitHomEquiv PointedCGWH.sphereOne).injective
  rw [circleReflection_unit_eval, unitHomEquiv_spherePoint]
  let γ : (PointedCGWH.loop.obj PointedCGWH.sphereOne.{u, v}).right :=
    identityCircleLoop.right unitFreePoint
  change (PointedCGWH.loopEvalAt PointedCGWH.sphereOne t).right
    ((loopReflection PointedCGWH.sphereOne).right γ) = _
  have h₁ := PointedCGWH.loopLanding_evaluation PointedCGWH.sphereOne
    ((loopReflection PointedCGWH.sphereOne).right γ) t
  have h₂ := loopReflection_landing_evaluation PointedCGWH.sphereOne γ
    (TopCat.I.homeomorph t)
  have h₃ : PointedCGWH.loopLanding PointedCGWH.sphereOne γ (σ (TopCat.I.homeomorph t)) =
      PointedCGWH.sphereOneParam (reflectedInterval t) :=
    identityCircleLoop_landing_evaluation (σ (TopCat.I.homeomorph t))
  exact h₁.symm.trans (h₂.trans h₃)

/-- Internal-Hom precomposition evaluates at the complete image of the original circle point. -/
theorem loopPre_pointEvaluation (A : PointedCGWH.{u, v})
    (f : PointedCGWH.sphereOne ⟶ PointedCGWH.sphereOne) (t : TopCat.I.{v}) :
    (MonoidalClosed.pre f).app A ≫ PointedCGWH.loopEvalAt A t =
      CategoryTheory.MonoidalClosed.NativeEvaluationInterchange.pointEvaluation
        PointedCGWH.sphereOne A (spherePoint t ≫ f) := by
  rw [← pointEvaluation_eq_loopEvalAt]
  unfold CategoryTheory.MonoidalClosed.NativeEvaluationInterchange.pointEvaluation
  rw [MonoidalClosed.pre_map]
  simp only [NatTrans.comp_app, Category.assoc]

/-- The complete native loop reflection is the original contravariant circle-reflection map. -/
theorem loopReflection_eq_pre (A : PointedCGWH.{u, v}) :
    loopReflection A = (MonoidalClosed.pre circleReflection).app A := by
  apply Under.UnderMorphism.ext
  apply ConcreteCategory.hom_ext
  intro γ
  apply loopLanding_injective A
  apply Path.ext
  funext t
  let t' := TopCat.I.homeomorph.{v}.symm t
  have ht : TopCat.I.homeomorph t' = t := TopCat.I.homeomorph.apply_symm_apply t
  have he := loopPre_pointEvaluation A circleReflection t'
  rw [circleReflection_spherePoint, pointEvaluation_eq_loopEvalAt] at he
  have heγ := congrArg (fun f : PointedCGWH.loop.obj A ⟶ A => f.right γ) he
  have h₀ := PointedCGWH.loopLanding_evaluation A
    (((MonoidalClosed.pre circleReflection).app A).right γ) t'
  have h₁ := PointedCGWH.loopLanding_evaluation A γ (reflectedInterval t')
  have h₂ : PointedCGWH.loopLanding A γ (σ t) =
      (PointedCGWH.loopEvalAt A (reflectedInterval t')).right γ := by
    have hr : TopCat.I.homeomorph (reflectedInterval t') = σ t := by
      change TopCat.I.homeomorph.{v}
        (TopCat.I.homeomorph.{v}.symm (σ (TopCat.I.homeomorph.{v} t'))) = _
      rw [TopCat.I.homeomorph.{v}.apply_symm_apply, ht]
    exact (congrArg (fun s => PointedCGWH.loopLanding A γ s) hr.symm).trans h₁
  rw [loopReflection_landing_evaluation]
  exact h₂.trans (heγ.symm.trans
    ((congrArg (fun s => PointedCGWH.loopLanding A
      (((MonoidalClosed.pre circleReflection).app A).right γ) s) ht.symm).trans h₀).symm)

/-- The entire original two-loop evaluation is continuous in the loop and both parameters. -/
def doubleLoopEvaluation (A : PointedCGWH.{u, v}) :
    C((CGWH.cgwhToTop.obj (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) ×
        (unitInterval × unitInterval), CGWH.cgwhToTop.obj A.right) := by
  let o : C(CGWH.cgwhToTop.obj (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right,
      LoopSpace (CGWH.cgwhToTop.obj (PointedCGWH.loop.obj A).right)
        (underlyingBasepoint (PointedCGWH.loop.obj A))) :=
    (PointedCGWH.loopLanding (PointedCGWH.loop.obj A)).hom
  let i : C(CGWH.cgwhToTop.obj (PointedCGWH.loop.obj A).right,
      LoopSpace (CGWH.cgwhToTop.obj A.right) (underlyingBasepoint A)) :=
    (PointedCGWH.loopLanding A).hom
  let eo : C((CGWH.cgwhToTop.obj (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) ×
      unitInterval, CGWH.cgwhToTop.obj (PointedCGWH.loop.obj A).right) :=
    ⟨fun z => o z.1 z.2, Path.continuous_uncurry_iff.mpr o.continuous⟩
  let ei : C((CGWH.cgwhToTop.obj (PointedCGWH.loop.obj A).right) × unitInterval,
      CGWH.cgwhToTop.obj A.right) :=
    ⟨fun z => i z.1 z.2, Path.continuous_uncurry_iff.mpr i.continuous⟩
  exact ei.comp
    ⟨fun z => (eo (z.1, z.2.1), z.2.2),
      (eo.continuous.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
        continuous_snd.snd⟩

/-- Every original evaluation value retains both full native loop landings. -/
theorem doubleLoopEvaluation_apply (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) (s t : unitInterval) :
    doubleLoopEvaluation A (γ, (s, t)) =
      PointedCGWH.loopLanding A (PointedCGWH.loopLanding (PointedCGWH.loop.obj A) γ s) t := rfl

/-- The whole original double-loop evaluation is based on every side of the actual square. -/
theorem doubleLoopEvaluation_boundary (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) (s t : unitInterval)
    (h : s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) :
    doubleLoopEvaluation A (γ, (s, t)) = underlyingBasepoint A := by
  rw [doubleLoopEvaluation_apply]
  rcases h with h | h | h | h
  · subst s
    have ho : PointedCGWH.loopLanding (PointedCGWH.loop.obj A) γ 0 =
        underlyingBasepoint (PointedCGWH.loop.obj A) :=
      (PointedCGWH.loopLanding (PointedCGWH.loop.obj A) γ).source
    rw [ho]
    exact congrArg (fun p => p t) (PointedCGWH.loopLanding_basepoint A)
  · subst s
    have ho : PointedCGWH.loopLanding (PointedCGWH.loop.obj A) γ 1 =
        underlyingBasepoint (PointedCGWH.loop.obj A) :=
      (PointedCGWH.loopLanding (PointedCGWH.loop.obj A) γ).target
    rw [ho]
    exact congrArg (fun p => p t) (PointedCGWH.loopLanding_basepoint A)
  · subst t
    exact (PointedCGWH.loopLanding A
      (PointedCGWH.loopLanding (PointedCGWH.loop.obj A) γ s)).source
  · subst t
    exact (PointedCGWH.loopLanding A
      (PointedCGWH.loopLanding (PointedCGWH.loop.obj A) γ s)).target

private theorem squareBoundary_swap (p : unitInterval × unitInterval)
    (h : p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1) :
    p.2 = 0 ∨ p.2 = 1 ∨ p.1 = 0 ∨ p.1 = 1 := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- Turn the full square in its actual inner coordinate, retaining the original native loop. -/
def turnedInnerLoops (A : PointedCGWH.{u, v}) :
    C(unitInterval × (unitInterval ×
        (CGWH.cgwhToTop.obj (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right)),
      LoopSpace (CGWH.cgwhToTop.obj A.right) (underlyingBasepoint A)) where
  toFun z :=
    { toFun t :=
        let p := HomotopyGroup.CoordinateInterchange.squareTurn (z.1, (t, z.2.1))
        doubleLoopEvaluation A (z.2.2, (p.2, p.1))
      continuous_toFun := by
        have hp : Continuous (fun t : unitInterval =>
            HomotopyGroup.CoordinateInterchange.squareTurn (z.1, (t, z.2.1))) :=
          HomotopyGroup.CoordinateInterchange.continuous_squareTurn.comp (by fun_prop)
        exact (doubleLoopEvaluation A).continuous.comp
          (continuous_const.prodMk (hp.snd.prodMk hp.fst))
      source' := by
        exact doubleLoopEvaluation_boundary A z.2.2 _ _ (squareBoundary_swap _
          (HomotopyGroup.CoordinateInterchange.squareTurn_boundary (z.1, (0, z.2.1))
            (Or.inl rfl)))
      target' := by
        exact doubleLoopEvaluation_boundary A z.2.2 _ _ (squareBoundary_swap _
          (HomotopyGroup.CoordinateInterchange.squareTurn_boundary (z.1, (1, z.2.1))
            (Or.inr (Or.inl rfl)))) }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    have hp : Continuous (fun z :
        (unitInterval × (unitInterval ×
          (CGWH.cgwhToTop.obj (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right))) ×
            unitInterval =>
        HomotopyGroup.CoordinateInterchange.squareTurn (z.1.1, (z.2, z.1.2.1))) :=
      HomotopyGroup.CoordinateInterchange.continuous_squareTurn.comp (by fun_prop)
    exact (doubleLoopEvaluation A).continuous.comp
      (continuous_fst.snd.snd.prodMk (hp.snd.prodMk hp.fst))

/-- The entire turned based-loop family retains its original square turn and both evaluations. -/
theorem turnedInnerLoops_apply (A : PointedCGWH.{u, v}) (τ s t : unitInterval)
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) :
    turnedInnerLoops A (τ, (s, γ)) t =
      let p := HomotopyGroup.CoordinateInterchange.squareTurn (τ, (t, s))
      doubleLoopEvaluation A (γ, (p.2, p.1)) := rfl

/-- At time zero the entire turned family reflects only the actual inner loop coordinate. -/
theorem turnedInnerLoops_zero (A : PointedCGWH.{u, v}) (s t : unitInterval)
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) :
    turnedInnerLoops A (0, (s, γ)) t = doubleLoopEvaluation A (γ, (s, σ t)) := by
  rw [turnedInnerLoops_apply, HomotopyGroup.CoordinateInterchange.squareTurn_zero]

/-- At time one the entire original turned family is the complete native coordinate exchange. -/
theorem turnedInnerLoops_one (A : PointedCGWH.{u, v}) (s t : unitInterval)
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) :
    turnedInnerLoops A (1, (s, γ)) t = doubleLoopEvaluation A (γ, (t, s)) := by
  rw [turnedInnerLoops_apply, HomotopyGroup.CoordinateInterchange.squareTurn_one]

/-- The original native interval has its complete ordinary interval homeomorphism. -/
def nativeIntervalHomeo : CGWH.cgwhToTop.obj CGWH.interval.{u, v} ≃ₜ unitInterval :=
  (TopCat.homeoOfIso CGWH.intervalToTopIso.{u, v}).trans TopCat.I.homeomorph.{v}

/-- Local compactness of the actual native interval is transported from its proved homeomorphism. -/
theorem nativeIntervalLocallyCompact : LocallyCompactSpace CGWH.interval.{u, v} := by
  let h := (TopCat.homeoOfIso CGWH.intervalToTopIso.{u, v}).trans TopCat.I.homeomorph.{v}
  exact h.isClosedEmbedding.locallyCompactSpace

/-- The actual native interval is Hausdorff through that same proved homeomorphism. -/
theorem nativeIntervalT2 : T2Space CGWH.interval.{u, v} := by
  let h := (TopCat.homeoOfIso CGWH.intervalToTopIso.{u, v}).trans TopCat.I.homeomorph.{v}
  exact h.isEmbedding.t2Space

/-- The actual Cartesian interval tensor retains both original ordinary coordinates. -/
def intervalPairHomeo (D : CGWH.{u, v}) (h : CGWH.cgwhToTop.obj D ≃ₜ unitInterval) :
    CGWH.cgwhToTop.obj (D ⊗ D) ≃ₜ unitInterval × unitInterval := by
  let _ : LocallyCompactSpace D := h.isClosedEmbedding.locallyCompactSpace
  let _ : T2Space D := h.isEmbedding.t2Space
  exact (TopCat.homeoOfIso (CGWH.tensorToTopIsoOfLocallyCompactRight D D)).trans
    (h.prodCongr h)

/-- The complete raw turned family on the actual native interval tensor. -/
def nativeTurnInnerRaw (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) :
    CGWH.cgwhToTop.obj (CGWH.interval.{u, v} ⊗ CGWH.interval.{u, v}) ⟶ TopCat.of
      (LoopSpace (CGWH.cgwhToTop.obj A.right) (underlyingBasepoint A)) := by
  let D := CGWH.interval.{u, v}
  let h := (TopCat.homeoOfIso CGWH.intervalToTopIso.{u, v}).trans TopCat.I.homeomorph.{v}
  let h₂ := intervalPairHomeo D h
  exact TopCat.ofHom ((turnedInnerLoops A).comp
    ⟨fun p => ((h₂ p).1, ((h₂ p).2, γ)),
      h₂.continuous.fst.prodMk (h₂.continuous.snd.prodMk continuous_const)⟩)

/-- The full raw value keeps both original native interval-tensor coordinates. -/
theorem nativeTurnInnerRaw_apply (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right)
    (p : CGWH.cgwhToTop.obj (CGWH.interval.{u, v} ⊗ CGWH.interval.{u, v})) :
    nativeTurnInnerRaw A γ p =
      let D := CGWH.interval.{u, v}
      let h := (TopCat.homeoOfIso CGWH.intervalToTopIso.{u, v}).trans TopCat.I.homeomorph.{v}
      let q := intervalPairHomeo D h p
      turnedInnerLoops A (q.1, (q.2, γ)) := rfl

/-- Lift the complete turned inner-loop family from the actual native interval tensor. -/
def nativeTurnInnerFamily (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) :
    CGWH.interval.{u, v} ⊗ CGWH.interval.{u, v} ⟶ (PointedCGWH.loop.obj A).right :=
  liftLoopFamily (CGWH.interval.{u, v} ⊗ CGWH.interval.{u, v}) A (nativeTurnInnerRaw A γ)

/-- The entire native family lands in the complete original raw native-tensor map. -/
@[reassoc]
theorem nativeTurnInnerFamily_landing_map (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) :
    CGWH.cgwhToTop.map (nativeTurnInnerFamily A γ) ≫ PointedCGWH.loopLanding A =
      nativeTurnInnerRaw A γ :=
  liftLoopFamily_landing (CGWH.interval.{u, v} ⊗ CGWH.interval.{u, v}) A (nativeTurnInnerRaw A γ)

/-- Every whole native family value is the same original raw turned-loop value. -/
theorem nativeTurnInnerFamily_landing (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right)
    (p : CGWH.cgwhToTop.obj (CGWH.interval.{u, v} ⊗ CGWH.interval.{u, v})) :
    PointedCGWH.loopLanding A (nativeTurnInnerFamily A γ p) = nativeTurnInnerRaw A γ p :=
  ConcreteCategory.congr_hom (nativeTurnInnerFamily_landing_map A γ) p

/-- The whole turned family has the original constant-loop value on the first outer endpoint. -/
theorem turnedInnerLoops_outer_zero (A : PointedCGWH.{u, v}) (τ : unitInterval)
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) :
    turnedInnerLoops A (τ, (0, γ)) = Path.refl (underlyingBasepoint A) := by
  apply Path.ext
  funext t
  rw [turnedInnerLoops_apply]
  exact doubleLoopEvaluation_boundary A γ _ _ (squareBoundary_swap _
    (HomotopyGroup.CoordinateInterchange.squareTurn_boundary (τ, (t, 0))
      (Or.inr (Or.inr (Or.inl rfl)))))

/-- The whole turned family has the original constant-loop value on the second outer endpoint. -/
theorem turnedInnerLoops_outer_one (A : PointedCGWH.{u, v}) (τ : unitInterval)
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) :
    turnedInnerLoops A (τ, (1, γ)) = Path.refl (underlyingBasepoint A) := by
  apply Path.ext
  funext t
  rw [turnedInnerLoops_apply]
  exact doubleLoopEvaluation_boundary A γ _ _ (squareBoundary_swap _
    (HomotopyGroup.CoordinateInterchange.squareTurn_boundary (τ, (t, 1))
      (Or.inr (Or.inr (Or.inr rfl)))))

/-- A complete turned family on any actual Cartesian square coordinate presentation. -/
def turnInnerRaw (S : CGWH.{u, v}) (e : CGWH.cgwhToTop.obj S ≃ₜ unitInterval × unitInterval)
    (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) :
    CGWH.cgwhToTop.obj S ⟶ TopCat.of
      (LoopSpace (CGWH.cgwhToTop.obj A.right) (underlyingBasepoint A)) :=
  TopCat.ofHom ((turnedInnerLoops A).comp
    ⟨fun p => ((e p).1, ((e p).2, γ)),
      e.continuous.fst.prodMk (e.continuous.snd.prodMk continuous_const)⟩)

/-- Every full raw-square value retains both supplied coordinate functions. -/
theorem turnInnerRaw_apply (S : CGWH.{u, v})
    (e : CGWH.cgwhToTop.obj S ≃ₜ unitInterval × unitInterval) (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) (p : CGWH.cgwhToTop.obj S) :
    turnInnerRaw S e A γ p = turnedInnerLoops A ((e p).1, ((e p).2, γ)) := rfl

/-- Lift the full square-coordinate family through the original native loop coreflection. -/
def turnInnerFamily (S : CGWH.{u, v})
    (e : CGWH.cgwhToTop.obj S ≃ₜ unitInterval × unitInterval) (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) :
    S ⟶ (PointedCGWH.loop.obj A).right := liftLoopFamily S A (turnInnerRaw S e A γ)

/-- The entire lifted square-coordinate family has the original raw landing map. -/
@[reassoc]
theorem turnInnerFamily_landing_map (S : CGWH.{u, v})
    (e : CGWH.cgwhToTop.obj S ≃ₜ unitInterval × unitInterval) (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) :
    CGWH.cgwhToTop.map (turnInnerFamily S e A γ) ≫ PointedCGWH.loopLanding A =
      turnInnerRaw S e A γ := liftLoopFamily_landing S A (turnInnerRaw S e A γ)

/-- Every full native lifted value is the original turned value at the actual square coordinates. -/
theorem turnInnerFamily_landing (S : CGWH.{u, v})
    (e : CGWH.cgwhToTop.obj S ≃ₜ unitInterval × unitInterval) (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) (p : CGWH.cgwhToTop.obj S) :
    PointedCGWH.loopLanding A (turnInnerFamily S e A γ p) =
      turnedInnerLoops A ((e p).1, ((e p).2, γ)) :=
  (ConcreteCategory.congr_hom (turnInnerFamily_landing_map S e A γ) p).trans
    (turnInnerRaw_apply S e A γ p)

/-- Both original outer endpoint coordinates lift to the actual selected native-loop point. -/
theorem turnInnerFamily_endpoint (S : CGWH.{u, v})
    (e : CGWH.cgwhToTop.obj S ≃ₜ unitInterval × unitInterval) (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right)
    (τ s : unitInterval) (hs : s = 0 ∨ s = 1) :
    turnInnerFamily S e A γ (e.symm (τ, s)) =
      underlyingBasepoint (PointedCGWH.loop.obj A) := by
  have hr := turnInnerRaw_apply S e A γ (e.symm (τ, s))
  rw [e.apply_symm_apply] at hr
  have hb : turnedInnerLoops A (τ, (s, γ)) = Path.refl (underlyingBasepoint A) := by
    rcases hs with rfl | rfl
    · exact turnedInnerLoops_outer_zero A τ γ
    · exact turnedInnerLoops_outer_one A τ γ
  exact liftLoopFamily_eq_basepoint S A (turnInnerRaw S e A γ) (e.symm (τ, s)) (hr.trans hb)

/-- The whole native outer evaluation retains the actual square and time coordinate maps. -/
def turnOuterEvaluation (S D : CGWH.{u, v})
    (e : CGWH.cgwhToTop.obj S ≃ₜ unitInterval × unitInterval)
    (h : CGWH.cgwhToTop.obj D ≃ₜ unitInterval) (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) :
    C((CGWH.cgwhToTop.obj D) × unitInterval, CGWH.cgwhToTop.obj (PointedCGWH.loop.obj A).right) :=
  evaluationInSquareCoordinates
    (ConcreteCategory.hom (C := CGWH.{u, v}) (turnInnerFamily S e A γ)) e h

/-- Every complete evaluation value keeps the same inverse-square-coordinate point. -/
theorem turnOuterEvaluation_apply (S D : CGWH.{u, v})
    (e : CGWH.cgwhToTop.obj S ≃ₜ unitInterval × unitInterval)
    (h : CGWH.cgwhToTop.obj D ≃ₜ unitInterval) (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right)
    (x : CGWH.cgwhToTop.obj D) (s : unitInterval) :
    turnOuterEvaluation S D e h A γ (x, s) =
      (ConcreteCategory.hom (C := CGWH.{u, v}) (turnInnerFamily S e A γ))
        (e.symm (h x, s)) :=
  evaluationInSquareCoordinates_apply
    (ConcreteCategory.hom (C := CGWH.{u, v}) (turnInnerFamily S e A γ)) e h x s

/-- The full native outer evaluation has its first original based endpoint. -/
theorem turnOuterEvaluation_zero (S D : CGWH.{u, v})
    (e : CGWH.cgwhToTop.obj S ≃ₜ unitInterval × unitInterval)
    (h : CGWH.cgwhToTop.obj D ≃ₜ unitInterval) (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) (x : CGWH.cgwhToTop.obj D) :
    turnOuterEvaluation S D e h A γ (x, 0) = underlyingBasepoint (PointedCGWH.loop.obj A) :=
  (turnOuterEvaluation_apply S D e h A γ x 0).trans
    (turnInnerFamily_endpoint S e A γ (h x) 0 (Or.inl rfl))

/-- The full native outer evaluation has its second original based endpoint. -/
theorem turnOuterEvaluation_one (S D : CGWH.{u, v})
    (e : CGWH.cgwhToTop.obj S ≃ₜ unitInterval × unitInterval)
    (h : CGWH.cgwhToTop.obj D ≃ₜ unitInterval) (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) (x : CGWH.cgwhToTop.obj D) :
    turnOuterEvaluation S D e h A γ (x, 1) = underlyingBasepoint (PointedCGWH.loop.obj A) :=
  (turnOuterEvaluation_apply S D e h A γ x 1).trans
    (turnInnerFamily_endpoint S e A γ (h x) 1 (Or.inr rfl))

/-- The complete outer-loop family is built from the original based evaluation. -/
def turnOuterRawLoops (S D : CGWH.{u, v})
    (e : CGWH.cgwhToTop.obj S ≃ₜ unitInterval × unitInterval)
    (h : CGWH.cgwhToTop.obj D ≃ₜ unitInterval) (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) :
    C(CGWH.cgwhToTop.obj D, LoopSpace (CGWH.cgwhToTop.obj (PointedCGWH.loop.obj A).right)
      (underlyingBasepoint (PointedCGWH.loop.obj A))) :=
  rawLoopsOfBasedFamily (turnOuterEvaluation S D e h A γ)
    (underlyingBasepoint (PointedCGWH.loop.obj A))
    (turnOuterEvaluation_zero S D e h A γ) (turnOuterEvaluation_one S D e h A γ)

/-- The actual double-loop time family uses both original compact-open coreflections. -/
def turnDoubleFamily (S D : CGWH.{u, v})
    (e : CGWH.cgwhToTop.obj S ≃ₜ unitInterval × unitInterval)
    (h : CGWH.cgwhToTop.obj D ≃ₜ unitInterval) (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right) :
    D ⟶ (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right :=
  liftLoopFamily D (PointedCGWH.loop.obj A) (TopCat.ofHom (turnOuterRawLoops S D e h A γ))

/-- Both full original native loop evaluations preserve the entire actual square-turn family. -/
theorem turnDoubleFamily_landing (S D : CGWH.{u, v})
    (e : CGWH.cgwhToTop.obj S ≃ₜ unitInterval × unitInterval)
    (h : CGWH.cgwhToTop.obj D ≃ₜ unitInterval) (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right)
    (x : CGWH.cgwhToTop.obj D) (s t : unitInterval) :
    PointedCGWH.loopLanding A
        (PointedCGWH.loopLanding (PointedCGWH.loop.obj A) (turnDoubleFamily S D e h A γ x) s) t =
      turnedInnerLoops A (h x, (s, γ)) t := by
  have ho := liftLoopFamily_apply D (PointedCGWH.loop.obj A)
    (TopCat.ofHom (turnOuterRawLoops S D e h A γ)) x s
  have he := turnOuterEvaluation_apply S D e h A γ x s
  have hi := turnInnerFamily_landing S e A γ (e.symm (h x, s))
  rw [e.apply_symm_apply] at hi
  have h₁ := congrArg (fun y => PointedCGWH.loopLanding A y t) (ho.trans he)
  have h₂ := congrArg (fun p => p t) hi
  exact h₁.trans h₂

/-- The entire original native double-loop point is determined by both complete evaluations. -/
theorem doubleLoop_ext (A : PointedCGWH.{u, v})
    (γ δ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right)
    (h : ∀ s t : unitInterval, PointedCGWH.loopLanding A
        (PointedCGWH.loopLanding (PointedCGWH.loop.obj A) γ s) t =
      PointedCGWH.loopLanding A (PointedCGWH.loopLanding (PointedCGWH.loop.obj A) δ s) t) :
    γ = δ := by
  apply loopLanding_injective (PointedCGWH.loop.obj A)
  apply Path.ext
  funext s
  apply loopLanding_injective A
  apply Path.ext
  funext t
  exact h s t

/-- The full time-zero native family is the actual reflection of the inner native loop. -/
theorem turnDoubleFamily_zero (S D : CGWH.{u, v})
    (e : CGWH.cgwhToTop.obj S ≃ₜ unitInterval × unitInterval)
    (h : CGWH.cgwhToTop.obj D ≃ₜ unitInterval) (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right)
    (x : CGWH.cgwhToTop.obj D) (hx : h x = 0) :
    turnDoubleFamily S D e h A γ x =
      (PointedCGWH.loop.map (loopReflection A)).right γ := by
  apply doubleLoop_ext A
  intro s t
  have hf := turnDoubleFamily_landing S D e h A γ x s t
  rw [hx, turnedInnerLoops_zero] at hf
  have hg := loopLanding_map_evaluation (loopReflection A) γ s
  have h₁ := congrArg (fun y => PointedCGWH.loopLanding A y t) hg
  have h₂ := loopReflection_landing_evaluation A
    (PointedCGWH.loopLanding (PointedCGWH.loop.obj A) γ s) t
  have hd := doubleLoopEvaluation_apply A γ s (σ t)
  exact hf.trans (hd.trans (h₁.trans h₂).symm)

/-- The full time-one native family is the actual complete closed-category interchange. -/
theorem turnDoubleFamily_one (S D : CGWH.{u, v})
    (e : CGWH.cgwhToTop.obj S ≃ₜ unitInterval × unitInterval)
    (h : CGWH.cgwhToTop.obj D ≃ₜ unitInterval) (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right)
    (x : CGWH.cgwhToTop.obj D) (hx : h x = 1) :
    turnDoubleFamily S D e h A γ x = (interchange A).right γ := by
  apply doubleLoop_ext A
  intro s t
  have hf := turnDoubleFamily_landing S D e h A γ x s t
  rw [hx, turnedInnerLoops_one] at hf
  have hi := interchange_landing_evaluation A γ s t
  have hd := doubleLoopEvaluation_apply A γ t s
  exact hf.trans (hd.trans hi.symm)

/-- The entire continuous double-loop family becomes a pointed map by the actual free adjunction. -/
def pointedTurnFamily (S D : CGWH.{u, v})
    (e : CGWH.cgwhToTop.obj S ≃ₜ unitInterval × unitInterval)
    (h : CGWH.cgwhToTop.obj D ≃ₜ unitInterval) (A : PointedCGWH.{u, v})
    (g : (𝟙_ PointedCGWH) ⟶ PointedCGWH.loop.obj (PointedCGWH.loop.obj A)) :
    (Under.costar CGWH.point).obj D ⟶ PointedCGWH.loop.obj (PointedCGWH.loop.obj A) :=
  ((Under.costarAdjForget CGWH.point).homEquiv D
    (PointedCGWH.loop.obj (PointedCGWH.loop.obj A))).symm
    (turnDoubleFamily S D e h A (unitHomEquiv _ g))

/-- The full pointed family forgets to the same original continuous double-loop family. -/
theorem pointedTurnFamily_forget (S D : CGWH.{u, v})
    (e : CGWH.cgwhToTop.obj S ≃ₜ unitInterval × unitInterval)
    (h : CGWH.cgwhToTop.obj D ≃ₜ unitInterval) (A : PointedCGWH.{u, v})
    (g : (𝟙_ PointedCGWH) ⟶ PointedCGWH.loop.obj (PointedCGWH.loop.obj A)) :
    (Under.costarAdjForget CGWH.point).homEquiv D
      (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)) (pointedTurnFamily S D e h A g) =
      turnDoubleFamily S D e h A (unitHomEquiv _ g) :=
  ((Under.costarAdjForget CGWH.point).homEquiv D
    (PointedCGWH.loop.obj (PointedCGWH.loop.obj A))).apply_symm_apply _

/-- A genuine zero time endpoint gives the full original pointed reflected-loop composite. -/
theorem pointedTurnFamily_zero (S D : CGWH.{u, v})
    (e : CGWH.cgwhToTop.obj S ≃ₜ unitInterval × unitInterval)
    (h : CGWH.cgwhToTop.obj D ≃ₜ unitInterval) (A : PointedCGWH.{u, v})
    (g : (𝟙_ PointedCGWH) ⟶ PointedCGWH.loop.obj (PointedCGWH.loop.obj A))
    (i : CGWH.point ⟶ D) (hi : h (i PUnit.unit) = 0) :
    (Under.costar CGWH.point).map i ≫ pointedTurnFamily S D e h A g =
      g ≫ PointedCGWH.loop.map (loopReflection A) := by
  apply ((Under.costarAdjForget CGWH.point).homEquiv CGWH.point _).injective
  rw [Adjunction.homEquiv_naturality_left, pointedTurnFamily_forget,
    Adjunction.homEquiv_naturality_right]
  apply (CGWH.pointHomEquiv _).injective
  rw [pointHomEquiv_comp, pointHomEquiv_comp]
  have hp := CGWH.pointHomEquiv_apply D i
  have ht := turnDoubleFamily_zero S D e h A (unitHomEquiv _ g) (i PUnit.unit) hi
  have hg := unitHomEquiv_eq_pointHomEquiv (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)) g
  have hfinal := (congrArg (fun x => turnDoubleFamily S D e h A (unitHomEquiv _ g) x) hp).trans
    (ht.trans (congrArg (PointedCGWH.loop.map (loopReflection A)).right hg))
  simpa only [Under.forget_obj, Under.forget_map] using hfinal

/-- A genuine one time endpoint gives the full original pointed interchange composite. -/
theorem pointedTurnFamily_one (S D : CGWH.{u, v})
    (e : CGWH.cgwhToTop.obj S ≃ₜ unitInterval × unitInterval)
    (h : CGWH.cgwhToTop.obj D ≃ₜ unitInterval) (A : PointedCGWH.{u, v})
    (g : (𝟙_ PointedCGWH) ⟶ PointedCGWH.loop.obj (PointedCGWH.loop.obj A))
    (i : CGWH.point ⟶ D) (hi : h (i PUnit.unit) = 1) :
    (Under.costar CGWH.point).map i ≫ pointedTurnFamily S D e h A g =
      g ≫ interchange A := by
  apply ((Under.costarAdjForget CGWH.point).homEquiv CGWH.point _).injective
  rw [Adjunction.homEquiv_naturality_left, pointedTurnFamily_forget,
    Adjunction.homEquiv_naturality_right]
  apply (CGWH.pointHomEquiv _).injective
  rw [pointHomEquiv_comp, pointHomEquiv_comp]
  have hp := CGWH.pointHomEquiv_apply D i
  have ht := turnDoubleFamily_one S D e h A (unitHomEquiv _ g) (i PUnit.unit) hi
  have hg := unitHomEquiv_eq_pointHomEquiv (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)) g
  have hfinal := (congrArg (fun x => turnDoubleFamily S D e h A (unitHomEquiv _ g) x) hp).trans
    (ht.trans (congrArg (interchange A).right hg))
  simpa only [Under.forget_obj, Under.forget_map] using hfinal

/-- The original twice-curried identity on two circle factors retains its right-unit map. -/
def doubleIdentityLoop (K : PointedCGWH.{u, v}) :
    (𝟙_ PointedCGWH) ⟶ (ihom K).obj ((ihom K).obj (K ⊗ K)) :=
  MonoidalClosed.curry (MonoidalClosed.curry (K ◁ (ρ_ K).hom))

/-- Both original uncurry operations recover the entire selected identity coefficient map. -/
theorem doubleIdentityLoop_uncurry (K : PointedCGWH.{u, v}) :
    MonoidalClosed.uncurry (MonoidalClosed.uncurry (doubleIdentityLoop K)) =
      K ◁ (ρ_ K).hom := by
  simp only [doubleIdentityLoop, MonoidalClosed.uncurry_curry]

/-- The actual double transpose moves time past the entire two-circle coefficient. -/
def doubleTransposeAction (D A : PointedCGWH.{u, v})
    (g : D ⟶ PointedCGWH.loop.obj (PointedCGWH.loop.obj A)) :
    D ⊗ (PointedCGWH.sphereOne ⊗ PointedCGWH.sphereOne) ⟶ A :=
  (β_ D (PointedCGWH.sphereOne ⊗ PointedCGWH.sphereOne)).hom ≫
    (α_ PointedCGWH.sphereOne PointedCGWH.sphereOne D).hom ≫
      MonoidalClosed.uncurry (MonoidalClosed.uncurry g)

/-- Every full pointed time insertion retains both original uncurry operations and unitors. -/
theorem doubleTransposeAction_endpoint (D A : PointedCGWH.{u, v})
    (g : D ⟶ PointedCGWH.loop.obj (PointedCGWH.loop.obj A))
    (i : (𝟙_ PointedCGWH) ⟶ D) :
    (λ_ (PointedCGWH.sphereOne ⊗ PointedCGWH.sphereOne)).inv ≫
      i ▷ (PointedCGWH.sphereOne ⊗ PointedCGWH.sphereOne) ≫ doubleTransposeAction D A g =
        (ρ_ (PointedCGWH.sphereOne ⊗ PointedCGWH.sphereOne)).inv ≫
          (α_ PointedCGWH.sphereOne PointedCGWH.sphereOne (𝟙_ PointedCGWH)).hom ≫
            MonoidalClosed.uncurry (MonoidalClosed.uncurry (i ≫ g)) := by
  rw [doubleTransposeAction, BraidedCategory.braiding_naturality_left_assoc,
    braiding_tensorUnit_left]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [associator_naturality_right_assoc, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_natural_left]

/-- Reflecting the inner native loop reflects the first original tensor coefficient. -/
theorem doubleUncurry_loopReflection {D A : PointedCGWH.{u, v}}
    (g : D ⟶ PointedCGWH.loop.obj (PointedCGWH.loop.obj A)) :
    MonoidalClosed.uncurry (MonoidalClosed.uncurry
        (g ≫ PointedCGWH.loop.map (loopReflection A))) =
      circleReflection ▷ (PointedCGWH.sphereOne ⊗ D) ≫
        MonoidalClosed.uncurry (MonoidalClosed.uncurry g) := by
  change MonoidalClosed.uncurry (MonoidalClosed.uncurry
      (g ≫ (ihom PointedCGWH.sphereOne).map (loopReflection A))) = _
  rw [MonoidalClosed.uncurry_natural_right, loopReflection_eq_pre,
    MonoidalClosed.uncurry_pre_app]

/-- The full original reflected identity coefficient is reflection of the first circle. -/
theorem doubleIdentityLoop_reflection :
    (ρ_ (PointedCGWH.sphereOne.{u, v} ⊗ PointedCGWH.sphereOne)).inv ≫
      (α_ PointedCGWH.sphereOne PointedCGWH.sphereOne (𝟙_ PointedCGWH)).hom ≫
        MonoidalClosed.uncurry (MonoidalClosed.uncurry
          (doubleIdentityLoop PointedCGWH.sphereOne ≫
            PointedCGWH.loop.map (loopReflection
              (PointedCGWH.sphereOne ⊗ PointedCGWH.sphereOne)))) =
      circleReflection ▷ PointedCGWH.sphereOne := by
  rw [doubleUncurry_loopReflection, doubleIdentityLoop_uncurry]
  rw [← whisker_exchange]
  have hu : (ρ_ (PointedCGWH.sphereOne.{u, v} ⊗ PointedCGWH.sphereOne)).inv ≫
      (α_ PointedCGWH.sphereOne PointedCGWH.sphereOne (𝟙_ PointedCGWH)).hom ≫
        PointedCGWH.sphereOne ◁ (ρ_ PointedCGWH.sphereOne).hom = 𝟙 _ := by
    monoidal
  simpa only [Category.assoc, Category.id_comp] using
    congrArg (fun f => f ≫ circleReflection ▷ PointedCGWH.sphereOne) hu

open CategoryTheory.MonoidalClosed.OriginalDoubleLoopCoordinateGeometry in
/-- The full original interchanged identity coefficient is the actual inverse braiding. -/
theorem doubleIdentityLoop_interchange :
    (ρ_ (PointedCGWH.sphereOne.{u, v} ⊗ PointedCGWH.sphereOne)).inv ≫
      (α_ PointedCGWH.sphereOne PointedCGWH.sphereOne (𝟙_ PointedCGWH)).hom ≫
        MonoidalClosed.uncurry (MonoidalClosed.uncurry
          (doubleIdentityLoop PointedCGWH.sphereOne ≫
            interchange (PointedCGWH.sphereOne ⊗ PointedCGWH.sphereOne))) =
      (β_ PointedCGWH.sphereOne PointedCGWH.sphereOne).inv := by
  rw [originalWholeSquareSwap_hom_uncurry, doubleIdentityLoop_uncurry]
  simp only [Iso.hom_inv_id_assoc]
  rw [← rightUnitor_inv_naturality_assoc]
  have hu : (ρ_ (PointedCGWH.sphereOne.{u, v} ⊗ PointedCGWH.sphereOne)).inv ≫
      (α_ PointedCGWH.sphereOne PointedCGWH.sphereOne (𝟙_ PointedCGWH)).hom ≫
        PointedCGWH.sphereOne ◁ (ρ_ PointedCGWH.sphereOne).hom = 𝟙 _ := by
    monoidal
  simpa only [Category.assoc, Category.comp_id] using
    congrArg (fun f => (β_ PointedCGWH.sphereOne PointedCGWH.sphereOne).inv ≫ f) hu

end PointedCGWH.SuspensionCoefficientGeometry
