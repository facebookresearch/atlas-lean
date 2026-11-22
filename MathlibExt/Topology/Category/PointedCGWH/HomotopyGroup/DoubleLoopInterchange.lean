/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Homotopy.HomotopyGroupCoordinateInterchange
import MathlibExt.Topology.Homotopy.HomotopyGroupLoopShift
import MathlibExt.Topology.Homotopy.BasedHomotopyGroupEquivalence
import MathlibExt.Topology.Category.PointedCGWH.LoopHomotopyComparison
import MathlibExt.Topology.Category.PointedCGWH.Colimits.ClosedSequential
import MathlibExt.CategoryTheory.Monoidal.Closed.InternalHomInterchange
import MathlibExt.CategoryTheory.Monoidal.Closed.UnitEvaluation

/-!
# Original native loop comparisons and the actual coordinate interchange

The native loop landing is the original compact-open comparison and genuine
compact-generation counit. Its proved weakness supplies the actual cube-group
comparison, with the literal landing as its forward map. The topological loop
shift then gives the entire comparison with the next original homotopy group.

In particular, even the fundamental group of a native double loop has its
original commutative multiplication. No Omega-spectrum or basepoint condition
is an input to these constructions.
-/

set_option autoImplicit false
noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory Topology
open scoped unitInterval Topology MonoidalClosed CGWH.limits

namespace CategoryTheory.MonoidalClosed.NativeEvaluationInterchange

universe uC vC
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C]

open BraidedCategory
open CategoryTheory.MonoidalClosed.OriginalLoopInterchangeGeometry

/-- Evaluation at the full unit-point map uses original internal-Hom precomposition. -/
def pointEvaluation (K X : C) (s : (𝟙_ C) ⟶ K) : (ihom K).obj X ⟶ X :=
  (MonoidalClosed.pre s).app X ≫ (MonoidalClosed.unitIsoSelf (X := X)).hom

omit [SymmetricCategory C] in
/-- The complete point evaluation is natural in every original target map. -/
theorem pointEvaluation_naturality (K : C) (s : (𝟙_ C) ⟶ K)
    {X Y : C} (f : X ⟶ Y) :
    (ihom K).map f ≫ pointEvaluation K Y s = pointEvaluation K X s ≫ f :=
  (MonoidalClosed.pre s ≫ MonoidalClosed.unitNatIso.inv).naturality f

omit [SymmetricCategory C] in
/-- Evaluation of the entire internal-Hom map keeps its original uncurrying and unit insertion. -/
theorem pointEvaluation_comp (K X : C) (s : (𝟙_ C) ⟶ K)
    {A : C} (f : A ⟶ (ihom K).obj X) :
    f ≫ pointEvaluation K X s = (λ_ A).inv ≫ s ▷ A ≫ MonoidalClosed.uncurry f := by
  unfold pointEvaluation
  rw [← Category.assoc, NativeOmegaRecovery.UnitCotensorEvaluation.map,
    MonoidalClosed.uncurry_pre_app]

omit [MonoidalClosed C] in
/-- The actual inserted unit point crosses the full original coefficient coordinate. -/
@[reassoc]
theorem pointInsertion_interchange (K A : C) (s : (𝟙_ C) ⟶ K) :
    K ◁ ((λ_ A).inv ≫ s ▷ A) ≫ (α_ K K A).inv ≫
        (β_ K K).inv ▷ A ≫ (α_ K K A).hom =
      (λ_ (K ⊗ A)).inv ≫ s ▷ (K ⊗ A) := by
  rw [whiskerLeft_comp]
  simp only [Category.assoc]
  rw [associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, braiding_inv_naturality_right,
    comp_whiskerRight, Category.assoc, associator_naturality_left]
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding (𝟙_ C) K,
    braiding_tensorUnit_right, comp_whiskerRight]
  monoidal

/-- The whole original double-loop swap exchanges evaluation at an arbitrary complete unit point. -/
theorem interchange_outer_evaluation (K X : C) (s : (𝟙_ C) ⟶ K) :
    (originalSelfInterchangeNatIso K).hom.app X ≫ pointEvaluation K ((ihom K).obj X) s =
      (ihom K).map (pointEvaluation K X s) := by
  apply MonoidalClosed.uncurry_injective
  rw [pointEvaluation_comp, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_natural_left,
    originalSelfInterchangeNatIso_hom_double_uncurry, MonoidalClosed.uncurry_ihom_map,
    pointEvaluation_comp]
  simp only [MonoidalClosed.uncurry_eq]
  rw [← whiskerLeft_comp_assoc]
  exact pointInsertion_interchange_assoc K ((ihom K).obj ((ihom K).obj X)) s
    (K ◁ (ihom.ev K).app ((ihom K).obj X) ≫ (ihom.ev K).app X)

/-- Both original parameter evaluations exchange under the complete original closed swap. -/
theorem interchange_two_evaluations (K X : C) (s t : (𝟙_ C) ⟶ K) :
    (originalSelfInterchangeNatIso K).hom.app X ≫
        pointEvaluation K ((ihom K).obj X) s ≫ pointEvaluation K X t =
      pointEvaluation K ((ihom K).obj X) t ≫ pointEvaluation K X s := by
  rw [← Category.assoc, interchange_outer_evaluation]
  exact pointEvaluation_naturality K t (pointEvaluation K X s)

end CategoryTheory.MonoidalClosed.NativeEvaluationInterchange

namespace CategoryTheory.MonoidalClosed.NativeCartesianEvaluation

universe uC vC
variable {C : Type uC} [Category.{vC} C] [CartesianMonoidalCategory C]

/-- The actual unit insertion evaluates the same original Cartesian point before and after a map. -/
theorem pointPair_transport {P K H J : C} (hP : IsTerminal P) (j : H ⟶ J) (a : P ⟶ K) :
    j ≫ (λ_ J).inv ≫
        ((CartesianMonoidalCategory.isTerminalTensorUnit.uniqueUpToIso hP).hom ▷ J) ≫ a ▷ J =
      CartesianMonoidalCategory.lift (hP.from H ≫ a) (𝟙 H) ≫ K ◁ j := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
      CartesianMonoidalCategory.whiskerRight_fst_assoc,
      CartesianMonoidalCategory.whiskerLeft_fst, CartesianMonoidalCategory.lift_fst,
      CartesianMonoidalCategory.leftUnitor_inv_fst_assoc]
    simpa only [Category.assoc] using congrArg (fun q : H ⟶ P => q ≫ a)
      (hP.hom_ext
        (j ≫ CartesianMonoidalCategory.toUnit J ≫
          (CartesianMonoidalCategory.isTerminalTensorUnit.uniqueUpToIso hP).hom)
        (hP.from H))
  · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
      CartesianMonoidalCategory.whiskerLeft_snd, CartesianMonoidalCategory.lift_snd_assoc,
      CartesianMonoidalCategory.leftUnitor_inv_snd, Category.comp_id, Category.id_comp]

/-- The original tensor/product comparison carries the complete selected pair. -/
theorem tensorPair_compare (A B H : C) [HasBinaryProduct A B] (c : H ⟶ A) (d : H ⟶ B) :
    Limits.prod.lift c d ≫ (CartesianMonoidalCategory.tensorLeftIsoProd A).inv.app B =
      CartesianMonoidalCategory.lift c d := by
  let e := (CartesianMonoidalCategory.tensorLeftIsoProd A).app B
  have hf : e.hom ≫ (Limits.prod.fst : A ⨯ B ⟶ A) =
      CartesianMonoidalCategory.fst A B :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct A B)
      (limit.isLimit _) ⟨WalkingPair.left⟩
  have hs : e.hom ≫ (Limits.prod.snd : A ⨯ B ⟶ B) =
      CartesianMonoidalCategory.snd A B :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct A B)
      (limit.isLimit _) ⟨WalkingPair.right⟩
  apply (cancel_mono e.hom).mp
  change (Limits.prod.lift c d ≫ e.inv) ≫ e.hom =
    CartesianMonoidalCategory.lift c d ≫ e.hom
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply Limits.prod.hom_ext
  · rw [Limits.prod.lift_fst, Category.assoc, hf, CartesianMonoidalCategory.lift_fst]
  · rw [Limits.prod.lift_snd, Category.assoc, hs, CartesianMonoidalCategory.lift_snd]

end CategoryTheory.MonoidalClosed.NativeCartesianEvaluation

namespace PointedCGWH.DoubleLoopInterchangeGeometry

open CategoryTheory.Limits
open CategoryTheory.MonoidalClosed.NativeEvaluationInterchange
open CategoryTheory.MonoidalClosed.NativeCartesianEvaluation

/-- The complete native interval point as an actual map from the original pointed smash unit. -/
def spherePoint (t : TopCat.I.{v}) : (𝟙_ PointedCGWH.{u, v}) ⟶ PointedCGWH.sphereOne :=
  ((Under.costarAdjForget CGWH.point).homEquiv CGWH.point PointedCGWH.sphereOne).symm
    (ConcreteCategory.ofHom (ContinuousMap.const _ (PointedCGWH.sphereOneParam t)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original free summand of the pointed unit retains the entire interval point. -/
theorem spherePoint_free (t : TopCat.I.{v}) :
    (coprod.inr : CGWH.point.{u, v} ⟶ (𝟙_ PointedCGWH.{u, v}).right) ≫
        (spherePoint t).right =
      (ConcreteCategory.ofHom (ContinuousMap.const _ (PointedCGWH.sphereOneParam t)) :
        CGWH.point.{u, v} ⟶ PointedCGWH.sphereOne.right) := by
  have hunit : (Under.costarAdjForget CGWH.point.{u, v}).unit.app CGWH.point =
      (coprod.inr : CGWH.point.{u, v} ⟶ (𝟙_ PointedCGWH.{u, v}).right) := by
    unfold Under.costarAdjForget
    rw [Adjunction.comp_unit_app, Monad.adj_unit,
      Equivalence.toAdjunction_unit, coprodMonad_η_app]
    dsimp [algebraEquivUnder, Monad.forget, Monad.Algebra.isoMk]
    rfl
  have h := ((Under.costarAdjForget CGWH.point).homEquiv
    CGWH.point PointedCGWH.sphereOne).apply_symm_apply
      (ConcreteCategory.ofHom (ContinuousMap.const _ (PointedCGWH.sphereOneParam t)))
  rw [Adjunction.homEquiv_unit] at h
  change (Under.costarAdjForget CGWH.point).unit.app CGWH.point ≫
    (spherePoint t).right = _ at h
  calc
    _ = (Under.costarAdjForget CGWH.point).unit.app CGWH.point ≫ (spherePoint t).right :=
      congrArg (fun f : CGWH.point.{u, v} ⟶ (𝟙_ PointedCGWH.{u, v}).right =>
        f ≫ (spherePoint t).right) hunit.symm
    _ = _ := h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Native evaluation at each original interval point is the closed unit-point evaluation. -/
theorem pointEvaluation_eq_loopEvalAt (A : PointedCGWH.{u, v}) (t : TopCat.I.{v}) :
    pointEvaluation PointedCGWH.sphereOne A (spherePoint t) =
      PointedCGWH.loopEvalAt A t := by
  let _ : BraidedCategory CGWH.{u, v} := BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let K := PointedCGWH.sphereOne.{u, v}
  let H := PointedCGWH.loop.obj A
  let J := (ihom K.right).obj A.right
  let j : H.right ⟶ J :=
    (CategoryTheory.Pointed.basedInternalHomToInternalHom CGWH.point CGWH.point_isTerminal K).app A
  let a : CGWH.point.{u, v} ⟶ K.right :=
    ConcreteCategory.ofHom (ContinuousMap.const _ (PointedCGWH.sphereOneParam t))
  let p : H.right ⟶ K.right ⊗ H.right :=
    CartesianMonoidalCategory.lift (CGWH.point_isTerminal.from H.right ≫ a) (𝟙 H.right)
  let q := (CategoryTheory.Pointed.smashPresentation CGWH.point CGWH.point_isTerminal K H).2.1.inl
  let e : K.right ⊗ H.right ≅ K.right ⨯ H.right :=
    (CartesianMonoidalCategory.tensorLeftIsoProd K.right).app H.right
  have hu : (pointEvaluation K A (spherePoint t)).right =
      j ≫ (λ_ J).inv ≫
        ((CartesianMonoidalCategory.isTerminalTensorUnit.uniqueUpToIso
          CGWH.point_isTerminal).hom ▷ J) ≫ a ▷ J ≫ (ihom.ev K.right).app A.right := by
    have h := CategoryTheory.Pointed.basedInternalHom_pre_unit_carrier
      CGWH.point CGWH.point_isTerminal K A (spherePoint t)
    change (pointEvaluation K A (spherePoint t)).right =
      j ≫ (λ_ J).inv ≫
        ((CartesianMonoidalCategory.isTerminalTensorUnit.uniqueUpToIso
          CGWH.point_isTerminal).hom ▷ J) ≫
        (coprod.inr ≫ (spherePoint t).right) ▷ J ≫ (ihom.ev K.right).app A.right at h
    rw [spherePoint_free] at h
    exact h
  have hp := pointPair_transport CGWH.point_isTerminal j a
  have he := CategoryTheory.Pointed.smashQuotient_basedEval
    CGWH.point CGWH.point_isTerminal K A
  have he' : q ≫ ((PointedCGWH.basedEval K).app A).right =
      K.right ◁ j ≫ (ihom.ev K.right).app A.right := he
  have hpair : Limits.prod.lift (CGWH.point_isTerminal.from H.right ≫ a) (𝟙 H.right) ≫
      e.inv = p := tensorPair_compare K.right H.right H.right
        (CGWH.point_isTerminal.from H.right ≫ a) (𝟙 H.right)
  apply Under.UnderMorphism.ext
  change (pointEvaluation K A (spherePoint t)).right =
    ((Limits.prod.lift (CGWH.point_isTerminal.from H.right ≫ a) (𝟙 H.right) ≫ e.inv) ≫ q) ≫
      ((PointedCGWH.basedEval K).app A).right
  calc
    _ = (p ≫ K.right ◁ j) ≫ (ihom.ev K.right).app A.right :=
      hu.trans (by
        simpa only [Category.assoc] using
          congrArg (fun f => f ≫ (ihom.ev K.right).app A.right) hp)
    _ = (p ≫ q) ≫ ((PointedCGWH.basedEval K).app A).right := by
      simpa only [Category.assoc] using
        congrArg (fun f => p ≫ f) he'.symm
    _ = _ := congrArg
      (fun f : H.right ⟶ K.right ⊗ H.right =>
        (f ≫ q) ≫ ((PointedCGWH.basedEval K).app A).right) hpair.symm

/-- The original native closed interchange, with its original complete pointed map. -/
abbrev interchange (A : PointedCGWH.{u, v}) :
    PointedCGWH.loop.obj (PointedCGWH.loop.obj A) ⟶
      PointedCGWH.loop.obj (PointedCGWH.loop.obj A) :=
  (CategoryTheory.MonoidalClosed.OriginalLoopInterchangeGeometry.originalSelfInterchangeNatIso
    PointedCGWH.sphereOne).hom.app A

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Both complete original interval evaluations exchange under the native closed interchange. -/
@[reassoc]
theorem interchange_two_loopEvalAt (A : PointedCGWH.{u, v}) (s t : TopCat.I.{v}) :
    interchange A ≫ PointedCGWH.loopEvalAt (PointedCGWH.loop.obj A) s ≫
        PointedCGWH.loopEvalAt A t =
      PointedCGWH.loopEvalAt (PointedCGWH.loop.obj A) t ≫ PointedCGWH.loopEvalAt A s := by
  have h := interchange_two_evaluations
    PointedCGWH.sphereOne A (spherePoint s) (spherePoint t)
  rw [pointEvaluation_eq_loopEvalAt, pointEvaluation_eq_loopEvalAt,
    pointEvaluation_eq_loopEvalAt, pointEvaluation_eq_loopEvalAt] at h
  exact h

/-- The whole landed double-loop function exchanges the two actual interval parameters. -/
theorem interchange_landing_evaluation (A : PointedCGWH.{u, v})
    (γ : (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right)
    (s t : unitInterval) :
    PointedCGWH.loopLanding A
        (PointedCGWH.loopLanding (PointedCGWH.loop.obj A) ((interchange A).right γ) s) t =
      PointedCGWH.loopLanding A
        (PointedCGWH.loopLanding (PointedCGWH.loop.obj A) γ t) s := by
  let s' := TopCat.I.homeomorph.{v}.symm s
  let t' := TopCat.I.homeomorph.{v}.symm t
  have hs : TopCat.I.homeomorph s' = s := TopCat.I.homeomorph.apply_symm_apply s
  have ht : TopCat.I.homeomorph t' = t := TopCat.I.homeomorph.apply_symm_apply t
  rw [← hs, ← ht, PointedCGWH.loopLanding_evaluation,
    PointedCGWH.loopLanding_evaluation, PointedCGWH.loopLanding_evaluation,
    PointedCGWH.loopLanding_evaluation]
  exact congrArg
    (fun f : PointedCGWH.loop.obj (PointedCGWH.loop.obj A) ⟶ A => f.right γ)
    (interchange_two_loopEvalAt A s' t')

/-- The original native loop landing supplies the actual multiplicative cube-group comparison. -/
def landingMulEquiv (k : ℕ) (A : PointedCGWH.{u, v}) :
    piN (k + 1) (PointedCGWH.loop.obj A) ≃*
      HomotopyGroup.Pi (k + 1)
        (LoopSpace (CGWH.cgwhToTop.obj A.right) (underlyingBasepoint A))
        (Path.refl (underlyingBasepoint A)) :=
  TopCat.piPositiveMulEquivOfWeakEquivalence k (PointedCGWH.loopLanding A)
    (underlyingBasepoint (PointedCGWH.loop.obj A)) (Path.refl (underlyingBasepoint A))
    (PointedCGWH.loopLanding_basepoint A) (PointedCGWH.LoopGeometry.loopLanding_weak A)

/-- The whole comparison function is the actual equality-aware map of the original landing. -/
theorem landingMulEquiv_apply (k : ℕ) (A : PointedCGWH.{u, v})
    (a : piN (k + 1) (PointedCGWH.loop.obj A)) :
    landingMulEquiv k A a =
      HomotopyGroup.mapHomOfEq (PointedCGWH.loopLanding A).hom
        (PointedCGWH.loopLanding_basepoint A) k a :=
  TopCat.piPositiveMulEquivOfWeakEquivalence_apply k (PointedCGWH.loopLanding A)
    (underlyingBasepoint (PointedCGWH.loop.obj A)) (Path.refl (underlyingBasepoint A))
    (PointedCGWH.loopLanding_basepoint A) (PointedCGWH.LoopGeometry.loopLanding_weak A) a

/-- The actual native landing followed by the original topological cube-loop shift. -/
def loopMulEquiv (k : ℕ) (A : PointedCGWH.{u, v}) :
    piN (k + 1) (PointedCGWH.loop.obj A) ≃* piN (k + 2) A :=
  (landingMulEquiv k A).trans
    (HomotopyGroup.loopShiftMulEquiv k (CGWH.cgwhToTop.obj A.right) (underlyingBasepoint A))

/-- Both original native loop landings and both actual cube shifts give the full double-loop map. -/
def doubleLoopMulEquiv (k : ℕ) (A : PointedCGWH.{u, v}) :
    piN (k + 1) (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)) ≃* piN (k + 3) A :=
  (loopMulEquiv k (PointedCGWH.loop.obj A)).trans (loopMulEquiv (k + 1) A)

/-- The entire native double-loop comparison keeps both complete original forward functions. -/
theorem doubleLoopMulEquiv_apply (k : ℕ) (A : PointedCGWH.{u, v})
    (a : piN (k + 1) (PointedCGWH.loop.obj (PointedCGWH.loop.obj A))) :
    doubleLoopMulEquiv k A a = loopMulEquiv (k + 1) A
      (loopMulEquiv k (PointedCGWH.loop.obj A) a) := rfl

/-- The inverse native double-loop comparison retains both original inverse functions. -/
theorem doubleLoopMulEquiv_symm_apply (k : ℕ) (A : PointedCGWH.{u, v}) (a : piN (k + 3) A) :
    (doubleLoopMulEquiv k A).symm a =
      (loopMulEquiv k (PointedCGWH.loop.obj A)).symm ((loopMulEquiv (k + 1) A).symm a) := rfl

/-- The original positive homotopy group of a native loop is commutative, including its π₁. -/
theorem loop_mul_comm (k : ℕ) (A : PointedCGWH.{u, v})
    (a b : piN (k + 1) (PointedCGWH.loop.obj A)) : a * b = b * a := by
  apply (loopMulEquiv k A).injective
  rw [map_mul, map_mul]
  exact mul_comm _ _

/-- The canonical multiplication on the actual native double loop is commutative for every k. -/
theorem doubleLoop_mul_comm (k : ℕ) (A : PointedCGWH.{u, v})
    (a b : piN (k + 1) (PointedCGWH.loop.obj (PointedCGWH.loop.obj A))) : a * b = b * a :=
  loop_mul_comm k (PointedCGWH.loop.obj A) a b

/-- The additional commutativity law extends the original canonical native-loop group. -/
@[instance_reducible]
def loopCommGroup (k : ℕ) (A : PointedCGWH.{u, v}) :
    CommGroup (piN (k + 1) (PointedCGWH.loop.obj A)) where
  toGroup := inferInstance
  mul_comm := loop_mul_comm k A

/-- The native double-loop commutative group keeps the original positive group structure. -/
@[instance_reducible]
def doubleLoopCommGroup (k : ℕ) (A : PointedCGWH.{u, v}) :
    CommGroup (piN (k + 1) (PointedCGWH.loop.obj (PointedCGWH.loop.obj A))) :=
  loopCommGroup k (PointedCGWH.loop.obj A)

end PointedCGWH.DoubleLoopInterchangeGeometry

namespace HomotopyGroup.LoopCoordinateGeometry

variable {X : Type w} [TopologicalSpace X] {x : X}

/-- Equality-aware postcomposition retains the complete original cube representative. -/
theorem mapHomOfEq_mk {Y : Type u} [TopologicalSpace Y] {y : Y}
    (f : C(X, Y)) (hf : f x = y) (n : ℕ)
    (p : GenLoop (Fin (n + 1)) X x) :
    HomotopyGroup.mapHomOfEq f hf n (HomotopyGroup.mk p) =
      HomotopyGroup.mk
        (⟨(GenLoop.map f p).1,
          fun q hq => (GenLoop.boundary (GenLoop.map f p) q hq).trans hf⟩ :
          GenLoop (Fin (n + 1)) Y y) :=
  _root_.HomotopyGroup.mapHomOfEq_mk n f hf p

/-- Append the actual loop coordinate after every original cube coordinate. -/
def appendLoopCube (n : ℕ)
    (p : GenLoop (Fin (n + 1)) (LoopSpace X x) (Path.refl x)) :
    GenLoop (Fin (n + 2)) X x :=
  ⟨⟨fun q => p (fun i => q i.castSucc) (q (Fin.last (n + 1))), by fun_prop⟩, by
    intro q hq
    change p (fun i => q i.castSucc) (q (Fin.last (n + 1))) = x
    rcases hq with ⟨j, hj⟩
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · have h : (fun i => q i.castSucc) ∈ Cube.boundary (Fin (n + 1)) := ⟨i, hj⟩
      rw [GenLoop.boundary p _ h]
      rfl
    · rcases hj with h | h
      · rw [h]
        exact (p _).source
      · rw [h]
        exact (p _).target⟩

/-- Every whole loop-shift representative is the actual appended cube coordinate. -/
theorem loopShiftMulEquiv_mk (n : ℕ)
    (p : GenLoop (Fin (n + 1)) (LoopSpace X x) (Path.refl x)) :
    HomotopyGroup.loopShiftMulEquiv n X x (HomotopyGroup.mk p) =
      HomotopyGroup.mk (appendLoopCube n p) := by
  change HomotopyGroup.mk _ = HomotopyGroup.mk _
  apply congrArg HomotopyGroup.mk
  apply GenLoop.ext
  intro q
  change p (fun i => q ((finSumFinEquiv : Fin (n + 1) ⊕ Fin 1 ≃ Fin (n + 2)) (Sum.inl i)))
      (q ((finSumFinEquiv : Fin (n + 1) ⊕ Fin 1 ≃ Fin (n + 2)) (Sum.inr (0 : Fin 1)))) =
    p (fun i => q i.castSucc) (q (Fin.last (n + 1)))
  have hFirst : (fun i : Fin (n + 1) =>
      q ((finSumFinEquiv : Fin (n + 1) ⊕ Fin 1 ≃ Fin (n + 2)) (Sum.inl i))) =
      (fun i => q i.castSucc) := by
    funext i
    exact congrArg q (Fin.ext rfl)
  have hLast :
      (finSumFinEquiv : Fin (n + 1) ⊕ Fin 1 ≃ Fin (n + 2)) (Sum.inr (0 : Fin 1)) =
        Fin.last (n + 1) := Fin.ext rfl
  rw [hFirst, hLast]

end HomotopyGroup.LoopCoordinateGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PointedCGWH.DoubleLoopInterchangeGeometry

open HomotopyGroup.LoopCoordinateGeometry
open PointedCGWH.CubeColimitGeometry

/-- Land the full native loop representative using its actual selected-point equality. -/
def landingCube (k : ℕ) (A : PointedCGWH.{u, v})
    (p : GenLoop (Fin (k + 1)) (CGWH.cgwhToTop.obj (PointedCGWH.loop.obj A).right)
      (underlyingBasepoint (PointedCGWH.loop.obj A))) :
    GenLoop (Fin (k + 1))
      (LoopSpace (CGWH.cgwhToTop.obj A.right) (underlyingBasepoint A))
      (Path.refl (underlyingBasepoint A)) :=
  ⟨(PointedCGWH.loopLanding A).hom.comp p.1, fun q hq =>
    (congrArg (PointedCGWH.loopLanding A) (GenLoop.boundary p q hq)).trans
      (PointedCGWH.loopLanding_basepoint A)⟩

/-- The native landing retains every original cube and loop parameter. -/
theorem landingCube_apply (k : ℕ) (A : PointedCGWH.{u, v})
    (p : GenLoop (Fin (k + 1)) (CGWH.cgwhToTop.obj (PointedCGWH.loop.obj A).right)
      (underlyingBasepoint (PointedCGWH.loop.obj A)))
    (q : Fin (k + 1) → unitInterval) (t : unitInterval) :
    (landingCube k A p).1 q t = PointedCGWH.loopLanding A (p.1 q) t := rfl

/-- Append the complete native loop parameter after every original cube coordinate. -/
def nativeLoopCube (k : ℕ) (A : PointedCGWH.{u, v})
    (p : GenLoop (Fin (k + 1)) (CGWH.cgwhToTop.obj (PointedCGWH.loop.obj A).right)
      (underlyingBasepoint (PointedCGWH.loop.obj A))) :
    GenLoop (Fin (k + 2)) (CGWH.cgwhToTop.obj A.right) (underlyingBasepoint A) :=
  appendLoopCube k (landingCube k A p)

/-- The whole native shifted cube retains the original landing and final coordinate. -/
theorem nativeLoopCube_apply (k : ℕ) (A : PointedCGWH.{u, v})
    (p : GenLoop (Fin (k + 1)) (CGWH.cgwhToTop.obj (PointedCGWH.loop.obj A).right)
      (underlyingBasepoint (PointedCGWH.loop.obj A)))
    (q : Fin (k + 2) → unitInterval) :
    (nativeLoopCube k A p).1 q =
      PointedCGWH.loopLanding A (p.1 (fun i => q i.castSucc)) (q (Fin.last (k + 1))) := rfl

/-- The actual native group comparison retains the whole original cube representative. -/
theorem loopMulEquiv_mk (k : ℕ) (A : PointedCGWH.{u, v})
    (p : GenLoop (Fin (k + 1)) (CGWH.cgwhToTop.obj (PointedCGWH.loop.obj A).right)
      (underlyingBasepoint (PointedCGWH.loop.obj A))) :
    loopMulEquiv k A (HomotopyGroup.mk p) = HomotopyGroup.mk (nativeLoopCube k A p) := by
  change HomotopyGroup.loopShiftMulEquiv k
    (CGWH.cgwhToTop.obj A.right) (underlyingBasepoint A)
      (landingMulEquiv k A (HomotopyGroup.mk p)) = _
  have hmap := mapHomOfEq_mk (PointedCGWH.loopLanding A).hom
    (PointedCGWH.loopLanding_basepoint A) k p
  change HomotopyGroup.mapHomOfEq (PointedCGWH.loopLanding A).hom
    (PointedCGWH.loopLanding_basepoint A) k (HomotopyGroup.mk p) =
      HomotopyGroup.mk (landingCube k A p) at hmap
  rw [landingMulEquiv_apply, hmap]
  exact loopShiftMulEquiv_mk k (landingCube k A p)

/-- Both original native loop parameters are appended after the original cube coordinates. -/
def doubleNativeLoopCube (k : ℕ) (A : PointedCGWH.{u, v})
    (p : GenLoop (Fin (k + 1))
      (CGWH.cgwhToTop.obj (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right)
      (underlyingBasepoint (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)))) :
    GenLoop (Fin (k + 3)) (CGWH.cgwhToTop.obj A.right) (underlyingBasepoint A) :=
  nativeLoopCube (k + 1) A (nativeLoopCube k (PointedCGWH.loop.obj A) p)

/-- The actual double-loop comparison keeps every whole shifted cube representative. -/
theorem doubleLoopMulEquiv_mk (k : ℕ) (A : PointedCGWH.{u, v})
    (p : GenLoop (Fin (k + 1))
      (CGWH.cgwhToTop.obj (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right)
      (underlyingBasepoint (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)))) :
    doubleLoopMulEquiv k A (HomotopyGroup.mk p) =
      HomotopyGroup.mk (doubleNativeLoopCube k A p) := by
  rw [doubleLoopMulEquiv_apply, loopMulEquiv_mk, loopMulEquiv_mk]
  rfl

/-- Both literal final-coordinate values occur in the original double native cube. -/
theorem doubleNativeLoopCube_apply (k : ℕ) (A : PointedCGWH.{u, v})
    (p : GenLoop (Fin (k + 1))
      (CGWH.cgwhToTop.obj (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right)
      (underlyingBasepoint (PointedCGWH.loop.obj (PointedCGWH.loop.obj A))))
    (q : Fin (k + 3) → unitInterval) :
    (doubleNativeLoopCube k A p).1 q =
      PointedCGWH.loopLanding A
        (PointedCGWH.loopLanding (PointedCGWH.loop.obj A)
          (p.1 (fun i => q i.castSucc.castSucc))
          (q (Fin.last (k + 1)).castSucc)) (q (Fin.last (k + 2))) := rfl

/-- The two appended native loop coordinates are distinct even when k is zero. -/
theorem finalCoordinates_ne (k : ℕ) :
    (Fin.last (k + 1)).castSucc ≠ (Fin.last (k + 2) : Fin (k + 3)) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_last] at hv
  omega

/-- The complete native closed map is exactly the transposition of the two appended coordinates. -/
theorem doubleNativeLoopCube_interchange (k : ℕ) (A : PointedCGWH.{u, v})
    (p : GenLoop (Fin (k + 1))
      (CGWH.cgwhToTop.obj (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)).right)
      (underlyingBasepoint (PointedCGWH.loop.obj (PointedCGWH.loop.obj A)))) :
    doubleNativeLoopCube k A (cubeMap (k + 1) (interchange A) p) =
      GenLoop.congr (underlyingBasepoint A)
        (Equiv.swap (Fin.last (k + 1)).castSucc (Fin.last (k + 2)))
        (doubleNativeLoopCube k A p) := by
  apply GenLoop.ext
  intro q
  let e := Equiv.swap (Fin.last (k + 1)).castSucc (Fin.last (k + 2))
  have hpoint := cubeMap_apply (k + 1) (interchange A) p
    (fun i => q i.castSucc.castSucc)
  have hlhs := doubleNativeLoopCube_apply k A (cubeMap (k + 1) (interchange A) p) q
  have hlhs' : (doubleNativeLoopCube k A (cubeMap (k + 1) (interchange A) p)).1 q =
      PointedCGWH.loopLanding A
        (PointedCGWH.loopLanding (PointedCGWH.loop.obj A)
          ((interchange A).right (p.1 (fun i => q i.castSucc.castSucc)))
          (q (Fin.last (k + 1)).castSucc)) (q (Fin.last (k + 2))) :=
    hlhs.trans (congrArg (fun γ => PointedCGWH.loopLanding A
      (PointedCGWH.loopLanding (PointedCGWH.loop.obj A) γ
        (q (Fin.last (k + 1)).castSucc)) (q (Fin.last (k + 2)))) hpoint)
  change (doubleNativeLoopCube k A (cubeMap (k + 1) (interchange A) p)).1 q =
    (doubleNativeLoopCube k A p).1 (fun i => q (e i))
  rw [hlhs', interchange_landing_evaluation,
    doubleNativeLoopCube_apply]
  have hFirst : (fun i : Fin (k + 1) =>
      q (Equiv.swap (Fin.last (k + 1)).castSucc (Fin.last (k + 2))
        i.castSucc.castSucc)) = (fun i => q i.castSucc.castSucc) := by
    funext i
    have hi₁ : i.castSucc.castSucc ≠ (Fin.last (k + 1)).castSucc := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_last] at hv
      omega
    have hi₂ : i.castSucc.castSucc ≠ (Fin.last (k + 2) : Fin (k + 3)) := by
      exact Fin.castSucc_ne_last _
    rw [Equiv.swap_apply_of_ne_of_ne hi₁ hi₂]
  rw [hFirst, Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- The original native closed interchange acts as inversion on every positive double-loop group. -/
theorem interchange_piNMap_eq_inv (k : ℕ) (A : PointedCGWH.{u, v})
    (a : piN (k + 1) (PointedCGWH.loop.obj (PointedCGWH.loop.obj A))) :
    piNMap (k + 1) (interchange A) a = a⁻¹ := by
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  apply (doubleLoopMulEquiv k A).injective
  have hmap := piNMap_mk (k + 1) (interchange A) p
  have hinv := HomotopyGroup.CoordinateInterchange.swap_class_eq_inverse
    (Fin.last (k + 1)).castSucc (Fin.last (k + 2)) (finalCoordinates_ne k)
    (doubleNativeLoopCube k A p)
  calc
    _ = doubleLoopMulEquiv k A (HomotopyGroup.mk (cubeMap (k + 1) (interchange A) p)) :=
      congrArg (doubleLoopMulEquiv k A) hmap
    _ = HomotopyGroup.mk (doubleNativeLoopCube k A (cubeMap (k + 1) (interchange A) p)) :=
      doubleLoopMulEquiv_mk k A (cubeMap (k + 1) (interchange A) p)
    _ = HomotopyGroup.mk
        (GenLoop.congr (underlyingBasepoint A)
          (Equiv.swap (Fin.last (k + 1)).castSucc (Fin.last (k + 2)))
          (doubleNativeLoopCube k A p)) :=
      congrArg HomotopyGroup.mk (doubleNativeLoopCube_interchange k A p)
    _ = (HomotopyGroup.mk (doubleNativeLoopCube k A p))⁻¹ := hinv
    _ = (doubleLoopMulEquiv k A (HomotopyGroup.mk p))⁻¹ :=
      congrArg Inv.inv (doubleLoopMulEquiv_mk k A p).symm
    _ = _ := (map_inv (doubleLoopMulEquiv k A) (HomotopyGroup.mk p)).symm

/-- The complete original positive group-functor map retains that same inversion function. -/
theorem interchange_piNPositiveMap_eq_inv (k : ℕ) (A : PointedCGWH.{u, v})
    (a : piN (k + 1) (PointedCGWH.loop.obj (PointedCGWH.loop.obj A))) :
    (piNPositiveMap k (interchange A)).hom a = a⁻¹ := by
  rw [piNPositiveMap_apply]
  exact interchange_piNMap_eq_inv k A a

/-- The original interval evaluation is natural in every complete pointed target map. -/
@[reassoc]
theorem loopEvalAt_naturality {A B : PointedCGWH.{u, v}} (f : A ⟶ B) (t : TopCat.I.{v}) :
    PointedCGWH.loop.map f ≫ PointedCGWH.loopEvalAt B t =
      PointedCGWH.loopEvalAt A t ≫ f := by
  have h := CategoryTheory.MonoidalClosed.NativeEvaluationInterchange.pointEvaluation_naturality
    PointedCGWH.sphereOne (spherePoint t) f
  rw [pointEvaluation_eq_loopEvalAt, pointEvaluation_eq_loopEvalAt] at h
  exact h

/-- The full original native loop landing retains strict postcomposition at every parameter. -/
theorem loopLanding_map_evaluation {A B : PointedCGWH.{u, v}} (f : A ⟶ B)
    (γ : (PointedCGWH.loop.obj A).right) (t : unitInterval) :
    PointedCGWH.loopLanding B ((PointedCGWH.loop.map f).right γ) t =
      f.right (PointedCGWH.loopLanding A γ t) := by
  let t' := TopCat.I.homeomorph.{v}.symm t
  have ht : TopCat.I.homeomorph t' = t := TopCat.I.homeomorph.apply_symm_apply t
  rw [← ht, PointedCGWH.loopLanding_evaluation, PointedCGWH.loopLanding_evaluation]
  exact congrArg (fun g : PointedCGWH.loop.obj A ⟶ B => g.right γ)
    (loopEvalAt_naturality f t')

/-- Every whole native shifted cube is natural in every original pointed target map. -/
theorem nativeLoopCube_naturality (k : ℕ) {A B : PointedCGWH.{u, v}} (f : A ⟶ B)
    (p : GenLoop (Fin (k + 1)) (CGWH.cgwhToTop.obj (PointedCGWH.loop.obj A).right)
      (underlyingBasepoint (PointedCGWH.loop.obj A))) :
    nativeLoopCube k B (cubeMap (k + 1) (PointedCGWH.loop.map f) p) =
      cubeMap (k + 2) f (nativeLoopCube k A p) := by
  apply GenLoop.ext
  intro q
  have hl := nativeLoopCube_apply k B (cubeMap (k + 1) (PointedCGWH.loop.map f) p) q
  have hp := cubeMap_apply (k + 1) (PointedCGWH.loop.map f) p (fun i => q i.castSucc)
  have hr := cubeMap_apply (k + 2) f (nativeLoopCube k A p) q
  have ha := nativeLoopCube_apply k A p q
  calc
    _ = PointedCGWH.loopLanding B
        ((PointedCGWH.loop.map f).right (p.1 (fun i => q i.castSucc)))
        (q (Fin.last (k + 1))) :=
      hl.trans (congrArg (fun γ => PointedCGWH.loopLanding B γ (q (Fin.last (k + 1)))) hp)
    _ = f.right
        (PointedCGWH.loopLanding A (p.1 (fun i => q i.castSucc)) (q (Fin.last (k + 1)))) :=
      loopLanding_map_evaluation f _ _
    _ = f.right ((nativeLoopCube k A p).1 q) := congrArg f.right ha.symm
    _ = _ := hr.symm

/-- The complete multiplicative native loop comparison is natural on the original cube quotient. -/
theorem loopMulEquiv_naturality (k : ℕ) {A B : PointedCGWH.{u, v}} (f : A ⟶ B)
    (a : piN (k + 1) (PointedCGWH.loop.obj A)) :
    loopMulEquiv k B (piNMap (k + 1) (PointedCGWH.loop.map f) a) =
      piNMap (k + 2) f (loopMulEquiv k A a) := by
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  have hs := piNMap_mk (k + 1) (PointedCGWH.loop.map f) p
  have ht := piNMap_mk (k + 2) f (nativeLoopCube k A p)
  calc
    _ = loopMulEquiv k B
        (HomotopyGroup.mk (cubeMap (k + 1) (PointedCGWH.loop.map f) p)) :=
      congrArg (loopMulEquiv k B) hs
    _ = HomotopyGroup.mk
        (nativeLoopCube k B (cubeMap (k + 1) (PointedCGWH.loop.map f) p)) :=
      loopMulEquiv_mk k B _
    _ = HomotopyGroup.mk (cubeMap (k + 2) f (nativeLoopCube k A p)) :=
      congrArg HomotopyGroup.mk (nativeLoopCube_naturality k f p)
    _ = piNMap (k + 2) f (HomotopyGroup.mk (nativeLoopCube k A p)) := ht.symm
    _ = _ := congrArg (piNMap (k + 2) f) (loopMulEquiv_mk k A p).symm

/-- Both whole original native loop comparisons are natural in every pointed target map. -/
theorem doubleLoopMulEquiv_naturality (k : ℕ) {A B : PointedCGWH.{u, v}} (f : A ⟶ B)
    (a : piN (k + 1) (PointedCGWH.loop.obj (PointedCGWH.loop.obj A))) :
    doubleLoopMulEquiv k B
        (piNMap (k + 1) (PointedCGWH.loop.map (PointedCGWH.loop.map f)) a) =
      piNMap (k + 3) f (doubleLoopMulEquiv k A a) := by
  change loopMulEquiv (k + 1) B
      (loopMulEquiv k (PointedCGWH.loop.obj B)
        (piNMap (k + 1) (PointedCGWH.loop.map (PointedCGWH.loop.map f)) a)) = _
  rw [loopMulEquiv_naturality, loopMulEquiv_naturality]
  rfl

/-- The full original closed interchange is natural on both complete native loop functors. -/
@[reassoc]
theorem interchange_naturality {A B : PointedCGWH.{u, v}} (f : A ⟶ B) :
    PointedCGWH.loop.map (PointedCGWH.loop.map f) ≫ interchange B =
      interchange A ≫ PointedCGWH.loop.map (PointedCGWH.loop.map f) :=
  (CategoryTheory.MonoidalClosed.OriginalLoopInterchangeGeometry.originalSelfInterchangeNatIso
    PointedCGWH.sphereOne).hom.naturality f

/-- Native loop-group inversion uses the original multiplication and its proved commutativity. -/
def loopGroupInversion (k : ℕ) (A : PointedCGWH.{u, v}) :
    (piNPositiveFunctor k).obj (PointedCGWH.loop.obj A) ⟶
      (piNPositiveFunctor k).obj (PointedCGWH.loop.obj A) :=
  GrpCat.ofHom
    { toFun := Inv.inv
      map_one' := inv_one
      map_mul' := fun a b => (mul_inv_rev a b).trans (loop_mul_comm k A b⁻¹ a⁻¹) }

/-- The entire original native loop-group inversion function is literal group inversion. -/
theorem loopGroupInversion_apply (k : ℕ) (A : PointedCGWH.{u, v})
    (a : piN (k + 1) (PointedCGWH.loop.obj A)) :
    (loopGroupInversion k A).hom a = a⁻¹ := rfl

/-- Whole native loop-group inversion is natural for every original pointed target map. -/
@[reassoc]
theorem loopGroupInversion_naturality (k : ℕ) {A B : PointedCGWH.{u, v}} (f : A ⟶ B) :
    (piNPositiveFunctor k).map (PointedCGWH.loop.map f) ≫ loopGroupInversion k B =
      loopGroupInversion k A ≫ (piNPositiveFunctor k).map (PointedCGWH.loop.map f) := by
  ext a
  exact (map_inv ((piNPositiveFunctor k).map (PointedCGWH.loop.map f)).hom a).symm

/-- The original inversion homomorphisms form a whole natural transformation on native loops. -/
def loopGroupInversionNatTrans (k : ℕ) :
    PointedCGWH.loop.{u, v} ⋙ piNPositiveFunctor k ⟶
      PointedCGWH.loop ⋙ piNPositiveFunctor k where
  app A := loopGroupInversion k A
  naturality {A B} f := loopGroupInversion_naturality k (A := A) (B := B) f

/-- The complete original native loop-group inversion is its own genuine natural inverse. -/
def loopGroupInversionNatIso (k : ℕ) :
    PointedCGWH.loop.{u, v} ⋙ piNPositiveFunctor k ≅
      PointedCGWH.loop ⋙ piNPositiveFunctor k where
  hom := loopGroupInversionNatTrans k
  inv := loopGroupInversionNatTrans k
  hom_inv_id := by
    ext A a
    change a⁻¹⁻¹ = a
    exact inv_inv a
  inv_hom_id := by
    ext A a
    change a⁻¹⁻¹ = a
    exact inv_inv a

/-- The complete original double-loop swap is that same actual inversion homomorphism. -/
theorem interchange_piNPositiveMap (k : ℕ) (A : PointedCGWH.{u, v}) :
    piNPositiveMap k (interchange A) = loopGroupInversion k (PointedCGWH.loop.obj A) := by
  ext a
  exact interchange_piNPositiveMap_eq_inv k A a

end PointedCGWH.DoubleLoopInterchangeGeometry
