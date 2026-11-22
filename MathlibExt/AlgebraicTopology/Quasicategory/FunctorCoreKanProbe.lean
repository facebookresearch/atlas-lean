/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Quasicategory.FunctorCoreKanSourceIso
import MathlibExt.AlgebraicTopology.Quasicategory.FunctorCoreHomotopyInvariance

/-!
# The actual functor core tested by Kan coefficients

The simplicial domain A remains arbitrary. A genuine Kan coefficient K
permits the original curry to land in the SAME equivalence-edge core.
The inverse uses its original inclusion and exponential counit. These are
mutually inverse on all maps, natural in both objects and the coefficient.
No Kan condition is imposed on A.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u

open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial

namespace SSet.FunctorCore

/-- Two consecutive actual changes retain the original contravariant source order. -/
theorem mapBoth_comp {A B C X Y Z : SSet.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    mapBoth b f ≫ mapBoth a g = mapBoth (a ≫ b) (f ≫ g) := by
  simp only [mapBoth]
  have hc := NatTrans.congr_app (sourceMap_comp a b) X
  simp only [NatTrans.comp_app] at hc
  rw [Category.assoc, (sourceMap a).naturality_assoc f]
  simpa only [Category.assoc, Functor.map_comp] using
    congrArg (fun h => h ≫ (functor A).map (f ≫ g)) hc.symm

/-- The simultaneous change retains both actual whole-map legs under the core inclusion. -/
@[reassoc]
theorem mapBoth_inclusion {A B X Y : SSet.{u}} (a : A ⟶ B) (f : X ⟶ Y) :
    mapBoth a f ≫ (core ((ihom A).obj Y)).ι =
      (core ((ihom B).obj X)).ι ≫ (pre a).app X ≫ (ihom A).map f := by
  rw [mapBoth, Category.assoc, map_inclusion, ← Category.assoc, sourceMap_inclusion]
  exact Category.assoc _ _ _

/-- Actual source restriction preserves each original simplicial functor as its own vertex. -/
theorem sourceMap_vertex {A B X : SSet.{u}} (a : A ⟶ B) (f : B ⟶ X) :
    ((sourceMap a).app X).app (op ⦋0⦌) (vertex f) = vertex (a ≫ f) := by
  apply Subtype.ext
  change ((pre a).app X).app (op ⦋0⦌) (ihomVertexEquiv B X f) =
    ihomVertexEquiv A X (a ≫ f)
  exact ihomVertexEquiv_pre_app a f

/-- Both original maps act on the SAME individual simplicial functor. -/
theorem mapBoth_vertex {A B X Y : SSet.{u}} (a : A ⟶ B) (f : B ⟶ X) (g : X ⟶ Y) :
    (mapBoth a g).app (op ⦋0⦌) (vertex f) = vertex (a ≫ f ≫ g) := by
  change ((functor A).map g).app (op ⦋0⦌)
    (((sourceMap a).app X).app (op ⦋0⦌) (vertex f)) = _
  rw [sourceMap_vertex, map_vertex]
  rw [Category.assoc]

namespace KanProbe

variable (A K Q : SSet.{u}) [KanComplex K]

/-- The original curry lands in the actual core because its coefficient is genuinely Kan. -/
def curryToCore (f : A ⊗ K ⟶ Q) : K ⟶ (FunctorCore.functor A).obj Q :=
  Subcomplex.lift (curry f) (KanSource.range_le_core (curry f))

/-- The forward map keeps the SAME ordinary curry under the SAME core inclusion. -/
@[reassoc]
theorem curryToCore_inclusion (f : A ⊗ K ⟶ Q) :
    curryToCore A K Q f ≫ (core ((ihom A).obj Q)).ι = curry f :=
  Subcomplex.lift_ι _ _

/-- Evaluation is the original exponential counit after the literal core inclusion. -/
def uncurryFromCore (f : K ⟶ (FunctorCore.functor A).obj Q) : A ⊗ K ⟶ Q :=
  A ◁ f ≫ FunctorCore.evaluation A Q

omit [KanComplex K] in
/-- The inverse retains the ordinary uncurrying of that SAME full core inclusion. -/
theorem uncurryFromCore_eq (f : K ⟶ (FunctorCore.functor A).obj Q) :
    uncurryFromCore A K Q f = uncurry (f ≫ (core ((ihom A).obj Q)).ι) := by
  simp only [uncurryFromCore, FunctorCore.evaluation, uncurry_eq, whiskerLeft_comp,
    Category.assoc]

/-- The actual product/Hom maps are a bijection for every Kan coefficient and arbitrary A. -/
def homEquiv : (A ⊗ K ⟶ Q) ≃ (K ⟶ (FunctorCore.functor A).obj Q) where
  toFun := curryToCore A K Q
  invFun := uncurryFromCore A K Q
  left_inv f := by
    rw [uncurryFromCore_eq, curryToCore_inclusion, uncurry_curry]
  right_inv f := by
    apply (cancel_mono (core ((ihom A).obj Q)).ι).mp
    rw [curryToCore_inclusion, uncurryFromCore_eq, curry_uncurry]

/-- The core evaluator recovers every original tensor map, including noninvertible A edges. -/
theorem homEquiv_evaluation (f : A ⊗ K ⟶ Q) :
    A ◁ homEquiv A K Q f ≫ FunctorCore.evaluation A Q = f :=
  (homEquiv A K Q).symm_apply_apply f

/-- Naturality in the target keeps the actual internal postcomposition/core map. -/
theorem homEquiv_target {Q' : SSet.{u}} (f : A ⊗ K ⟶ Q) (g : Q ⟶ Q') :
    homEquiv A K Q (f) ≫ (FunctorCore.functor A).map g =
      homEquiv A K Q' (f ≫ g) := by
  change curryToCore A K Q f ≫ (FunctorCore.functor A).map g = curryToCore A K Q' (f ≫ g)
  apply (cancel_mono (core ((ihom A).obj Q')).ι).mp
  rw [Category.assoc, FunctorCore.map_inclusion, ← Category.assoc,
    curryToCore_inclusion, curryToCore_inclusion, curry_natural_right]

/-- Naturality in arbitrary source maps keeps actual internal precomposition. -/
theorem homEquiv_source {B : SSet.{u}} (a : B ⟶ A) (f : A ⊗ K ⟶ Q) :
    homEquiv A K Q f ≫ (FunctorCore.sourceMap a).app Q =
      homEquiv B K Q (a ▷ K ≫ f) := by
  change curryToCore A K Q f ≫ (FunctorCore.sourceMap a).app Q =
    curryToCore B K Q (a ▷ K ≫ f)
  apply (cancel_mono (core ((ihom B).obj Q)).ι).mp
  rw [Category.assoc, FunctorCore.sourceMap_inclusion, ← Category.assoc,
    curryToCore_inclusion, curryToCore_inclusion, curry_pre_app]

/-- Every actual map of Kan coefficients retains the entire original scalar parameter. -/
theorem homEquiv_coefficient {L : SSet.{u}} [KanComplex L] (a : L ⟶ K)
    (f : A ⊗ K ⟶ Q) :
    a ≫ homEquiv A K Q f = homEquiv A L Q (A ◁ a ≫ f) := by
  change a ≫ curryToCore A K Q f = curryToCore A L Q (A ◁ a ≫ f)
  apply (cancel_mono (core ((ihom A).obj Q)).ι).mp
  rw [Category.assoc, curryToCore_inclusion, curryToCore_inclusion, curry_natural_left]

end KanProbe
end SSet.FunctorCore
