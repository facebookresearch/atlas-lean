/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.PathObject
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Based good paths and their actual loop fibres

The based path object is the pullback of the first endpoint of the supplied
good path along the caller's original zero map. Its projection to the second
endpoint is a fibration, while its projection to the same zero object is a
trivial fibration. The fibre of that projection is the pullback of both
original path endpoints along the original pair of zero maps.

All comparisons use the full limiting cones. Their maps retain both original
endpoint projections and every map of path objects. These constructions do
not use a properness hypothesis or a replacement of the caller's zero object.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.OriginalGoodPathFiberGeometry

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (Z : C) (hZ : IsZero Z) {Y : C} (P : PathObject Y)

/-- The actual based path object retains the caller's zero and the first original endpoint. -/
abbrev basedPath : C := pullback P.p₀ (hZ.isInitial.to Y)

/-- The full original based path projection to the supplied path object. -/
def pathLeg : basedPath Z hZ P ⟶ P.P := pullback.fst _ _

/-- The full based path projection to the same caller zero object. -/
def collapse : basedPath Z hZ P ⟶ Z := pullback.snd _ _

/-- The actual based path fibration is the second original path endpoint. -/
def projection : basedPath Z hZ P ⟶ Y := pathLeg Z hZ P ≫ P.p₁

/-- Every based path retains the complete first endpoint equation. -/
@[reassoc (attr := simp)]
theorem pathLeg_first :
    pathLeg Z hZ P ≫ P.p₀ = collapse Z hZ P ≫ hZ.isInitial.to Y :=
  pullback.condition

/-- The zero-to-based-path map is the actual constant path at the original zero. -/
def zeroInsertion : Z ⟶ basedPath Z hZ P :=
  pullback.lift (hZ.isInitial.to Y ≫ P.ι) (𝟙 Z) (by simp)

/-- The original zero insertion reads back the entire constant path. -/
@[reassoc (attr := simp)]
theorem zeroInsertion_pathLeg :
    zeroInsertion Z hZ P ≫ pathLeg Z hZ P = hZ.isInitial.to Y ≫ P.ι :=
  pullback.lift_fst _ _ _

/-- The original zero insertion reads back the same zero identity. -/
@[reassoc (attr := simp)]
theorem zeroInsertion_collapse :
    zeroInsertion Z hZ P ≫ collapse Z hZ P = 𝟙 Z :=
  pullback.lift_snd _ _ _

/-- The full second endpoint of the constant path is the original zero map. -/
@[reassoc (attr := simp)]
theorem zeroInsertion_projection :
    zeroInsertion Z hZ P ≫ projection Z hZ P = hZ.isInitial.to Y := by
  simp [projection]

/-- Both original endpoints are retained in the actual based-point inclusion. -/
def basedEndpoint (X : C) : X ⟶ X ⨯ X :=
  prod.lift (hZ.isTerminal.from X ≫ hZ.isInitial.to X) (𝟙 X)

/-- The entire based path square retains both original path projections. -/
theorem basedPath_pair_condition :
    pathLeg Z hZ P ≫ P.p = projection Z hZ P ≫ basedEndpoint Z hZ Y := by
  apply prod.hom_ext
  · simp only [Category.assoc, PrepathObject.p_fst, basedEndpoint, prod.lift_fst]
    rw [pathLeg_first]
    simpa only [Category.assoc] using
      congrArg (fun q : basedPath Z hZ P ⟶ Z => q ≫ hZ.isInitial.to Y)
        (hZ.isTerminal.hom_ext (collapse Z hZ P)
          (projection Z hZ P ≫ hZ.isTerminal.from Y))
  · simp [projection, basedEndpoint]

/-- The full based path square is a pullback of the actual two-end path map. -/
def basedPathPairIsLimit :
    IsLimit (PullbackCone.mk (pathLeg Z hZ P) (projection Z hZ P)
      (basedPath_pair_condition Z hZ P)) := by
  let lift : ∀ s : PullbackCone P.p (basedEndpoint Z hZ Y), s.pt ⟶ basedPath Z hZ P :=
    fun s => pullback.lift s.fst (s.snd ≫ hZ.isTerminal.from Y) (by
      have h := congrArg (fun f => f ≫ prod.fst) s.condition
      simpa only [Category.assoc, PrepathObject.p_fst, basedEndpoint, prod.lift_fst] using h)
  refine PullbackCone.IsLimit.mk _ lift ?_ ?_ ?_
  · intro s
    exact pullback.lift_fst _ _ _
  · intro s
    change lift s ≫ pathLeg Z hZ P ≫ P.p₁ = s.snd
    rw [← Category.assoc, show lift s ≫ pathLeg Z hZ P = s.fst from pullback.lift_fst _ _ _]
    have h := congrArg (fun f => f ≫ prod.snd) s.condition
    simpa only [Category.assoc, PrepathObject.p_snd, basedEndpoint, prod.lift_snd,
      Category.comp_id] using h
  · intro s m h₁ _h₂
    apply pullback.hom_ext
    · exact h₁.trans (pullback.lift_fst _ _ _).symm
    · exact hZ.isTerminal.hom_ext _ _

/-- The actual entire based path pullback square. -/
theorem basedPath_isPullback :
    IsPullback (pathLeg Z hZ P) (projection Z hZ P) P.p (basedEndpoint Z hZ Y) :=
  IsPullback.of_isLimit (basedPathPairIsLimit Z hZ P)

variable [IsFibrant Y] [P.IsGood]

omit [IsFibrant Y] in
/-- The actual second endpoint is a fibration by base change of the full good path. -/
theorem projection_fibration : Fibration (projection Z hZ P) := by
  rw [fibration_iff]
  exact (fibrations C).of_isPullback (basedPath_isPullback Z hZ P)
    ((fibration_iff _).mp inferInstance)

/-- The collapse to the same original zero is a fibration by its actual first-end pullback. -/
theorem collapse_fibration : Fibration (collapse Z hZ P) := by
  change Fibration (pullback.snd P.p₀ (hZ.isInitial.to Y))
  infer_instance

/-- The collapse is weak by base change of the original endpoint's trivial fibration. -/
theorem collapse_weak : WeakEquivalence (collapse Z hZ P) := by
  change WeakEquivalence (pullback.snd P.p₀ (hZ.isInitial.to Y))
  infer_instance

/-- The full based path collapse lies in the actual original trivial-fibration class. -/
theorem collapse_trivialFibration : trivialFibrations C (collapse Z hZ P) := by
  let : Fibration (collapse Z hZ P) := collapse_fibration Z hZ P
  let : WeakEquivalence (collapse Z hZ P) := collapse_weak Z hZ P
  exact mem_trivialFibrations _

/-- The original constant zero path is weak by the actual collapse retraction. -/
theorem zeroInsertion_weak : WeakEquivalence (zeroInsertion Z hZ P) := by
  let : WeakEquivalence (collapse Z hZ P) := collapse_weak Z hZ P
  exact weakEquivalence_of_postcomp_of_fac (zeroInsertion_collapse Z hZ P)

/-- The same based path object is fibrant by its full original endpoint fibration. -/
theorem basedPath_isFibrant : IsFibrant (basedPath Z hZ P) := by
  let : Fibration (projection Z hZ P) := projection_fibration Z hZ P
  exact isFibrant_of_fibration (projection Z hZ P)

end HomotopicalAlgebra.OriginalGoodPathFiberGeometry

namespace HomotopicalAlgebra.OriginalGoodPathFiberGeometry

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (Z : C) (hZ : IsZero Z) {Y : C} (P : PathObject Y)

/-- The original pair of zero endpoint maps, with its actual caller source. -/
def zeroPair (X : C) : Z ⟶ X ⨯ X := prod.lift (hZ.isInitial.to X) (hZ.isInitial.to X)

/-- The full ordinary path fibre retains both original endpoints and the original zero pair. -/
abbrev pathFiber : C := pullback P.p (zeroPair Z hZ Y)

/-- The fibre of the actual based path projection retains that same caller zero. -/
abbrev basedFiber : C := pullback (projection Z hZ P) (hZ.isInitial.to Y)

/-- The full based fibre projection reads back both original path endpoints. -/
theorem basedFiber_pair_condition :
    (pullback.fst (projection Z hZ P) (hZ.isInitial.to Y) ≫ pathLeg Z hZ P) ≫ P.p =
      pullback.snd (projection Z hZ P) (hZ.isInitial.to Y) ≫ zeroPair Z hZ Y := by
  apply prod.hom_ext
  · simp only [Category.assoc, PrepathObject.p_fst, zeroPair, prod.lift_fst]
    rw [pathLeg_first]
    rw [← Category.assoc]
    congr 1
    exact hZ.isTerminal.hom_ext _ _
  · simpa only [Category.assoc, PrepathObject.p_snd, zeroPair, prod.lift_snd,
      projection] using
      (pullback.condition (f := projection Z hZ P) (g := hZ.isInitial.to Y))

/-- The entire iterated fibre is a limiting cone on the original full path map. -/
def basedFiberPathIsLimit :
    IsLimit (PullbackCone.mk
      (pullback.fst (projection Z hZ P) (hZ.isInitial.to Y) ≫ pathLeg Z hZ P)
      (pullback.snd (projection Z hZ P) (hZ.isInitial.to Y))
      (basedFiber_pair_condition Z hZ P)) := by
  let inner : ∀ s : PullbackCone P.p (zeroPair Z hZ Y), s.pt ⟶ basedPath Z hZ P :=
    fun s => pullback.lift s.fst s.snd (by
      have h := congrArg (fun f => f ≫ prod.fst) s.condition
      simpa only [Category.assoc, PrepathObject.p_fst, zeroPair, prod.lift_fst] using h)
  let lift : ∀ s : PullbackCone P.p (zeroPair Z hZ Y), s.pt ⟶ basedFiber Z hZ P :=
    fun s => pullback.lift (inner s) s.snd (by
      change inner s ≫ pathLeg Z hZ P ≫ P.p₁ = s.snd ≫ hZ.isInitial.to Y
      rw [← Category.assoc, show inner s ≫ pathLeg Z hZ P = s.fst from pullback.lift_fst _ _ _]
      have h := congrArg (fun f => f ≫ prod.snd) s.condition
      simpa only [Category.assoc, PrepathObject.p_snd, zeroPair, prod.lift_snd] using h)
  refine PullbackCone.IsLimit.mk _ lift ?_ ?_ ?_
  · intro s
    change lift s ≫ pullback.fst _ _ ≫ pathLeg Z hZ P = s.fst
    rw [← Category.assoc, show lift s ≫ pullback.fst _ _ = inner s from pullback.lift_fst _ _ _]
    exact pullback.lift_fst _ _ _
  · intro s
    exact pullback.lift_snd _ _ _
  · intro s m h₁ h₂
    apply pullback.hom_ext
    · rw [show lift s ≫ pullback.fst _ _ = inner s from pullback.lift_fst _ _ _]
      apply pullback.hom_ext
      · simpa only [pathLeg, Category.assoc] using h₁.trans
          (show inner s ≫ pathLeg Z hZ P = s.fst from pullback.lift_fst _ _ _).symm
      · exact hZ.isTerminal.hom_ext _ _
    · exact h₂.trans (pullback.lift_snd _ _ _).symm

/-- The whole original iterated fibre is isomorphic to the full original path fibre. -/
def basedFiberIsoPathFiber : basedFiber Z hZ P ≅ pathFiber Z hZ P :=
  (basedFiberPathIsLimit Z hZ P).conePointUniqueUpToIso (pullback.isLimit _ _)

/-- The complete isomorphism retains the actual original path projection. -/
@[reassoc (attr := simp)]
theorem basedFiberIsoPathFiber_fst :
    (basedFiberIsoPathFiber Z hZ P).hom ≫ pullback.fst P.p (zeroPair Z hZ Y) =
      pullback.fst (projection Z hZ P) (hZ.isInitial.to Y) ≫ pathLeg Z hZ P :=
  IsLimit.conePointUniqueUpToIso_hom_comp (basedFiberPathIsLimit Z hZ P)
    (pullback.isLimit _ _) WalkingCospan.left

/-- The complete isomorphism retains the same original zero projection. -/
@[reassoc (attr := simp)]
theorem basedFiberIsoPathFiber_snd :
    (basedFiberIsoPathFiber Z hZ P).hom ≫ pullback.snd P.p (zeroPair Z hZ Y) =
      pullback.snd (projection Z hZ P) (hZ.isInitial.to Y) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (basedFiberPathIsLimit Z hZ P)
    (pullback.isLimit _ _) WalkingCospan.right

variable {Y' : C} (P' : PathObject Y') (f : Y ⟶ Y') (a : P.P ⟶ P'.P)
  (h₀ : a ≫ P'.p₀ = P.p₀ ≫ f) (h₁ : a ≫ P'.p₁ = P.p₁ ≫ f)

/-- Every actual map of both path endpoints gives the entire based path map. -/
def basedPathMap : basedPath Z hZ P ⟶ basedPath Z hZ P' :=
  pullback.map P.p₀ (hZ.isInitial.to Y) P'.p₀ (hZ.isInitial.to Y')
    a (𝟙 Z) f h₀.symm (hZ.isInitial.hom_ext _ _)

/-- The full based path map retains the original supplied path-object map. -/
@[reassoc (attr := simp)]
theorem basedPathMap_pathLeg :
    basedPathMap Z hZ P P' f a h₀ ≫ pathLeg Z hZ P' = pathLeg Z hZ P ≫ a :=
  pullback.lift_fst _ _ _

/-- The full based path map retains the same zero projection. -/
@[reassoc (attr := simp)]
theorem basedPathMap_collapse :
    basedPathMap Z hZ P P' f a h₀ ≫ collapse Z hZ P' = collapse Z hZ P := by
  simpa only [Category.comp_id] using
    (show basedPathMap Z hZ P P' f a h₀ ≫ collapse Z hZ P' =
      collapse Z hZ P ≫ 𝟙 Z from pullback.lift_snd _ _ _)

include h₁ in
/-- The actual full based path map retains the second original endpoint square. -/
@[reassoc (attr := simp)]
theorem basedPathMap_projection :
    basedPathMap Z hZ P P' f a h₀ ≫ projection Z hZ P' = projection Z hZ P ≫ f := by
  simp only [projection, ← Category.assoc, basedPathMap_pathLeg]
  rw [Category.assoc, h₁, ← Category.assoc]

/-- Every original based zero insertion is retained by the complete based path map. -/
theorem zeroInsertion_basedPathMap :
    zeroInsertion Z hZ P ≫ basedPathMap Z hZ P P' f a h₀ = zeroInsertion Z hZ P' :=
  hZ.isInitial.hom_ext _ _

include h₀ h₁ in
/-- Both original endpoint-map squares give the complete full-path map. -/
theorem pathMap_pair_condition :
    a ≫ P'.p = P.p ≫ prod.map f f := by
  apply prod.hom_ext <;> simp [h₀, h₁]

/-- The entire original path-fibre map retains both endpoint maps and the original zero identity. -/
def pathFiberMap : pathFiber Z hZ P ⟶ pathFiber Z hZ P' :=
  pullback.map P.p (zeroPair Z hZ Y) P'.p (zeroPair Z hZ Y')
    a (𝟙 Z) (prod.map f f) (pathMap_pair_condition P P' f a h₀ h₁).symm (hZ.isInitial.hom_ext _ _)

/-- The full based-fibre map retains the original based path and zero maps. -/
def basedFiberMap : basedFiber Z hZ P ⟶ basedFiber Z hZ P' :=
  pullback.map (projection Z hZ P) (hZ.isInitial.to Y)
    (projection Z hZ P') (hZ.isInitial.to Y')
    (basedPathMap Z hZ P P' f a h₀) (𝟙 Z) f
    (basedPathMap_projection Z hZ P P' f a h₀ h₁).symm (hZ.isInitial.hom_ext _ _)

/-- The full actual loop-fibre isomorphism retains every supplied map of both path endpoints. -/
theorem basedFiberIsoPathFiber_naturality :
    basedFiberMap Z hZ P P' f a h₀ h₁ ≫ (basedFiberIsoPathFiber Z hZ P').hom =
      (basedFiberIsoPathFiber Z hZ P).hom ≫ pathFiberMap Z hZ P P' f a h₀ h₁ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, basedFiberIsoPathFiber_fst]
    rw [← Category.assoc]
    rw [show basedFiberMap Z hZ P P' f a h₀ h₁ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ basedPathMap Z hZ P P' f a h₀ from pullback.lift_fst _ _ _]
    rw [Category.assoc, basedPathMap_pathLeg, ← Category.assoc]
    rw [← basedFiberIsoPathFiber_fst, Category.assoc]
    rw [show pathFiberMap Z hZ P P' f a h₀ h₁ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ a from pullback.lift_fst _ _ _]
  · simp only [Category.assoc, basedFiberIsoPathFiber_snd]
    rw [show basedFiberMap Z hZ P P' f a h₀ h₁ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ 𝟙 Z from pullback.lift_snd _ _ _]
    rw [show pathFiberMap Z hZ P P' f a h₀ h₁ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ 𝟙 Z from pullback.lift_snd _ _ _]
    simp

end HomotopicalAlgebra.OriginalGoodPathFiberGeometry
