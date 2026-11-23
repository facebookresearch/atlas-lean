/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberHomotopySquare
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberRestriction

/-!
# Original homotopy pullbacks through the actual mapping-path replacement

The original homotopy-pullback point and whole target path determine a
point of the SAME mapping-path replacement. Its universal property earns
the actual pullback over the right base. The original mapping-path endpoint
fibration therefore gives both projection fibrancy and weakness of the
actual fiber restriction map, for every original base point.

The original mapping-path inclusion and both whole inverse families earn
the other comparison on homotopy fibers. No base-map weakness, projection
fibrancy, fiber equivalence or pullback-comparison outcome is supplied.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology HomotopicalAlgebra
open scoped TopCat.modelCategory

universe u

namespace TopCat.HomotopyPullbackMappingPath

variable {E W B : TopCat.{u}} (p : E ⟶ B) (h : W ⟶ B)

private def lift {T : TopCat.{u}} (l : T ⟶ E) (r : T ⟶ W)
    (γ : T ⟶ pathObject B)
    (h₀ : γ ≫ pathEvalZero B = l ≫ p) (h₁ : γ ≫ pathEvalOne B = r ≫ h) :
    T ⟶ homotopyPullback p h :=
  pullback.lift (prod.lift l r) γ (by
    apply prod.hom_ext
    · calc
        _ = (prod.lift l r ≫ prod.fst) ≫ p := by
          rw [Category.assoc, prod.map_fst, ← Category.assoc]
        _ = l ≫ p := congrArg (fun f => f ≫ p) (prod.lift_fst l r)
        _ = γ ≫ pathEvalZero B := h₀.symm
        _ = _ := by simp only [pathEndpoints, Category.assoc, prod.lift_fst]
    · calc
        _ = (prod.lift l r ≫ prod.snd) ≫ h := by
          rw [Category.assoc, prod.map_snd, ← Category.assoc]
        _ = r ≫ h := congrArg (fun f => f ≫ h) (prod.lift_snd l r)
        _ = γ ≫ pathEvalOne B := h₁.symm
        _ = _ := by simp only [pathEndpoints, Category.assoc, prod.lift_snd])

private theorem lift_left {T : TopCat.{u}} (l : T ⟶ E) (r : T ⟶ W)
    (γ : T ⟶ pathObject B)
    (h₀ : γ ≫ pathEvalZero B = l ≫ p) (h₁ : γ ≫ pathEvalOne B = r ≫ h) :
    lift p h l r γ h₀ h₁ ≫ homotopyPullbackLeft p h = l := by
  rw [lift, homotopyPullbackLeft, ← Category.assoc, pullback.lift_fst, prod.lift_fst]

private theorem lift_right {T : TopCat.{u}} (l : T ⟶ E) (r : T ⟶ W)
    (γ : T ⟶ pathObject B)
    (h₀ : γ ≫ pathEvalZero B = l ≫ p) (h₁ : γ ≫ pathEvalOne B = r ≫ h) :
    lift p h l r γ h₀ h₁ ≫ homotopyPullbackRight p h = r := by
  rw [lift, homotopyPullbackRight, ← Category.assoc, pullback.lift_fst, prod.lift_snd]

private theorem lift_path {T : TopCat.{u}} (l : T ⟶ E) (r : T ⟶ W)
    (γ : T ⟶ pathObject B)
    (h₀ : γ ≫ pathEvalZero B = l ≫ p) (h₁ : γ ≫ pathEvalOne B = r ≫ h) :
    lift p h l r γ h₀ h₁ ≫ homotopyPullbackPath p h = γ := by
  rw [lift, homotopyPullbackPath, pullback.lift_snd]

/-- The actual whole left point and whole carried path lift to the SAME original mapping path. -/
def toReplacement : homotopyPullback p h ⟶ (mappingPathReplacement p).space :=
  (mappingPathReplacement_isPullback p).lift (homotopyPullbackLeft p h)
    (homotopyPullbackPath p h) (homotopyPullbackPath_evalZero p h).symm

/-- The entire original source point is retained by the replacement map. -/
theorem toReplacement_toSource :
    toReplacement p h ≫ (mappingPathReplacement p).toSource = homotopyPullbackLeft p h :=
  (mappingPathReplacement_isPullback p).lift_fst _ _ _

/-- The entire original carried target curve is retained by the replacement map. -/
theorem toReplacement_path :
    toReplacement p h ≫ (mappingPathReplacement p).pathMap = homotopyPullbackPath p h :=
  (mappingPathReplacement_isPullback p).lift_snd _ _ _

/-- The endpoint of the original carried path is the actual image of the original right point. -/
theorem toReplacement_toBase :
    toReplacement p h ≫ (mappingPathReplacement p).toBase = homotopyPullbackRight p h ≫ h := by
  calc
    _ = toReplacement p h ≫ (mappingPathReplacement p).pathMap ≫ pathEvalOne B :=
      congrArg (fun f => toReplacement p h ≫ f) (mappingPathReplacement p).pathOne.symm
    _ = homotopyPullbackPath p h ≫ pathEvalOne B := by
      rw [← Category.assoc, toReplacement_path]
    _ = _ := homotopyPullbackPath_evalOne p h

/-- The whole original homotopy pullback is the actual pullback of
the SAME earned mapping-path endpoint fibration along the arbitrary base map. -/
theorem isPullback :
    IsPullback (toReplacement p h) (homotopyPullbackRight p h)
      (mappingPathReplacement p).toBase h := by
  let m := mappingPathReplacement p
  let hP := mappingPathReplacement_isPullback p
  let comm := toReplacement_toBase p h
  apply IsPullback.of_isLimit' (CommSq.mk comm)
  apply PullbackCone.IsLimit.mk comm
    (fun c => lift p h (c.fst ≫ m.toSource) c.snd (c.fst ≫ m.pathMap)
      (by rw [Category.assoc, m.pathZero, ← Category.assoc])
      (by rw [Category.assoc, m.pathOne, c.condition]))
  · intro c
    apply hP.hom_ext
    · rw [Category.assoc, toReplacement_toSource, lift_left]
    · rw [Category.assoc, toReplacement_path, lift_path]
  · intro c
    exact lift_right p h _ _ _ _ _
  · intro c z hz₀ hz₁
    apply homotopyPullback_hom_ext
    · calc
        _ = (z ≫ toReplacement p h) ≫ m.toSource := by
          rw [Category.assoc, toReplacement_toSource]
        _ = c.fst ≫ m.toSource := congrArg (fun f => f ≫ m.toSource) hz₀
        _ = _ := (lift_left p h _ _ _ _ _).symm
    · exact hz₁.trans (lift_right p h _ _ _ _ _).symm
    · calc
        _ = (z ≫ toReplacement p h) ≫ m.pathMap := by
          rw [Category.assoc, toReplacement_path]
        _ = c.fst ≫ m.pathMap := congrArg (fun f => f ≫ m.pathMap) hz₀
        _ = _ := (lift_path p h _ _ _ _ _).symm

/-- Fibrancy of the actual right projection is earned from the original
mapping-path fibration and the original pullback universal property. -/
theorem rightProjection_fibration : Fibration (homotopyPullbackRight p h) := by
  let m := mappingPathReplacement p
  let _ : Fibration m.toBase := m.projectionFibration
  apply (fibration_iff _).mpr
  exact MorphismProperty.of_isPullback (isPullback p h) ((fibration_iff _).mp m.projectionFibration)

/-- The SAME actual map of projection fibers is weak at every original
point; no weakness of the arbitrary base map is supplied. -/
theorem fiberMap_mem_weakHomotopyEquivalences (w : W) :
    weakHomotopyEquivalences
      (homotopyFiberMapOfSquare (toReplacement p h) h (toReplacement_toBase p h).symm w) := by
  let m := mappingPathReplacement p
  let _ : Fibration m.toBase := m.projectionFibration
  let _ : Fibration (homotopyPullbackRight p h) := rightProjection_fibration p h
  exact homotopyFiberMapOfSquare_mem_of_isPullback_comparisons (isPullback p h) w
    (strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences (homotopyPullbackRight p h) w)
    (strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences m.toBase (h w))

/-- The actual original mapping-path inclusion keeps its original
source projection inverse and both complete old inverse families. -/
def inclusionEquiv : ContinuousMap.HomotopyEquiv E (mappingPathReplacement p).space where
  toFun := (mappingPathReplacement p).inclusion.hom
  invFun := (mappingPathReplacement p).toSource.hom
  left_inv := ⟨(mappingPathReplacement p).sourceInverseHomotopy⟩
  right_inv := ⟨(mappingPathReplacement p).sourceHomotopy⟩

/-- The exact old mapping-path inclusion is weak, with both full inverse families earned. -/
theorem inclusion_mem_weakHomotopyEquivalences :
    weakHomotopyEquivalences (mappingPathReplacement p).inclusion :=
  homotopyEquiv_toFun_mem (inclusionEquiv p)

/-- The exact old mapping-path inclusion induces a weak map of the
actual homotopy fibers over every point of the SAME identity base. -/
theorem inclusionFiberMap_mem_weakHomotopyEquivalences (b : B) :
    weakHomotopyEquivalences
      (homotopyFiberMapOfSquare (p := p) (q := (mappingPathReplacement p).toBase)
        (mappingPathReplacement p).inclusion (𝟙 B)
        (by simpa only [Category.comp_id] using
          (mappingPathReplacement p).inclusionToBase.symm) b) :=
  homotopyFiberMapOfSquare_mem_weakHomotopyEquivalences _ _ _ _
    (inclusion_mem_weakHomotopyEquivalences p) (weakHomotopyEquivalences.id_mem B)

end TopCat.HomotopyPullbackMappingPath

end
