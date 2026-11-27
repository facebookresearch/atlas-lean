/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.Topology.CompactOpen

/-!
# Compact-open homotopy pullbacks in `TopCat`

This file defines the compact-open path object, its endpoint maps, functorial homotopy pullbacks,
and homotopy fibers. A path in `homotopyPullback f g` is oriented from `f x` at time zero to `g y`
at time one.

It makes no fibration, quasifibration, weak-equivalence, loop-space, bar, `EG`, `BG`, or connecting-
map claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Topology

universe u

namespace TopCat

/-- The compact-open path object of a topological space. -/
abbrev pathObject (B : TopCat.{u}) : TopCat.{u} :=
  TopCat.of C(TopCat.I.{u}, B)

/-- Evaluation of a path at time zero. -/
def pathEvalZero (B : TopCat.{u}) : pathObject B ⟶ B :=
  TopCat.ofHom ⟨fun γ => γ 0, continuous_eval_const 0⟩

/-- Evaluation of a path at time one. -/
def pathEvalOne (B : TopCat.{u}) : pathObject B ⟶ B :=
  TopCat.ofHom ⟨fun γ => γ 1, continuous_eval_const 1⟩

/-- The pair of endpoint evaluations. -/
def pathEndpoints (B : TopCat.{u}) : pathObject B ⟶ B ⨯ B :=
  Limits.prod.lift (pathEvalZero B) (pathEvalOne B)

/-- Postcomposition maps compact-open path objects. -/
def pathObjectMap {B B' : TopCat.{u}} (h : B ⟶ B') :
    pathObject B ⟶ pathObject B' :=
  TopCat.ofHom ⟨fun γ => h.hom.comp γ,
    ContinuousMap.continuous_postcomp h.hom⟩

@[reassoc (attr := simp)]
theorem pathObjectMap_evalZero {B B' : TopCat.{u}} (h : B ⟶ B') :
    pathObjectMap h ≫ pathEvalZero B' = pathEvalZero B ≫ h := by
  ext γ
  rfl

@[reassoc (attr := simp)]
theorem pathObjectMap_evalOne {B B' : TopCat.{u}} (h : B ⟶ B') :
    pathObjectMap h ≫ pathEvalOne B' = pathEvalOne B ≫ h := by
  ext γ
  rfl

@[reassoc]
theorem pathObjectMap_endpoints {B B' : TopCat.{u}} (h : B ⟶ B') :
    pathObjectMap h ≫ pathEndpoints B' =
      pathEndpoints B ≫ Limits.prod.map h h := by
  apply Limits.prod.hom_ext
  · simp [pathEndpoints]
  · simp [pathEndpoints]

@[simp]
theorem pathObjectMap_id (B : TopCat.{u}) :
    pathObjectMap (𝟙 B) = 𝟙 (pathObject B) := by
  ext γ t
  rfl

@[simp]
theorem pathObjectMap_comp {B B' B'' : TopCat.{u}}
    (h : B ⟶ B') (h' : B' ⟶ B'') :
    pathObjectMap (h ≫ h') = pathObjectMap h ≫ pathObjectMap h' := by
  ext γ t
  rfl

/-- Compact-open homotopy pullback, with paths oriented from `f x` to `g y`. -/
abbrev homotopyPullback {X Y B : TopCat.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
    TopCat.{u} :=
  pullback (Limits.prod.map f g) (pathEndpoints B)

/-- Projection of a homotopy pullback to its left input. -/
abbrev homotopyPullbackLeft {X Y B : TopCat.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
    homotopyPullback f g ⟶ X :=
  pullback.fst (Limits.prod.map f g) (pathEndpoints B) ≫ Limits.prod.fst

/-- Projection of a homotopy pullback to its right input. -/
abbrev homotopyPullbackRight {X Y B : TopCat.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
    homotopyPullback f g ⟶ Y :=
  pullback.fst (Limits.prod.map f g) (pathEndpoints B) ≫ Limits.prod.snd

/-- Path projection of a homotopy pullback. -/
abbrev homotopyPullbackPath {X Y B : TopCat.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
    homotopyPullback f g ⟶ pathObject B :=
  pullback.snd (Limits.prod.map f g) (pathEndpoints B)

/-- The path starts at the image of the left projection. -/
@[reassoc]
theorem homotopyPullbackPath_evalZero {X Y B : TopCat.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) :
    homotopyPullbackPath f g ≫ pathEvalZero B =
      homotopyPullbackLeft f g ≫ f := by
  have h :
      pullback.fst (Limits.prod.map f g) (pathEndpoints B) ≫
          Limits.prod.map f g =
        pullback.snd (Limits.prod.map f g) (pathEndpoints B) ≫
          pathEndpoints B :=
    pullback.condition
  have hzero := congrArg
    (fun k => k ≫ (Limits.prod.fst : B ⨯ B ⟶ B)) h
  change pullback.snd (Limits.prod.map f g) (pathEndpoints B) ≫
      pathEvalZero B =
    (pullback.fst (Limits.prod.map f g) (pathEndpoints B) ≫
      Limits.prod.fst) ≫ f
  simpa [pathEndpoints, Category.assoc] using hzero.symm

/-- The path ends at the image of the right projection. -/
@[reassoc]
theorem homotopyPullbackPath_evalOne {X Y B : TopCat.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) :
    homotopyPullbackPath f g ≫ pathEvalOne B =
      homotopyPullbackRight f g ≫ g := by
  have h :
      pullback.fst (Limits.prod.map f g) (pathEndpoints B) ≫
          Limits.prod.map f g =
        pullback.snd (Limits.prod.map f g) (pathEndpoints B) ≫
          pathEndpoints B :=
    pullback.condition
  have hone := congrArg
    (fun k => k ≫ (Limits.prod.snd : B ⨯ B ⟶ B)) h
  change pullback.snd (Limits.prod.map f g) (pathEndpoints B) ≫
      pathEvalOne B =
    (pullback.fst (Limits.prod.map f g) (pathEndpoints B) ≫
      Limits.prod.snd) ≫ g
  simpa [pathEndpoints, Category.assoc] using hone.symm

/-- Maps into a homotopy pullback are determined by the left, right, and path projections. -/
@[ext]
theorem homotopyPullback_hom_ext {W X Y B : TopCat.{u}}
    {f : X ⟶ B} {g : Y ⟶ B} {a b : W ⟶ homotopyPullback f g}
    (hleft : a ≫ homotopyPullbackLeft f g = b ≫ homotopyPullbackLeft f g)
    (hright : a ≫ homotopyPullbackRight f g = b ≫ homotopyPullbackRight f g)
    (hpath : a ≫ homotopyPullbackPath f g = b ≫ homotopyPullbackPath f g) :
    a = b := by
  apply pullback.hom_ext
  · apply Limits.prod.hom_ext
    · simpa [homotopyPullbackLeft, Category.assoc] using hleft
    · simpa [homotopyPullbackRight, Category.assoc] using hright
  · exact hpath

/-- Functoriality of homotopy pullback under a map of both cospans. -/
noncomputable def homotopyPullbackMap
    {X Y B X' Y' B' : TopCat.{u}}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : X' ⟶ B'} {g' : Y' ⟶ B'}
    (l : X ⟶ X') (r : Y ⟶ Y') (h : B ⟶ B')
    (hf : f ≫ h = l ≫ f') (hg : g ≫ h = r ≫ g') :
    homotopyPullback f g ⟶ homotopyPullback f' g' :=
  pullback.lift
    (pullback.fst (Limits.prod.map f g) (pathEndpoints B) ≫
      Limits.prod.map l r)
    (pullback.snd (Limits.prod.map f g) (pathEndpoints B) ≫ pathObjectMap h)
    (by
      calc
        (pullback.fst (Limits.prod.map f g) (pathEndpoints B) ≫
              Limits.prod.map l r) ≫ Limits.prod.map f' g' =
            pullback.fst (Limits.prod.map f g) (pathEndpoints B) ≫
              Limits.prod.map (l ≫ f') (r ≫ g') := by simp
        _ = pullback.fst (Limits.prod.map f g) (pathEndpoints B) ≫
              Limits.prod.map (f ≫ h) (g ≫ h) := by rw [hf, hg]
        _ = (pullback.fst (Limits.prod.map f g) (pathEndpoints B) ≫
              Limits.prod.map f g) ≫ Limits.prod.map h h := by simp
        _ = (pullback.snd (Limits.prod.map f g) (pathEndpoints B) ≫
              pathEndpoints B) ≫ Limits.prod.map h h := by rw [pullback.condition]
        _ = pullback.snd (Limits.prod.map f g) (pathEndpoints B) ≫
              (pathEndpoints B ≫ Limits.prod.map h h) := Category.assoc _ _ _
        _ = pullback.snd (Limits.prod.map f g) (pathEndpoints B) ≫
              (pathObjectMap h ≫ pathEndpoints B') := by
                rw [pathObjectMap_endpoints]
        _ = (pullback.snd (Limits.prod.map f g) (pathEndpoints B) ≫
              pathObjectMap h) ≫ pathEndpoints B' :=
                (Category.assoc _ _ _).symm)

@[reassoc (attr := simp)]
theorem homotopyPullbackMap_left
    {X Y B X' Y' B' : TopCat.{u}}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : X' ⟶ B'} {g' : Y' ⟶ B'}
    (l : X ⟶ X') (r : Y ⟶ Y') (h : B ⟶ B')
    (hf : f ≫ h = l ≫ f') (hg : g ≫ h = r ≫ g') :
    homotopyPullbackMap l r h hf hg ≫ homotopyPullbackLeft f' g' =
      homotopyPullbackLeft f g ≫ l := by
  rw [homotopyPullbackMap, ← Category.assoc, pullback.lift_fst]
  simp [homotopyPullbackLeft, Category.assoc]

@[reassoc (attr := simp)]
theorem homotopyPullbackMap_right
    {X Y B X' Y' B' : TopCat.{u}}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : X' ⟶ B'} {g' : Y' ⟶ B'}
    (l : X ⟶ X') (r : Y ⟶ Y') (h : B ⟶ B')
    (hf : f ≫ h = l ≫ f') (hg : g ≫ h = r ≫ g') :
    homotopyPullbackMap l r h hf hg ≫ homotopyPullbackRight f' g' =
      homotopyPullbackRight f g ≫ r := by
  rw [homotopyPullbackMap, ← Category.assoc, pullback.lift_fst]
  simp [homotopyPullbackRight, Category.assoc]

@[reassoc (attr := simp)]
theorem homotopyPullbackMap_path
    {X Y B X' Y' B' : TopCat.{u}}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : X' ⟶ B'} {g' : Y' ⟶ B'}
    (l : X ⟶ X') (r : Y ⟶ Y') (h : B ⟶ B')
    (hf : f ≫ h = l ≫ f') (hg : g ≫ h = r ≫ g') :
    homotopyPullbackMap l r h hf hg ≫ homotopyPullbackPath f' g' =
      homotopyPullbackPath f g ≫ pathObjectMap h := by
  rw [homotopyPullbackMap, pullback.lift_snd]

@[simp]
theorem homotopyPullbackMap_id
    {X Y B : TopCat.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
    homotopyPullbackMap (𝟙 X) (𝟙 Y) (𝟙 B) (by simp) (by simp) =
      𝟙 (homotopyPullback f g) := by
  apply homotopyPullback_hom_ext
  · simp
  · simp
  · simp [pathObjectMap_id]

@[simp ←]
theorem homotopyPullbackMap_comp
    {X₀ Y₀ B₀ X₁ Y₁ B₁ X₂ Y₂ B₂ : TopCat.{u}}
    {f₀ : X₀ ⟶ B₀} {g₀ : Y₀ ⟶ B₀}
    {f₁ : X₁ ⟶ B₁} {g₁ : Y₁ ⟶ B₁}
    {f₂ : X₂ ⟶ B₂} {g₂ : Y₂ ⟶ B₂}
    (l₁ : X₀ ⟶ X₁) (r₁ : Y₀ ⟶ Y₁) (h₁ : B₀ ⟶ B₁)
    (l₂ : X₁ ⟶ X₂) (r₂ : Y₁ ⟶ Y₂) (h₂ : B₁ ⟶ B₂)
    (hf₁ : f₀ ≫ h₁ = l₁ ≫ f₁) (hg₁ : g₀ ≫ h₁ = r₁ ≫ g₁)
    (hf₂ : f₁ ≫ h₂ = l₂ ≫ f₂) (hg₂ : g₁ ≫ h₂ = r₂ ≫ g₂) :
    homotopyPullbackMap (l₁ ≫ l₂) (r₁ ≫ r₂) (h₁ ≫ h₂)
        (by
          calc
            f₀ ≫ h₁ ≫ h₂ = (f₀ ≫ h₁) ≫ h₂ := (Category.assoc _ _ _).symm
            _ = (l₁ ≫ f₁) ≫ h₂ := congrArg (· ≫ h₂) hf₁
            _ = l₁ ≫ f₁ ≫ h₂ := Category.assoc _ _ _
            _ = l₁ ≫ l₂ ≫ f₂ := congrArg (l₁ ≫ ·) hf₂)
        (by
          calc
            g₀ ≫ h₁ ≫ h₂ = (g₀ ≫ h₁) ≫ h₂ := (Category.assoc _ _ _).symm
            _ = (r₁ ≫ g₁) ≫ h₂ := congrArg (· ≫ h₂) hg₁
            _ = r₁ ≫ g₁ ≫ h₂ := Category.assoc _ _ _
            _ = r₁ ≫ r₂ ≫ g₂ := congrArg (r₁ ≫ ·) hg₂) =
      homotopyPullbackMap l₁ r₁ h₁ hf₁ hg₁ ≫
        homotopyPullbackMap l₂ r₂ h₂ hf₂ hg₂ := by
  apply homotopyPullback_hom_ext
  · simp
  · simp
  · simp [pathObjectMap_comp]

/-- Homotopy fiber over a point, with paths from `f x` to the chosen point. -/
abbrev homotopyFiber {X B : TopCat.{u}} (f : X ⟶ B) (b : B) : TopCat.{u} :=
  homotopyPullback f (TopCat.const b : TopCat.of PUnit ⟶ B)

/-- Projection from the homotopy fiber to the source. -/
abbrev homotopyFiberToTotal {X B : TopCat.{u}} (f : X ⟶ B) (b : B) :
    homotopyFiber f b ⟶ X :=
  homotopyPullbackLeft f (TopCat.const b)

/-- Path carried by a homotopy-fiber point. -/
abbrev homotopyFiberPath {X B : TopCat.{u}} (f : X ⟶ B) (b : B) :
    homotopyFiber f b ⟶ pathObject B :=
  homotopyPullbackPath f (TopCat.const b)

end TopCat
