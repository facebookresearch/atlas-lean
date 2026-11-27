/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Category.TopCat.HomotopyPullback

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace TopCat

section Generic

variable {W X Y B X' Y' B' : TopCat.{u}}
variable (f : X ⟶ B) (g : Y ⟶ B)

example : TopCat.{u} := pathObject B
example : pathObject B ⟶ B := pathEvalZero B
example : pathObject B ⟶ B := pathEvalOne B
example : pathObject B ⟶ B ⨯ B := pathEndpoints B

example (h : B ⟶ B') : pathObject B ⟶ pathObject B' :=
  pathObjectMap h

example (h : B ⟶ B') :
    pathObjectMap h ≫ pathEvalZero B' = pathEvalZero B ≫ h := by
  apply pathObjectMap_evalZero

example (h : B ⟶ B') :
    pathObjectMap h ≫ pathEvalOne B' = pathEvalOne B ≫ h := by
  apply pathObjectMap_evalOne

example (h : B ⟶ B') :
    pathObjectMap h ≫ pathEndpoints B' =
      pathEndpoints B ≫ Limits.prod.map h h := by
  apply pathObjectMap_endpoints

example : pathObjectMap (𝟙 B) = 𝟙 (pathObject B) := by
  apply pathObjectMap_id

example (h : B ⟶ B') (h' : B' ⟶ W) :
    pathObjectMap (h ≫ h') = pathObjectMap h ≫ pathObjectMap h' := by
  apply pathObjectMap_comp

example : TopCat.{u} := homotopyPullback f g
example : homotopyPullback f g ⟶ X := homotopyPullbackLeft f g
example : homotopyPullback f g ⟶ Y := homotopyPullbackRight f g
example : homotopyPullback f g ⟶ pathObject B := homotopyPullbackPath f g

example :
    homotopyPullbackPath f g ≫ pathEvalZero B =
      homotopyPullbackLeft f g ≫ f := by
  apply homotopyPullbackPath_evalZero

example :
    homotopyPullbackPath f g ≫ pathEvalOne B =
      homotopyPullbackRight f g ≫ g := by
  apply homotopyPullbackPath_evalOne

example {a b : W ⟶ homotopyPullback f g}
    (hleft : a ≫ homotopyPullbackLeft f g = b ≫ homotopyPullbackLeft f g)
    (hright : a ≫ homotopyPullbackRight f g = b ≫ homotopyPullbackRight f g)
    (hpath : a ≫ homotopyPullbackPath f g = b ≫ homotopyPullbackPath f g) :
    a = b := by
  apply homotopyPullback_hom_ext hleft hright hpath

example {f' : X' ⟶ B'} {g' : Y' ⟶ B'}
    (l : X ⟶ X') (r : Y ⟶ Y') (h : B ⟶ B')
    (hf : f ≫ h = l ≫ f') (hg : g ≫ h = r ≫ g') :
    homotopyPullback f g ⟶ homotopyPullback f' g' :=
  homotopyPullbackMap l r h hf hg

example {f' : X' ⟶ B'} {g' : Y' ⟶ B'}
    (l : X ⟶ X') (r : Y ⟶ Y') (h : B ⟶ B')
    (hf : f ≫ h = l ≫ f') (hg : g ≫ h = r ≫ g') :
    homotopyPullbackMap l r h hf hg ≫ homotopyPullbackLeft f' g' =
      homotopyPullbackLeft f g ≫ l := by
  apply homotopyPullbackMap_left

example {f' : X' ⟶ B'} {g' : Y' ⟶ B'}
    (l : X ⟶ X') (r : Y ⟶ Y') (h : B ⟶ B')
    (hf : f ≫ h = l ≫ f') (hg : g ≫ h = r ≫ g') :
    homotopyPullbackMap l r h hf hg ≫ homotopyPullbackRight f' g' =
      homotopyPullbackRight f g ≫ r := by
  apply homotopyPullbackMap_right

example {f' : X' ⟶ B'} {g' : Y' ⟶ B'}
    (l : X ⟶ X') (r : Y ⟶ Y') (h : B ⟶ B')
    (hf : f ≫ h = l ≫ f') (hg : g ≫ h = r ≫ g') :
    homotopyPullbackMap l r h hf hg ≫ homotopyPullbackPath f' g' =
      homotopyPullbackPath f g ≫ pathObjectMap h := by
  apply homotopyPullbackMap_path

example :
    homotopyPullbackMap (𝟙 X) (𝟙 Y) (𝟙 B) (by simp) (by simp) =
      𝟙 (homotopyPullback f g) := by
  apply homotopyPullbackMap_id

section Composition

variable {X₀ Y₀ B₀ X₁ Y₁ B₁ X₂ Y₂ B₂ : TopCat.{u}}
variable {f₀ : X₀ ⟶ B₀} {g₀ : Y₀ ⟶ B₀}
variable {f₁ : X₁ ⟶ B₁} {g₁ : Y₁ ⟶ B₁}
variable {f₂ : X₂ ⟶ B₂} {g₂ : Y₂ ⟶ B₂}

example (l₁ : X₀ ⟶ X₁) (r₁ : Y₀ ⟶ Y₁) (h₁ : B₀ ⟶ B₁)
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
  apply homotopyPullbackMap_comp

end Composition

example (b : B) : TopCat.{u} := homotopyFiber f b
example (b : B) : homotopyFiber f b ⟶ X := homotopyFiberToTotal f b
example (b : B) : homotopyFiber f b ⟶ pathObject B := homotopyFiberPath f b

example (b : B) :
    homotopyFiberPath f b ≫ pathEvalZero B =
      homotopyFiberToTotal f b ≫ f := by
  apply homotopyPullbackPath_evalZero

example (b : B) :
    homotopyFiberPath f b ≫ pathEvalOne B = TopCat.const b := by
  have h := homotopyPullbackPath_evalOne f
    (TopCat.const b : TopCat.of PUnit ⟶ B)
  calc
    homotopyFiberPath f b ≫ pathEvalOne B =
        homotopyPullbackRight f (TopCat.const b) ≫ TopCat.const b := h
    _ = TopCat.const b := by
      ext x
      rfl

end Generic

section Concrete

private abbrev Two := TopCat.discrete.obj Bool
private abbrev Point := TopCat.discrete.obj PUnit

private def falsePoint : Point ⟶ Two := TopCat.const false
private def truePoint : Point ⟶ Two := TopCat.const true

example : homotopyPullback falsePoint truePoint ⟶ pathObject Two :=
  homotopyPullbackPath falsePoint truePoint

example : homotopyFiber (𝟙 Two) false ⟶ Two :=
  homotopyFiberToTotal (𝟙 Two) false

example : homotopyFiber (TopCat.const false : Point ⟶ Two) true ⟶ pathObject Two :=
  homotopyFiberPath (TopCat.const false : Point ⟶ Two) true

example : pathEvalZero Two (ContinuousMap.const TopCat.I false) = false :=
  rfl

example : pathEvalOne Two (ContinuousMap.const TopCat.I false) = false :=
  rfl

end Concrete

section UniverseOne

example (B : TopCat.{1}) : TopCat.{1} := pathObject B

example {X B : TopCat.{1}} (f : X ⟶ B) (b : B) : TopCat.{1} :=
  homotopyFiber f b

end UniverseOne

section UniverseZero

example (B : TopCat.{0}) : TopCat.{0} := pathObject B

example {X B : TopCat.{0}} (f : X ⟶ B) (b : B) : TopCat.{0} :=
  homotopyFiber f b

end UniverseZero

#check pathObject
#check pathEvalZero
#check pathEvalOne
#check pathEndpoints
#check pathObjectMap
#check pathObjectMap_evalZero
#check pathObjectMap_evalOne
#check pathObjectMap_endpoints
#check pathObjectMap_id
#check pathObjectMap_comp
#check homotopyPullback
#check homotopyPullbackLeft
#check homotopyPullbackRight
#check homotopyPullbackPath
#check homotopyPullbackPath_evalZero
#check homotopyPullbackPath_evalOne
#check homotopyPullback_hom_ext
#check homotopyPullbackMap
#check homotopyPullbackMap_left
#check homotopyPullbackMap_right
#check homotopyPullbackMap_path
#check homotopyPullbackMap_id
#check homotopyPullbackMap_comp
#check homotopyFiber
#check homotopyFiberToTotal
#check homotopyFiberPath

#print axioms pathObject
#print axioms pathEvalZero
#print axioms pathEvalOne
#print axioms pathEndpoints
#print axioms pathObjectMap
#print axioms pathObjectMap_evalZero
#print axioms pathObjectMap_evalOne
#print axioms pathObjectMap_endpoints
#print axioms pathObjectMap_id
#print axioms pathObjectMap_comp
#print axioms homotopyPullback
#print axioms homotopyPullbackLeft
#print axioms homotopyPullbackRight
#print axioms homotopyPullbackPath
#print axioms homotopyPullbackPath_evalZero
#print axioms homotopyPullbackPath_evalOne
#print axioms homotopyPullback_hom_ext
#print axioms homotopyPullbackMap
#print axioms homotopyPullbackMap_left
#print axioms homotopyPullbackMap_right
#print axioms homotopyPullbackMap_path
#print axioms homotopyPullbackMap_id
#print axioms homotopyPullbackMap_comp
#print axioms homotopyFiber
#print axioms homotopyFiberToTotal
#print axioms homotopyFiberPath

end TopCat
