/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Reedy.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Original latching, matching and caller chosen boundary maps

The original category, degree, boundary maps and coefficient factories are retained.
Only the actual latching and matching shape (co)limits used by these constructions
are required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uJ vJ uD uC vC uB vB uS vS uK vK

section ReedyPart1

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]

/-- The original nonidentity direct arrows into the supplied source object. -/
abbrev latchingObjects (j : J) : ObjectProperty (Over (⟨j⟩ : r.Direct)) :=
  fun a => r.degree a.left.obj < r.degree j

/-- The original nonidentity inverse arrows out of the supplied source object. -/
abbrev matchingObjects (j : J) : ObjectProperty (Under (⟨j⟩ : r.Inverse)) :=
  fun a => r.degree a.right.obj < r.degree j

/-- The latching source keeps all actual direct comparison triangles. -/
abbrev Latching (j : J) := (r.latchingObjects j).FullSubcategory

/-- The matching source keeps all actual inverse comparison triangles. -/
abbrev Matching (j : J) := (r.matchingObjects j).FullSubcategory


/-- The original domain of a supplied latching arrow. -/
abbrev latchingSource {j : J} (a : r.Latching j) : J := a.obj.left.obj

/-- The original codomain of a supplied matching arrow. -/
abbrev matchingTarget {j : J} (a : r.Matching j) : J := a.obj.right.obj

/-- The actual incoming source arrow, with its original ordinary category type. -/
def latchingArrow {j : J} (a : r.Latching j) : r.latchingSource a ⟶ j := a.obj.hom.hom

/-- The actual outgoing source arrow, with its original ordinary category type. -/
def matchingArrow {j : J} (a : r.Matching j) : j ⟶ r.matchingTarget a := a.obj.hom.hom

/-- The ordinary source arrow of each actual latching comparison triangle. -/
def latchingComparison {j : J} {a c : r.Latching j} (f : a ⟶ c) :
    r.latchingSource a ⟶ r.latchingSource c := f.hom.left.hom

/-- The ordinary source arrow of each actual matching comparison triangle. -/
def matchingComparison {j : J} {a c : r.Matching j} (f : a ⟶ c) :
    r.matchingTarget a ⟶ r.matchingTarget c := f.hom.right.hom

/-- Each latching comparison is its original complete direct triangle. -/
theorem latchingComparison_arrow {j : J} {a c : r.Latching j} (f : a ⟶ c) :
    r.latchingComparison f ≫ r.latchingArrow c = r.latchingArrow a :=
  congrArg (fun h => h.hom) (Over.w f.hom)

/-- Each matching comparison is its original complete inverse triangle. -/
theorem matchingArrow_comparison {j : J} {a c : r.Matching j} (f : a ⟶ c) :
    r.matchingArrow a ≫ r.matchingComparison f = r.matchingArrow c :=
  congrArg (fun h => h.hom) (Under.w f.hom)

/-- Every caller nonidentity direct arrow is an actual object of the latching source. -/
def latchingMk {k j : J} (f : k ⟶ j) (hf : r.direct f) (hk : r.degree k < r.degree j) :
    r.Latching j := ⟨Over.mk ⟨f, hf⟩, hk⟩

/-- Every caller nonidentity inverse arrow is an actual object of the matching source. -/
def matchingMk {j k : J} (f : j ⟶ k) (hf : r.inverse f) (hk : r.degree k < r.degree j) :
    r.Matching j := ⟨Under.mk ⟨f, hf⟩, hk⟩

@[simp]
theorem latchingSource_mk {k j : J} (f : k ⟶ j) (hf : r.direct f) (hk : r.degree k < r.degree j) :
    r.latchingSource (r.latchingMk f hf hk) = k := rfl

@[simp]
theorem matchingTarget_mk {j k : J} (f : j ⟶ k) (hf : r.inverse f) (hk : r.degree k < r.degree j) :
    r.matchingTarget (r.matchingMk f hf hk) = k := rfl

@[simp]
theorem latchingArrow_mk {k j : J} (f : k ⟶ j) (hf : r.direct f) (hk : r.degree k < r.degree j) :
    r.latchingArrow (r.latchingMk f hf hk) = f := rfl

@[simp]
theorem matchingArrow_mk {j k : J} (f : j ⟶ k) (hf : r.inverse f) (hk : r.degree k < r.degree j) :
    r.matchingArrow (r.matchingMk f hf hk) = f := rfl

/-- The latching inclusion retains each original domain and direct comparison map. -/
abbrev latchingInclusion (j : J) : r.Latching j ⥤ J where
  obj a := r.latchingSource a
  map f := r.latchingComparison f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The matching inclusion retains each original codomain and inverse comparison map. -/
abbrev matchingInclusion (j : J) : r.Matching j ⥤ J where
  obj a := r.matchingTarget a
  map f := r.matchingComparison f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The actual latching diagram is the restriction of the full original caller diagram. -/
abbrev latchingDiagram (X : J ⥤ C) (j : J) : r.Latching j ⥤ C :=
  r.latchingInclusion j ⋙ X

/-- The actual matching diagram is the restriction of the full original caller diagram. -/
abbrev matchingDiagram (X : J ⥤ C) (j : J) : r.Matching j ⥤ C :=
  r.matchingInclusion j ⋙ X

/-- Each original coefficient and incoming direct arrow is retained in the full latching cocone. -/
def latchingCocone (X : J ⥤ C) (j : J) : Cocone (r.latchingDiagram X j) where
  pt := X.obj j
  ι.app a := X.map (r.latchingArrow a)
  ι.naturality a b f := by
    change X.map (r.latchingComparison f) ≫ X.map (r.latchingArrow b) =
      X.map (r.latchingArrow a) ≫ 𝟙 _
    rw [Category.comp_id, ← X.map_comp]
    congr 1
    exact r.latchingComparison_arrow f

/-- Each original coefficient and outgoing inverse arrow is retained in the full matching cone. -/
def matchingCone (X : J ⥤ C) (j : J) : Cone (r.matchingDiagram X j) where
  pt := X.obj j
  π.app a := X.map (r.matchingArrow a)
  π.naturality a b f := by
    change 𝟙 _ ≫ X.map (r.matchingArrow b) =
      X.map (r.matchingArrow a) ≫ X.map (r.matchingComparison f)
    rw [Category.id_comp, ← X.map_comp]
    congr 1
    exact (r.matchingArrow_comparison f).symm

/-- The original transformation restricted to all original direct latching triangles. -/
abbrev latchingTransformation {X Y : J ⥤ C} (f : X ⟶ Y) (j : J) :
    r.latchingDiagram X j ⟶ r.latchingDiagram Y j :=
  Functor.whiskerLeft (r.latchingInclusion j) f

/-- The original transformation restricted to all original inverse matching triangles. -/
abbrev matchingTransformation {X Y : J ⥤ C} (f : X ⟶ Y) (j : J) :
    r.matchingDiagram X j ⟶ r.matchingDiagram Y j :=
  Functor.whiskerLeft (r.matchingInclusion j) f

/-- The actual latching map obtained from any caller complete latching cocone. -/
def latchingMapWith (X : J ⥤ C) (j : J) (c : Cocone (r.latchingDiagram X j))
    (hc : IsColimit c) : c.pt ⟶ X.obj j := hc.desc (r.latchingCocone X j)

/-- The actual matching map obtained from any caller complete matching cone. -/
def matchingMapWith (X : J ⥤ C) (j : J) (c : Cone (r.matchingDiagram X j))
    (hc : IsLimit c) : X.obj j ⟶ c.pt := hc.lift (r.matchingCone X j)

/-- Every caller latching injection recovers the same original direct coefficient arrow. -/
@[reassoc]
theorem latchingMapWith_ι (X : J ⥤ C) (j : J) (c : Cocone (r.latchingDiagram X j))
    (hc : IsColimit c) (a : r.Latching j) :
    c.ι.app a ≫ r.latchingMapWith X j c hc = X.map (r.latchingArrow a) := hc.fac _ a

/-- Every caller matching projection recovers the same original inverse coefficient arrow. -/
@[reassoc]
theorem matchingMapWith_π (X : J ⥤ C) (j : J) (c : Cone (r.matchingDiagram X j))
    (hc : IsLimit c) (a : r.Matching j) :
    r.matchingMapWith X j c hc ≫ c.π.app a = X.map (r.matchingArrow a) := hc.fac _ a


end CategoryTheory.ReedyStructure

end ReedyPart1

section ReedyPart2

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]

/-- The complete actual transformation between any caller latching colimits. -/
def latchingComparisonWith {X Y : J ⥤ C} (f : X ⟶ Y) (j : J)
    (cX : Cocone (r.latchingDiagram X j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram Y j)) : cX.pt ⟶ cY.pt :=
  hX.desc ((Cocone.precompose (r.latchingTransformation f j)).obj cY)

/-- The complete actual transformation between any caller matching limits. -/
def matchingComparisonWith {X Y : J ⥤ C} (f : X ⟶ Y) (j : J)
    (cX : Cone (r.matchingDiagram X j))
    (cY : Cone (r.matchingDiagram Y j)) (hY : IsLimit cY) : cX.pt ⟶ cY.pt :=
  hY.lift ((Cone.postcompose (r.matchingTransformation f j)).obj cX)

/-- Every caller latching comparison injection retains the original coefficient transformation. -/
@[reassoc]
theorem latchingComparisonWith_ι {X Y : J ⥤ C} (f : X ⟶ Y) (j : J)
    (cX : Cocone (r.latchingDiagram X j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram Y j)) (a : r.Latching j) :
    cX.ι.app a ≫ r.latchingComparisonWith f j cX hX cY = f.app (r.latchingSource a) ≫ cY.ι.app a :=
  hX.fac _ a

/-- Every caller matching comparison projection retains the original coefficient transformation. -/
@[reassoc]
theorem matchingComparisonWith_π {X Y : J ⥤ C} (f : X ⟶ Y) (j : J)
    (cX : Cone (r.matchingDiagram X j))
    (cY : Cone (r.matchingDiagram Y j)) (hY : IsLimit cY) (a : r.Matching j) :
    r.matchingComparisonWith f j cX cY hY ≫ cY.π.app a = cX.π.app a ≫ f.app (r.matchingTarget a) :=
  hY.fac _ a

/-- The complete chosen latching comparison preserves the actual original identity. -/
theorem latchingComparisonWith_id (X : J ⥤ C) (j : J)
    (c : Cocone (r.latchingDiagram X j)) (hc : IsColimit c) :
    r.latchingComparisonWith (𝟙 X) j c hc c = 𝟙 c.pt := by
  apply hc.hom_ext
  intro a
  rw [r.latchingComparisonWith_ι]
  simp

/-- The complete chosen matching comparison preserves the actual original identity. -/
theorem matchingComparisonWith_id (X : J ⥤ C) (j : J)
    (c : Cone (r.matchingDiagram X j)) (hc : IsLimit c) :
    r.matchingComparisonWith (𝟙 X) j c c hc = 𝟙 c.pt := by
  apply hc.hom_ext
  intro a
  rw [r.matchingComparisonWith_π]
  simp

/-- Chosen latching comparisons retain every original compositional comparison naturality. -/
theorem latchingComparisonWith_comp {X Y Z : J ⥤ C} (f : X ⟶ Y) (g : Y ⟶ Z) (j : J)
    (cX : Cocone (r.latchingDiagram X j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram Y j)) (hY : IsColimit cY)
    (cZ : Cocone (r.latchingDiagram Z j)) :
    r.latchingComparisonWith (f ≫ g) j cX hX cZ =
      r.latchingComparisonWith f j cX hX cY ≫ r.latchingComparisonWith g j cY hY cZ := by
  apply hX.hom_ext
  intro a
  rw [r.latchingComparisonWith_ι, r.latchingComparisonWith_ι_assoc, r.latchingComparisonWith_ι]
  change (f.app (r.latchingSource a) ≫ g.app (r.latchingSource a)) ≫ cZ.ι.app a =
    f.app (r.latchingSource a) ≫ g.app (r.latchingSource a) ≫ cZ.ι.app a
  exact Category.assoc _ _ _

/-- Chosen matching comparisons retain every original compositional comparison naturality. -/
theorem matchingComparisonWith_comp {X Y Z : J ⥤ C} (f : X ⟶ Y) (g : Y ⟶ Z) (j : J)
    (cX : Cone (r.matchingDiagram X j))
    (cY : Cone (r.matchingDiagram Y j)) (hY : IsLimit cY)
    (cZ : Cone (r.matchingDiagram Z j)) (hZ : IsLimit cZ) :
    r.matchingComparisonWith (f ≫ g) j cX cZ hZ =
      r.matchingComparisonWith f j cX cY hY ≫ r.matchingComparisonWith g j cY cZ hZ := by
  apply hZ.hom_ext
  intro a
  rw [r.matchingComparisonWith_π, Category.assoc, r.matchingComparisonWith_π,
    r.matchingComparisonWith_π_assoc]
  rfl

/-- Every caller latching map commutes with its complete original chosen latching comparison. -/
theorem latchingMapWith_naturality {X Y : J ⥤ C} (f : X ⟶ Y) (j : J)
    (cX : Cocone (r.latchingDiagram X j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram Y j)) (hY : IsColimit cY) :
    r.latchingMapWith X j cX hX ≫ f.app j =
      r.latchingComparisonWith f j cX hX cY ≫ r.latchingMapWith Y j cY hY := by
  apply hX.hom_ext
  intro a
  rw [r.latchingMapWith_ι_assoc, r.latchingComparisonWith_ι_assoc, r.latchingMapWith_ι]
  exact f.naturality (r.latchingArrow a)

/-- Every caller matching map commutes with its complete original chosen matching comparison. -/
theorem matchingMapWith_naturality {X Y : J ⥤ C} (f : X ⟶ Y) (j : J)
    (cX : Cone (r.matchingDiagram X j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram Y j)) (hY : IsLimit cY) :
    r.matchingMapWith X j cX hX ≫ r.matchingComparisonWith f j cX cY hY =
      f.app j ≫ r.matchingMapWith Y j cY hY := by
  apply hY.hom_ext
  intro a
  rw [Category.assoc, r.matchingComparisonWith_π, r.matchingMapWith_π_assoc,
    Category.assoc, r.matchingMapWith_π]
  exact f.naturality (r.matchingArrow a)

/-- The original latching-corner map from any caller chosen complete boundary pushout. -/
def latchingCornerWith {X Y : J ⥤ C} (f : X ⟶ Y) (j : J)
    (cX : Cocone (r.latchingDiagram X j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram Y j)) (hY : IsColimit cY)
    (cP : PushoutCocone (r.latchingMapWith X j cX hX) (r.latchingComparisonWith f j cX hX cY))
    (hP : IsColimit cP) : cP.pt ⟶ Y.obj j :=
  hP.desc (PushoutCocone.mk (f.app j) (r.latchingMapWith Y j cY hY)
    (r.latchingMapWith_naturality f j cX hX cY hY))

/-- The original matching-corner map to any caller chosen complete boundary pullback. -/
def matchingCornerWith {X Y : J ⥤ C} (f : X ⟶ Y) (j : J)
    (cX : Cone (r.matchingDiagram X j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram Y j)) (hY : IsLimit cY)
    (cP : PullbackCone (r.matchingComparisonWith f j cX cY hY) (r.matchingMapWith Y j cY hY))
    (hP : IsLimit cP) : X.obj j ⟶ cP.pt :=
  hP.lift (PullbackCone.mk (r.matchingMapWith X j cX hX) (f.app j)
    (r.matchingMapWith_naturality f j cX hX cY hY))

/-- The caller latching-corner left injection retains the unchanged original component map. -/
@[reassoc]
theorem latchingCornerWith_inl {X Y : J ⥤ C} (f : X ⟶ Y) (j : J)
    (cX : Cocone (r.latchingDiagram X j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram Y j)) (hY : IsColimit cY)
    (cP : PushoutCocone (r.latchingMapWith X j cX hX) (r.latchingComparisonWith f j cX hX cY))
    (hP : IsColimit cP) : cP.inl ≫ r.latchingCornerWith f j cX hX cY hY cP hP = f.app j :=
  hP.fac _ WalkingSpan.left

/-- The caller latching-corner right injection retains the unchanged complete caller latching
map. -/
@[reassoc]
theorem latchingCornerWith_inr {X Y : J ⥤ C} (f : X ⟶ Y) (j : J)
    (cX : Cocone (r.latchingDiagram X j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram Y j)) (hY : IsColimit cY)
    (cP : PushoutCocone (r.latchingMapWith X j cX hX) (r.latchingComparisonWith f j cX hX cY))
    (hP : IsColimit cP) : cP.inr ≫ r.latchingCornerWith f j cX hX cY hY cP hP =
      r.latchingMapWith Y j cY hY := hP.fac _ WalkingSpan.right

/-- The caller matching-corner first projection retains the unchanged complete caller matching
map. -/
@[reassoc]
theorem matchingCornerWith_fst {X Y : J ⥤ C} (f : X ⟶ Y) (j : J)
    (cX : Cone (r.matchingDiagram X j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram Y j)) (hY : IsLimit cY)
    (cP : PullbackCone (r.matchingComparisonWith f j cX cY hY) (r.matchingMapWith Y j cY hY))
    (hP : IsLimit cP) : r.matchingCornerWith f j cX hX cY hY cP hP ≫ cP.fst =
      r.matchingMapWith X j cX hX := hP.fac _ WalkingCospan.left

/-- The caller matching-corner second projection retains the unchanged original component map. -/
@[reassoc]
theorem matchingCornerWith_snd {X Y : J ⥤ C} (f : X ⟶ Y) (j : J)
    (cX : Cone (r.matchingDiagram X j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram Y j)) (hY : IsLimit cY)
    (cP : PullbackCone (r.matchingComparisonWith f j cX cY hY) (r.matchingMapWith Y j cY hY))
    (hP : IsLimit cP) : r.matchingCornerWith f j cX hX cY hY cP hP ≫ cP.snd = f.app j :=
  hP.fac _ WalkingCospan.right

end CategoryTheory.ReedyStructure

end ReedyPart2

section ReedyPart3

open CategoryTheory MorphismProperty

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)

/-- The original incoming arrow is in the supplied direct subcategory. -/
theorem latchingArrow_mem {j : J} (a : r.Latching j) : r.direct (r.latchingArrow a) :=
  a.obj.hom.property

/-- The original outgoing arrow is in the supplied inverse subcategory. -/
theorem matchingArrow_mem {j : J} (a : r.Matching j) : r.inverse (r.matchingArrow a) :=
  a.obj.hom.property

/-- Every original latching comparison is direct. -/
theorem latchingComparison_mem {j : J} {a c : r.Latching j} (g : a ⟶ c) :
    r.direct (r.latchingComparison g) := g.hom.left.property

/-- Every original matching comparison is inverse. -/
theorem matchingComparison_mem {j : J} {a c : r.Matching j} (g : a ⟶ c) :
    r.inverse (r.matchingComparison g) := g.hom.right.property

/-- Compose every original smaller incoming arrow with the caller incoming arrow. -/
def latchingCompose {j : J} (a : r.Latching j)
    (b : r.Latching (r.latchingSource a)) : r.Latching j :=
  r.latchingMk (r.latchingArrow b ≫ r.latchingArrow a)
    (r.direct.comp_mem _ _ (r.latchingArrow_mem b) (r.latchingArrow_mem a))
    (b.property.trans a.property)

/-- Compose the caller outgoing arrow with every original smaller outgoing arrow. -/
def matchingCompose {j : J} (a : r.Matching j)
    (b : r.Matching (r.matchingTarget a)) : r.Matching j :=
  r.matchingMk (r.matchingArrow a ≫ r.matchingArrow b)
    (r.inverse.comp_mem _ _ (r.matchingArrow_mem a) (r.matchingArrow_mem b))
    (b.property.trans a.property)

@[simp]
theorem latchingSource_compose {j : J} (a : r.Latching j)
    (b : r.Latching (r.latchingSource a)) :
    r.latchingSource (r.latchingCompose a b) = r.latchingSource b := rfl

@[simp]
theorem matchingTarget_compose {j : J} (a : r.Matching j)
    (b : r.Matching (r.matchingTarget a)) :
    r.matchingTarget (r.matchingCompose a b) = r.matchingTarget b := rfl

/-- Each composed incoming source still has its original strictly smaller degree. -/
theorem latchingCompose_lt {j : J} (a : r.Latching j)
    (b : r.Latching (r.latchingSource a)) :
    r.degree (r.latchingSource (r.latchingCompose a b)) < r.degree (r.latchingSource a) :=
  b.property

/-- Each composed outgoing target still has its original strictly smaller degree. -/
theorem matchingCompose_lt {j : J} (a : r.Matching j)
    (b : r.Matching (r.matchingTarget a)) :
    r.degree (r.matchingTarget (r.matchingCompose a b)) < r.degree (r.matchingTarget a) :=
  b.property

@[simp]
theorem latchingArrow_compose {j : J} (a : r.Latching j)
    (b : r.Latching (r.latchingSource a)) :
    r.latchingArrow (r.latchingCompose a b) = r.latchingArrow b ≫ r.latchingArrow a := rfl

@[simp]
theorem matchingArrow_compose {j : J} (a : r.Matching j)
    (b : r.Matching (r.matchingTarget a)) :
    r.matchingArrow (r.matchingCompose a b) = r.matchingArrow a ≫ r.matchingArrow b := rfl

/-- The complete comparison from a composed incoming arrow to its caller arrow. -/
def latchingComposeTo {j : J} (a : r.Latching j)
    (b : r.Latching (r.latchingSource a)) : r.latchingCompose a b ⟶ a :=
  ObjectProperty.homMk (Over.homMk b.obj.hom (by
    apply WideSubcategory.hom_ext
    rfl))

/-- The complete comparison from the caller outgoing arrow to its composition. -/
def matchingToCompose {j : J} (a : r.Matching j)
    (b : r.Matching (r.matchingTarget a)) : a ⟶ r.matchingCompose a b :=
  ObjectProperty.homMk (Under.homMk b.obj.hom (by
    apply WideSubcategory.hom_ext
    rfl))

@[simp]
theorem latchingComparison_composeTo {j : J} (a : r.Latching j)
    (b : r.Latching (r.latchingSource a)) :
    r.latchingComparison (r.latchingComposeTo a b) = r.latchingArrow b := rfl

@[simp]
theorem matchingComparison_toCompose {j : J} (a : r.Matching j)
    (b : r.Matching (r.matchingTarget a)) :
    r.matchingComparison (r.matchingToCompose a b) = r.matchingArrow b := rfl

/-- Composition preserves every actual incoming comparison triangle. -/
def latchingComposeMap {j : J} (a : r.Latching j)
    {b c : r.Latching (r.latchingSource a)} (g : b ⟶ c) :
    r.latchingCompose a b ⟶ r.latchingCompose a c :=
  ObjectProperty.homMk (Over.homMk g.hom.left (by
    apply WideSubcategory.hom_ext
    change r.latchingComparison g ≫ (r.latchingArrow c ≫ r.latchingArrow a) =
      r.latchingArrow b ≫ r.latchingArrow a
    rw [← Category.assoc, r.latchingComparison_arrow]))

/-- Composition preserves every actual outgoing comparison triangle. -/
def matchingComposeMap {j : J} (a : r.Matching j)
    {b c : r.Matching (r.matchingTarget a)} (g : b ⟶ c) :
    r.matchingCompose a b ⟶ r.matchingCompose a c :=
  ObjectProperty.homMk (Under.homMk g.hom.right (by
    apply WideSubcategory.hom_ext
    change (r.matchingArrow a ≫ r.matchingArrow b) ≫ r.matchingComparison g =
      r.matchingArrow a ≫ r.matchingArrow c
    rw [Category.assoc, r.matchingArrow_comparison]))

@[simp]
theorem latchingComparison_composeMap {j : J} (a : r.Latching j)
    {b c : r.Latching (r.latchingSource a)} (g : b ⟶ c) :
    r.latchingComparison (r.latchingComposeMap a g) = r.latchingComparison g := rfl

@[simp]
theorem matchingComparison_composeMap {j : J} (a : r.Matching j)
    {b c : r.Matching (r.matchingTarget a)} (g : b ⟶ c) :
    r.matchingComparison (r.matchingComposeMap a g) = r.matchingComparison g := rfl

/-- Every smaller original incoming comparison is exactly its source composition. -/
theorem latchingCompose_comparison {j : J} {a c : r.Latching j} (g : a ⟶ c)
    (h : r.degree (r.latchingSource a) < r.degree (r.latchingSource c)) :
    r.latchingCompose c (r.latchingMk (r.latchingComparison g)
      (r.latchingComparison_mem g) h) = a := by
  apply ObjectProperty.FullSubcategory.ext
  refine CostructuredArrow.obj_ext
    (r.latchingCompose c (r.latchingMk (r.latchingComparison g)
      (r.latchingComparison_mem g) h)).obj a.obj ?_ ?_
  · rfl
  · apply WideSubcategory.hom_ext
    change (𝟙 (r.latchingSource a)) ≫ r.latchingArrow a =
      r.latchingComparison g ≫ r.latchingArrow c
    rw [Category.id_comp]
    exact (r.latchingComparison_arrow g).symm

/-- Every smaller original outgoing comparison is exactly its target composition. -/
theorem matchingCompose_comparison {j : J} {a c : r.Matching j} (g : a ⟶ c)
    (h : r.degree (r.matchingTarget c) < r.degree (r.matchingTarget a)) :
    r.matchingCompose a (r.matchingMk (r.matchingComparison g)
      (r.matchingComparison_mem g) h) = c := by
  apply ObjectProperty.FullSubcategory.ext
  refine StructuredArrow.obj_ext
    (r.matchingCompose a (r.matchingMk (r.matchingComparison g)
      (r.matchingComparison_mem g) h)).obj c.obj ?_ ?_
  · rfl
  · apply WideSubcategory.hom_ext
    change (r.matchingArrow a ≫ r.matchingComparison g) ≫ (𝟙 (r.matchingTarget c)) =
      r.matchingArrow c
    rw [Category.comp_id]
    exact r.matchingArrow_comparison g

/-- The direct inclusion retains the original identity transport. -/
theorem direct_eqToHom {a c : r.Direct} (e : a = c) :
    (eqToHom e).hom = eqToHom (congrArg WideSubcategory.obj e) := by
  cases e
  rfl

/-- The inverse inclusion retains the original identity transport. -/
theorem inverse_eqToHom {a c : r.Inverse} (e : a = c) :
    (eqToHom e).hom = eqToHom (congrArg WideSubcategory.obj e) := by
  cases e
  rfl

/-- A latching comparison whose degree does not rise is the actual object identity transport. -/
theorem latchingComparison_identity_of_not_lt {j : J} {a c : r.Latching j} (g : a ⟶ c)
    (h : ¬ r.degree (r.latchingSource a) < r.degree (r.latchingSource c)) :
    ∃ e : a = c, r.latchingComparison g = eqToHom (congrArg r.latchingSource e) := by
  obtain ⟨e₀, hg⟩ := r.direct_identity_of_not_lt
    (r.latchingComparison g) (r.latchingComparison_mem g) h
  have e : a.obj.left = c.obj.left := WideSubcategory.ext e₀
  have hg' : g.hom.left = eqToHom e := by
    apply WideSubcategory.hom_ext
    rw [r.direct_eqToHom]
    exact hg
  have ea : a = c := by
    apply ObjectProperty.FullSubcategory.ext
    refine CostructuredArrow.obj_ext a.obj c.obj e ?_
    change eqToHom e ≫ c.obj.hom = a.obj.hom
    rw [← hg']
    exact Over.w g.hom
  exact ⟨ea, hg⟩

/-- A matching comparison whose degree does not fall is the actual object identity transport. -/
theorem matchingComparison_identity_of_not_lt {j : J} {a c : r.Matching j} (g : a ⟶ c)
    (h : ¬ r.degree (r.matchingTarget c) < r.degree (r.matchingTarget a)) :
    ∃ e : a = c, r.matchingComparison g = eqToHom (congrArg r.matchingTarget e) := by
  obtain ⟨e₀, hg⟩ := r.inverse_identity_of_not_lt
    (r.matchingComparison g) (r.matchingComparison_mem g) h
  have e : a.obj.right = c.obj.right := WideSubcategory.ext e₀
  have hg' : g.hom.right = eqToHom e := by
    apply WideSubcategory.hom_ext
    rw [r.inverse_eqToHom]
    exact hg
  have ea : a = c := by
    apply ObjectProperty.FullSubcategory.ext
    refine StructuredArrow.obj_ext a.obj c.obj e ?_
    change a.obj.hom ≫ eqToHom e = c.obj.hom
    rw [← hg']
    exact Under.w g.hom
  exact ⟨ea, hg⟩

end CategoryTheory.ReedyStructure

end ReedyPart3

section ReedyPart4

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]

/-- Each actual incoming direct source object lies in the full lower-degree subcategory. -/
abbrev latchingBelow {d : D} (j : J) (hj : r.degree j = d) : r.Latching j ⥤ r.Below d where
  obj a := ⟨r.latchingSource a, a.property.trans_eq hj⟩
  map f := ObjectProperty.homMk (r.latchingComparison f)
  map_id _ := by apply ObjectProperty.hom_ext; rfl
  map_comp _ _ := by apply ObjectProperty.hom_ext; rfl

/-- Each actual outgoing inverse source object lies in the full lower-degree subcategory. -/
abbrev matchingBelow {d : D} (j : J) (hj : r.degree j = d) : r.Matching j ⥤ r.Below d where
  obj a := ⟨r.matchingTarget a, a.property.trans_eq hj⟩
  map f := ObjectProperty.homMk (r.matchingComparison f)
  map_id _ := by apply ObjectProperty.hom_ext; rfl
  map_comp _ _ := by apply ObjectProperty.hom_ext; rfl

/-- The full actual lower latching diagram retains every original direct triangle. -/
abbrev lowerLatchingDiagram {d : D} (P : r.Below d ⥤ C) (j : J) (hj : r.degree j = d) :
    r.Latching j ⥤ C := r.latchingBelow j hj ⋙ P

/-- The full actual lower matching diagram retains every original inverse triangle. -/
abbrev lowerMatchingDiagram {d : D} (P : r.Below d ⥤ C) (j : J) (hj : r.degree j = d) :
    r.Matching j ⥤ C := r.matchingBelow j hj ⋙ P


/-- The actual original composite is an arrow between its precise lower-source objects. -/
def lowerBoundaryArrow {d : D} (j : J) (hj : r.degree j = d)
    (a : r.Latching j) (b : r.Matching j) :
    (r.latchingBelow j hj).obj a ⟶ (r.matchingBelow j hj).obj b :=
  ObjectProperty.homMk (r.latchingArrow a ≫ r.matchingArrow b)

/-- Each incoming original lower coefficient maps to every outgoing coefficient by the original
composite arrow. -/
abbrev lowerBoundaryCone {d : D} (P : r.Below d ⥤ C) (j : J) (hj : r.degree j = d)
    (a : r.Latching j) : Cone (r.lowerMatchingDiagram P j hj) where
  pt := P.obj ((r.latchingBelow j hj).obj a)
  π.app b := P.map (r.lowerBoundaryArrow j hj a b)
  π.naturality b c f := by
    change 𝟙 _ ≫ P.map (r.lowerBoundaryArrow j hj a c) =
      P.map (r.lowerBoundaryArrow j hj a b) ≫
        P.map ((r.matchingBelow j hj).map f)
    rw [Category.id_comp, ← P.map_comp]
    congr 1
    apply ObjectProperty.hom_ext
    change r.latchingArrow a ≫ r.matchingArrow c =
      (r.latchingArrow a ≫ r.matchingArrow b) ≫ r.matchingComparison f
    exact ((Category.assoc _ _ _).trans
      (congrArg (fun h => r.latchingArrow a ≫ h) (r.matchingArrow_comparison f))).symm


end CategoryTheory.ReedyStructure

end ReedyPart4

section ReedyPart5

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]

/-- The exact complete original restriction strictly below the supplied degree. -/
abbrev restrictBelow (X : J ⥤ C) (d : D) : r.Below d ⥤ C := (r.belowObjects d).ι ⋙ X

/-- The exact complete original restriction through the supplied degree. -/
abbrev restrictThrough (X : J ⥤ C) (d : D) : r.Through d ⥤ C := (r.throughObjects d).ι ⋙ X

/-- The complete original lower latching diagram is the same original full caller latching
diagram. -/
theorem lowerLatchingDiagram_restrict (X : J ⥤ C) {d : D} (j : J) (hj : r.degree j = d) :
    r.lowerLatchingDiagram (r.restrictBelow X d) j hj = r.latchingDiagram X j := rfl

/-- The complete original lower matching diagram is the same original full caller matching
diagram. -/
theorem lowerMatchingDiagram_restrict (X : J ⥤ C) {d : D} (j : J) (hj : r.degree j = d) :
    r.lowerMatchingDiagram (r.restrictBelow X d) j hj = r.matchingDiagram X j := rfl


end CategoryTheory.ReedyStructure

end ReedyPart5

section ReedyPart6

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)

/-- The complete actual smaller-degree source inclusion retains each original object and arrow. -/
abbrev belowThrough (d : D) : r.Below d ⥤ r.Through d where
  obj j := ⟨j.obj, le_of_lt j.property⟩
  map f := ObjectProperty.homMk f.hom
  map_id _ := by apply ObjectProperty.hom_ext; rfl
  map_comp _ _ := by apply ObjectProperty.hom_ext; rfl


end CategoryTheory.ReedyStructure

end ReedyPart6

section ReedyPart7

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]

/-- Pointwise functors have the same original latching-shape colimits. -/
instance functorCategory_latchingColimits
    [∀ j, HasColimitsOfShape (r.Latching j) C] (K : Type uK) [Category.{vK} K] :
    ∀ j, HasColimitsOfShape (r.Latching j) (K ⥤ C) := fun _ ↦ inferInstance

/-- Pointwise functors have the same original matching-shape limits. -/
instance functorCategory_matchingLimits
    [∀ j, HasLimitsOfShape (r.Matching j) C] (K : Type uK) [Category.{vK} K] :
    ∀ j, HasLimitsOfShape (r.Matching j) (K ⥤ C) := fun _ ↦ inferInstance

section Latching

variable [∀ j, HasColimitsOfShape (r.Latching j) C]

/-- The original latching map uses precisely its own actual colimit shape. -/
def latchingMap (X : J ⥤ C) (j : J) : colimit (r.latchingDiagram X j) ⟶ X.obj j :=
  r.latchingMapWith X j (colimit.cocone _) (colimit.isColimit _)

/-- Every original latching injection retains its original direct arrow. -/
@[reassoc]
theorem latchingMap_ι (X : J ⥤ C) (j : J) (a : r.Latching j) :
    colimit.ι (r.latchingDiagram X j) a ≫ latchingMap r X j = X.map (r.latchingArrow a) :=
  r.latchingMapWith_ι X j (colimit.cocone _) (colimit.isColimit _) a

/-- All original coefficient transformations retain whole latching naturality. -/
@[reassoc]
theorem latchingMap_naturality {X Y : J ⥤ C} (f : X ⟶ Y) (j : J) :
    latchingMap r X j ≫ f.app j =
      colimMap (r.latchingTransformation f j) ≫ latchingMap r Y j :=
  r.latchingMapWith_naturality f j (colimit.cocone _) (colimit.isColimit _)
    (colimit.cocone _) (colimit.isColimit _)

end Latching

section Matching

variable [∀ j, HasLimitsOfShape (r.Matching j) C]

/-- The original matching map uses precisely its own actual limit shape. -/
def matchingMap (X : J ⥤ C) (j : J) : X.obj j ⟶ limit (r.matchingDiagram X j) :=
  r.matchingMapWith X j (limit.cone _) (limit.isLimit _)

/-- Every original matching projection retains its original inverse arrow. -/
@[reassoc]
theorem matchingMap_π (X : J ⥤ C) (j : J) (a : r.Matching j) :
    matchingMap r X j ≫ limit.π (r.matchingDiagram X j) a = X.map (r.matchingArrow a) :=
  r.matchingMapWith_π X j (limit.cone _) (limit.isLimit _) a

/-- All original coefficient transformations retain whole matching naturality. -/
@[reassoc]
theorem matchingMap_naturality {X Y : J ⥤ C} (f : X ⟶ Y) (j : J) :
    matchingMap r X j ≫ limMap (r.matchingTransformation f j) =
      f.app j ≫ matchingMap r Y j :=
  r.matchingMapWith_naturality f j (limit.cone _) (limit.isLimit _)
    (limit.cone _) (limit.isLimit _)

end Matching

end CategoryTheory.ReedyStructure

end ReedyPart7

section ReedyPart8

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] {X Y : J ⥤ C} (f : X ⟶ Y) (j : J)

section Latching

variable [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPushouts C]

/-- The original relative latching corner at the actual original coefficient object. -/
def latchingCorner :
    pushout (latchingMap r X j) (colimMap (r.latchingTransformation f j)) ⟶ Y.obj j :=
  pushout.desc (f.app j) (latchingMap r Y j) (latchingMap_naturality r f j)

/-- The first actual pushout injection retains the original coefficient map. -/
@[reassoc]
theorem latchingCorner_inl :
    pushout.inl (latchingMap r X j) (colimMap (r.latchingTransformation f j)) ≫
      latchingCorner r f j = f.app j := pushout.inl_desc _ _ _

/-- The second actual pushout injection retains the complete original latching map. -/
@[reassoc]
theorem latchingCorner_inr :
    pushout.inr (latchingMap r X j) (colimMap (r.latchingTransformation f j)) ≫
      latchingCorner r f j = latchingMap r Y j := pushout.inr_desc _ _ _

end Latching

section Matching

variable [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPullbacks C]

/-- The original relative matching corner at the actual original coefficient object. -/
def matchingCorner :
    X.obj j ⟶ pullback (limMap (r.matchingTransformation f j)) (matchingMap r Y j) :=
  pullback.lift (matchingMap r X j) (f.app j) (matchingMap_naturality r f j)

/-- The first actual pullback projection retains the complete original matching map. -/
@[reassoc]
theorem matchingCorner_fst :
    matchingCorner r f j ≫ pullback.fst (limMap (r.matchingTransformation f j))
      (matchingMap r Y j) = matchingMap r X j := pullback.lift_fst _ _ _

/-- The second actual pullback projection retains the original coefficient map. -/
@[reassoc]
theorem matchingCorner_snd :
    matchingCorner r f j ≫ pullback.snd (limMap (r.matchingTransformation f j))
      (matchingMap r Y j) = f.app j := pullback.lift_snd _ _ _

end Matching

end CategoryTheory.ReedyStructure

end ReedyPart8
