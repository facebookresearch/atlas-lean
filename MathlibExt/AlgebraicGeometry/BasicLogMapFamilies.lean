/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LogCurveFamilies
public import MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
public import MathlibExt.AlgebraicGeometry.RingedSiteLogMorphisms
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Stable log maps and their actual basicization category

The ordinary stable family is fixed. Enhancements are actual fine saturated
log structures on the same base and curve, with their native projection,
target and base maps. Their comparisons to the original logs are actual
fixed-ring monoid sheaf maps. The commuting triangles are specified on those
maps, so changing the underlying curve or supplying a Basic predicate is
not part of this construction.

Basicization is the initial object in this concrete enhancement category,
with the resulting universal-minimal family. This is the universal-property
form of Gross--Siebert arXiv:1102.4322v2, Proposition1.24; its geometric
point comparison with Construction1.16/Definition1.20 is a separate
normalized ghost-presentation contract. No enhancement exists for an
arbitrary ordinary map merely by definition: the input is an actual stable
log map.
-/

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.BasicLogMapFamilies
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.EtaleLogSchemes
open MathlibExt.AlgebraicGeometry.EtaleLogDiagrams
open MathlibExt.AlgebraicGeometry.SmallEtaleGeometry
open MathlibExt.AlgebraicGeometry.FormalLogSmoothness
open MathlibExt.AlgebraicGeometry.LogCurveFamilies
open MathlibExt.AlgebraicGeometry.LogStructures

variable [InverseImageTheory.{0}]

/-- An actual stable log-map family over an arbitrary fixed relative target. -/
structure StableLogMap {X S : LogScheme.{0}} (q : EtaleLogSchemes.Hom X S)
    (n g : ℕ) (T : Scheme.{0}) (b : T ⟶ S.scheme) where
  family : GeneralStableMapFamilies.Family q.map n g T b
  stable : GeneralStableMapFamilies.IsGeometricallyStable family
  curve : LogCurve family.curve
  baseMap : MorphismAlong ⟨T,curve.baseLog⟩ S b
  targetMap : MorphismAlong ⟨family.curve.X,curve.curveLog⟩ X family.map
  square : Square
    (homOfAlong ⟨family.curve.X,curve.curveLog⟩ X family.map targetMap) q
    (homOfAlong ⟨family.curve.X,curve.curveLog⟩ ⟨T,curve.baseLog⟩ family.curve.π curve.projection)
    (homOfAlong ⟨T,curve.baseLog⟩ S b baseMap)

variable {X S : LogScheme.{0}} {q : EtaleLogSchemes.Hom X S} {n g : ℕ}
    {T : Scheme.{0}} {b : T ⟶ S.scheme}

/-- The fixed native monoid-sheaf direct image, with its site universe explicit. -/
abbrev pushMonoids {A B : Scheme.{0}} (f : A ⟶ B) :=
  (etaleBaseChange f).sheafPushforwardContinuous CommMonCat.{1}
    B.smallEtaleTopology A.smallEtaleTopology

/-- A log enhancement on exactly the same ordinary stable map and curve.
All compatibility maps are actual ringed-site arrows. -/
structure Enhancement (M : StableLogMap q n g T b) where
  curve : LogCurve M.family.curve
  baseMap : MorphismAlong ⟨T,curve.baseLog⟩ S b
  targetMap : MorphismAlong ⟨M.family.curve.X,curve.curveLog⟩ X M.family.map
  square : Square
    (homOfAlong ⟨M.family.curve.X,curve.curveLog⟩ X M.family.map targetMap) q
    (homOfAlong ⟨M.family.curve.X,curve.curveLog⟩ ⟨T,curve.baseLog⟩ M.family.curve.π curve.projection)
    (homOfAlong ⟨T,curve.baseLog⟩ S b baseMap)
  baseComparison : curve.baseLog ⟶ M.curve.baseLog
  curveComparison : curve.curveLog ⟶ M.curve.curveLog
  projection : baseComparison.hom.left ≫ M.curve.projection.left =
    curve.projection.left ≫
      ((etaleBaseChange M.family.curve.π).sheafPushforwardContinuous CommMonCat
        T.smallEtaleTopology M.family.curve.X.smallEtaleTopology).map curveComparison.hom.left
  base : baseMap.left ≫
    ((etaleBaseChange b).sheafPushforwardContinuous CommMonCat
      S.scheme.smallEtaleTopology T.smallEtaleTopology).map baseComparison.hom.left = M.baseMap.left
  target : targetMap.left ≫
    ((etaleBaseChange M.family.map).sheafPushforwardContinuous CommMonCat
      X.scheme.smallEtaleTopology M.family.curve.X.smallEtaleTopology).map curveComparison.hom.left =
        M.targetMap.left

namespace Enhancement
variable {M : StableLogMap q n g T b}

structure Hom (E F : Enhancement M) where
  baseMap : E.curve.baseLog ⟶ F.curve.baseLog
  curveMap : E.curve.curveLog ⟶ F.curve.curveLog
  projection : baseMap.hom.left ≫ F.curve.projection.left =
    E.curve.projection.left ≫
      ((etaleBaseChange M.family.curve.π).sheafPushforwardContinuous CommMonCat
        T.smallEtaleTopology M.family.curve.X.smallEtaleTopology).map curveMap.hom.left
  base : E.baseMap.left ≫
    ((etaleBaseChange b).sheafPushforwardContinuous CommMonCat
      S.scheme.smallEtaleTopology T.smallEtaleTopology).map baseMap.hom.left = F.baseMap.left
  target : E.targetMap.left ≫
    ((etaleBaseChange M.family.map).sheafPushforwardContinuous CommMonCat
      X.scheme.smallEtaleTopology M.family.curve.X.smallEtaleTopology).map curveMap.hom.left = F.targetMap.left
  baseComparison : baseMap ≫ F.baseComparison = E.baseComparison
  curveComparison : curveMap ≫ F.curveComparison = E.curveComparison

@[ext] theorem Hom.ext {E F : Enhancement M} {a b : Hom E F}
    (hb : a.baseMap = b.baseMap) (hc : a.curveMap = b.curveMap) : a = b := by
  cases a; cases b; cases hb; cases hc; rfl

instance : Category (Enhancement M) where
  Hom E F := Hom E F
  id E :=
    { baseMap := 𝟙 _
      curveMap := 𝟙 _
      projection := by
        change (𝟙 _) ≫ E.curve.projection.left = E.curve.projection.left ≫
          (pushMonoids M.family.curve.π).map (𝟙 _)
        simp
      base := by
        change E.baseMap.left ≫ (pushMonoids b).map (𝟙 _) = E.baseMap.left
        simp
      target := by
        change E.targetMap.left ≫ (pushMonoids M.family.map).map (𝟙 _) = E.targetMap.left
        simp
      baseComparison := by simp
      curveComparison := by simp }
  comp a c :=
    { baseMap := a.baseMap ≫ c.baseMap
      curveMap := a.curveMap ≫ c.curveMap
      projection := by
        change (a.baseMap.hom.left ≫ c.baseMap.hom.left) ≫ _ =
          _ ≫ (pushMonoids M.family.curve.π).map (a.curveMap.hom.left ≫ c.curveMap.hom.left)
        rw [Category.assoc, c.projection, ← Category.assoc, a.projection,
          Category.assoc, ← _root_.CategoryTheory.Functor.map_comp]
      base := by
        change _ ≫ (pushMonoids b).map (a.baseMap.hom.left ≫ c.baseMap.hom.left) = _
        rw [_root_.CategoryTheory.Functor.map_comp, ← Category.assoc, a.base, c.base]
      target := by
        change _ ≫ (pushMonoids M.family.map).map (a.curveMap.hom.left ≫ c.curveMap.hom.left) = _
        rw [_root_.CategoryTheory.Functor.map_comp, ← Category.assoc, a.target, c.target]
      baseComparison := by rw [Category.assoc, c.baseComparison, a.baseComparison]
      curveComparison := by rw [Category.assoc, c.curveComparison, a.curveComparison] }
  id_comp a := by apply Hom.ext <;> simp
  comp_id a := by apply Hom.ext <;> simp
  assoc a c d := by apply Hom.ext <;> exact Category.assoc _ _ _

/-- The actual enhanced log family, retaining the original underlying maps. -/
def toStableLogMap (E : Enhancement M) : StableLogMap q n g T b :=
  ⟨M.family, M.stable, E.curve, E.baseMap, E.targetMap, E.square⟩

end Enhancement

/-- The existing family as its identity enhancement. -/
def identityEnhancement (M : StableLogMap q n g T b) : Enhancement M where
  curve := M.curve
  baseMap := M.baseMap
  targetMap := M.targetMap
  square := M.square
  baseComparison := 𝟙 _
  curveComparison := 𝟙 _
  projection := by
        change (𝟙 _) ≫ M.curve.projection.left = M.curve.projection.left ≫
          (pushMonoids M.family.curve.π).map (𝟙 _)
        simp
  base := by
        change M.baseMap.left ≫ (pushMonoids b).map (𝟙 _) = M.baseMap.left
        simp
  target := by
        change M.targetMap.left ≫ (pushMonoids M.family.map).map (𝟙 _) = M.targetMap.left
        simp

/-- Universal-minimality, on the actual enhancement category. Its source
comparison with the explicit geometric basic monoid remains named separately. -/
def IsUniversallyMinimal (M : StableLogMap q n g T b) : Prop :=
  Nonempty (IsInitial (identityEnhancement M))

/-- A basicization of a stable log map $M$ (log structures on small étale sites, with the inverse
images of the given `InverseImageTheory`): an enhancement $E$ of $M$, that is, a log curve
structure on the same underlying stable map with log maps to the base and the target and
comparison maps to the log structures of $M$ compatible with them, given as an initial object of
the category of enhancements of $M$, such that the stable log map defined by $E$ is universally
minimal: its identity enhancement is initial among its own enhancements. -/
structure Basicization (M : StableLogMap q n g T b) where
  enhancement : Enhancement M
  initial : IsInitial enhancement
  minimal : IsUniversallyMinimal enhancement.toStableLogMap

end MathlibExt.AlgebraicGeometry.BasicLogMapFamilies
