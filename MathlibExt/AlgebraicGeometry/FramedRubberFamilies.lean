/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RubberModuliStackModels
public import MathlibExt.AlgebraicGeometry.RubberStandardScalingModels

/-!
# Actual standard-target frames on rubber families

A frame is the actual isomorphism to a pulled standard length-m target,
preserving its projection, contraction and boundary. Framed arrows preserve
the full target coordinate map, parameter, source curve and all marks.
Base changes retain the actual source/target Cartesian squares.

The group action relation changes the parameter and target map by the
literal standard torus action, with the native source curve isomorphism
and all markings fixed. Source: Jun Li arXiv:math/0009097v1, Section4;
JPPZ arXiv:1602.04705v2, Section0.2.4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.FramedRubberFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open CoherentCurveLinearSeries RelativeProjectiveLineModels ExpandedTargetChainGeometry
open StandardRelativeExpansionModels ExpandedRelativeFamilies ExpansionParameterModels
open RubberMapFamilies RubberStandardScalingModels

variable {k : Type} [Field k]
  (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
  (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
  (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
  (m : ℕ) {g n : ℕ} (a : Fin n → ℤ)

structure Family (T : Over (Spec (.of k))) where
  rubber : RubberFamily O P D R S T g n a
  parameter : T ⟶ ParameterSpace k m
  frame : rubber.target.StandardFrame m parameter

variable {T : Over (Spec (.of k))}

def targetMap (F : Family O P D R S m (g := g) a T) : F.rubber.target.scheme ⟶ (S.chart m).scheme :=
  F.frame.comparison.hom ≫ pullback.fst (S.chart m).projection F.parameter

def totalMap (F : Family O P D R S m (g := g) a T) : F.rubber.curve.X ⟶ (S.chart m).scheme.left :=
  F.rubber.map ≫ (targetMap O P D R S m a F).left

theorem targetMap_projection (F : Family O P D R S m (g := g) a T) :
    targetMap O P D R S m a F ≫ (S.chart m).projection = F.rubber.target.projection ≫ F.parameter := by
  dsimp [targetMap]
  rw [Category.assoc, pullback.condition, ← Category.assoc, F.frame.projection]

theorem totalMap_over (F : Family O P D R S m (g := g) a T) :
    totalMap O P D R S m a F ≫ (S.chart m).projection.left = F.rubber.curve.π ≫ F.parameter.left := by
  have h := congrArg Over.Hom.left (targetMap_projection O P D R S m a F)
  dsimp only [Over.comp_left] at h
  rw [totalMap, Category.assoc, h, ← Category.assoc, F.rubber.over]

structure Hom (F H : Family O P D R S m (g := g) a T) where
  iso : RubberIso O P D R S F.rubber H.rubber
  parameter : F.parameter = H.parameter
  frame : iso.target.iso.hom ≫ targetMap O P D R S m a H = targetMap O P D R S m a F

@[ext] theorem Hom.ext {F H : Family O P D R S m (g := g) a T} (e h : Hom O P D R S m a F H)
    (same : e.iso = h.iso) : e = h := by cases e; cases h; cases same; rfl

instance familyGroupoid (T : Over (Spec (.of k))) : Groupoid (Family O P D R S m (g := g) a T) where
  Hom F H := Hom O P D R S m a F H
  id F := ⟨@CategoryStruct.id (RubberFamily O P D R S T g n a) inferInstance F.rubber, rfl, by
    change 𝟙 F.rubber.target.scheme ≫ targetMap O P D R S m a F = _
    simp⟩
  comp {F H K} e h := ⟨@CategoryStruct.comp (RubberFamily O P D R S T g n a)
      inferInstance F.rubber H.rubber K.rubber e.iso h.iso, e.parameter.trans h.parameter, by
    change (e.iso.target.iso.hom ≫ h.iso.target.iso.hom) ≫ _ = _
    rw [Category.assoc, h.frame, e.frame]⟩
  inv {F H} e := ⟨@Groupoid.inv (RubberFamily O P D R S T g n a) inferInstance F.rubber H.rubber e.iso,
      e.parameter.symm, by
    change e.iso.target.iso.inv ≫ targetMap O P D R S m a _ = _
    rw [← e.frame]
    simp⟩
  id_comp {X Y} e := by
    apply Hom.ext
    exact @Category.id_comp (RubberFamily O P D R S T g n a) inferInstance X.rubber Y.rubber e.iso
  comp_id {X Y} e := by
    apply Hom.ext
    exact @Category.comp_id (RubberFamily O P D R S T g n a) inferInstance X.rubber Y.rubber e.iso
  assoc {W X Y Z} e h j := by
    apply Hom.ext
    exact @Category.assoc (RubberFamily O P D R S T g n a) inferInstance
      W.rubber X.rubber Y.rubber Z.rubber e.iso h.iso j.iso
  inv_comp {X Y} e := by
    apply Hom.ext
    exact @Groupoid.inv_comp (RubberFamily O P D R S T g n a) inferInstance X.rubber Y.rubber e.iso
  comp_inv {X Y} e := by
    apply Hom.ext
    exact @Groupoid.comp_inv (RubberFamily O P D R S T g n a) inferInstance X.rubber Y.rubber e.iso

def forget (T : Over (Spec (.of k))) : Family O P D R S m (g := g) a T ⥤ RubberFamily O P D R S T g n a where
  obj F := F.rubber
  map {F H} e := (show Hom O P D R S m a F H from e).iso
  map_id _F := rfl
  map_comp _e _h := rfl

def stable (T : Over (Spec (.of k))) : ObjectProperty (Family O P D R S m (g := g) a T) :=
  fun F => IsStableRubber O P D R S F.rubber

abbrev StableFamily (T : Over (Spec (.of k))) := (stable O P D R S m (g := g) a T).FullSubcategory

structure BaseChange {T U : Over (Spec (.of k))} (h : T ⟶ U)
    (F : Family O P D R S m (g := g) a T) (H : Family O P D R S m (g := g) a U) where
  rubber : RubberModuliStackModels.FamilyBaseChange O P D R S a h F.rubber H.rubber
  parameter : F.parameter = h ≫ H.parameter
  frame : rubber.target ≫ targetMap O P D R S m a H = targetMap O P D R S m a F

variable (H : TorusTheory k (m + 1)) (N : StandardAction O P D R S m H)

def curveOver (F : Family O P D R S m (g := g) a T) : Over (Spec (.of k)) := Over.mk (F.rubber.curve.π ≫ T.hom)

def curveProjection (F : Family O P D R S m (g := g) a T) : curveOver O P D R S m a F ⟶ T :=
  Over.homMk F.rubber.curve.π rfl

def totalOver (F : Family O P D R S m (g := g) a T) : curveOver O P D R S m a F ⟶ (S.chart m).scheme :=
  Over.homMk (totalMap O P D R S m a F) (by
    have h := (Over.w F.parameter)
    have hs := Over.w (S.chart m).projection
    rw [← hs, ← Category.assoc, totalMap_over, Category.assoc, h]
    rfl)

structure ScalingRelation (u : T ⟶ torusScheme k (m + 1))
    (F G : Family O P D R S m (g := g) a T) where
  source : F.rubber.curve.X ≅ G.rubber.curve.X
  over : source.hom ≫ G.rubber.curve.π = F.rubber.curve.π
  markings : ∀ i : Fin n, F.rubber.curve.marking i ≫ source.hom = G.rubber.curve.marking i
  parameter : letI := H.group; letI := N.parameter;
    G.parameter = CartesianMonoidalCategory.lift u F.parameter ≫ γ[torusScheme k (m + 1),ParameterSpace k m]
  map : letI := H.group; letI := N.standard;
    source.hom ≫ totalMap O P D R S m a G =
      (CartesianMonoidalCategory.lift (curveProjection O P D R S m a F ≫ u)
        (totalOver O P D R S m a F) ≫ γ[torusScheme k (m + 1),(S.chart m).scheme]).left

end MathlibExt.AlgebraicGeometry.FramedRubberFamilies
