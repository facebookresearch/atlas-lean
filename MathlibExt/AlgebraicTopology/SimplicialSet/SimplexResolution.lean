/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanAugmentation
public import MathlibExt.AlgebraicTopology.SimplicialSet.LeftFiber

/-!
# Simplicial resolution by pullbacks over all simplices

For `p : Z ⟶ Y`, the category of simplices of `Y` indexes the pullbacks of
`p` along all representing standard-simplex maps. Their Bousfield--Kan carrier
is the simplex resolution of `p`. Triangles over `Y` induce strict maps of
diagrams and resolutions.

Using the generic Bousfield--Kan augmentation, the pullback diagram is
augmented by its first projection. This file proves only carrier,
functoriality, projection, resolution-specific augmentation, and left-fiber
computation laws. It makes no contraction, weak-equivalence, realization,
Quillen Theorem A, or Waldhausen additivity claim.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial

universe u

namespace SSet

/-- The category of simplices of `Y`, in its costructured-arrow presentation. -/
abbrev SimplexIndex (Y : SSet.{u}) :=
  CostructuredArrow SSet.stdSimplex.{u} Y

/-- Canonical map between pullbacks induced by a morphism of represented
simplices. -/
noncomputable def simplexPullbackMap {Z Y : SSet.{u}} (p : Z ⟶ Y)
    {s t : SimplexIndex Y} (u : s ⟶ t) :
    pullback p s.hom ⟶ pullback p t.hom :=
  pullback.lift (pullback.fst p s.hom)
    (pullback.snd p s.hom ≫ SSet.stdSimplex.map u.left) (by
      rw [Category.assoc, CostructuredArrow.w u]
      exact pullback.condition)

@[reassoc (attr := simp)]
theorem simplexPullbackMap_fst {Z Y : SSet.{u}} (p : Z ⟶ Y)
    {s t : SimplexIndex Y} (u : s ⟶ t) :
    simplexPullbackMap p u ≫ pullback.fst p t.hom =
      pullback.fst p s.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem simplexPullbackMap_snd {Z Y : SSet.{u}} (p : Z ⟶ Y)
    {s t : SimplexIndex Y} (u : s ⟶ t) :
    simplexPullbackMap p u ≫ pullback.snd p t.hom =
      pullback.snd p s.hom ≫ SSet.stdSimplex.map u.left :=
  pullback.lift_snd _ _ _

/-- Diagram of pullbacks of `p : Z ⟶ Y` along all simplices of `Y`. -/
noncomputable def simplexPullbackDiagram {Z Y : SSet.{u}} (p : Z ⟶ Y) :
    SimplexIndex Y ⥤ SSet.{u} where
  obj s := pullback p s.hom
  map u := simplexPullbackMap p u
  map_id s := by
    apply pullback.hom_ext
    · exact (simplexPullbackMap_fst p (𝟙 s)).trans
        (Category.id_comp _).symm
    · have hleft : (𝟙 s : s ⟶ s).left = 𝟙 s.left := rfl
      calc
        simplexPullbackMap p (𝟙 s) ≫ pullback.snd p s.hom =
            pullback.snd p s.hom ≫
              SSet.stdSimplex.map ((𝟙 s : s ⟶ s).left) :=
          simplexPullbackMap_snd p (𝟙 s)
        _ = pullback.snd p s.hom ≫ SSet.stdSimplex.map (𝟙 s.left) := by rw [hleft]
        _ = pullback.snd p s.hom ≫ 𝟙 _ :=
          congrArg (pullback.snd p s.hom ≫ ·)
            (SSet.stdSimplex.map_id s.left)
        _ = pullback.snd p s.hom := Category.comp_id _
        _ = 𝟙 _ ≫ pullback.snd p s.hom := (Category.id_comp _).symm
  map_comp {s t r} u v := by
    apply pullback.hom_ext
    · calc
        simplexPullbackMap p (u ≫ v) ≫ pullback.fst p r.hom =
            pullback.fst p s.hom := simplexPullbackMap_fst p (u ≫ v)
        _ = simplexPullbackMap p u ≫ pullback.fst p t.hom :=
          (simplexPullbackMap_fst p u).symm
        _ = simplexPullbackMap p u ≫
            (simplexPullbackMap p v ≫ pullback.fst p r.hom) :=
          congrArg (simplexPullbackMap p u ≫ ·)
            (simplexPullbackMap_fst p v).symm
        _ = (simplexPullbackMap p u ≫ simplexPullbackMap p v) ≫
            pullback.fst p r.hom := (Category.assoc _ _ _).symm
    · have hleft : (u ≫ v).left = u.left ≫ v.left := rfl
      calc
        simplexPullbackMap p (u ≫ v) ≫ pullback.snd p r.hom =
            pullback.snd p s.hom ≫ SSet.stdSimplex.map (u ≫ v).left :=
          simplexPullbackMap_snd p (u ≫ v)
        _ = pullback.snd p s.hom ≫
            SSet.stdSimplex.map (u.left ≫ v.left) := by rw [hleft]
        _ = pullback.snd p s.hom ≫
            (SSet.stdSimplex.map u.left ≫ SSet.stdSimplex.map v.left) :=
          congrArg (pullback.snd p s.hom ≫ ·) (Functor.map_comp _ _ _)
        _ = (pullback.snd p s.hom ≫ SSet.stdSimplex.map u.left) ≫
            SSet.stdSimplex.map v.left := (Category.assoc _ _ _).symm
        _ = (simplexPullbackMap p u ≫ pullback.snd p t.hom) ≫
            SSet.stdSimplex.map v.left :=
          congrArg (· ≫ SSet.stdSimplex.map v.left)
            (simplexPullbackMap_snd p u).symm
        _ = simplexPullbackMap p u ≫
            (pullback.snd p t.hom ≫ SSet.stdSimplex.map v.left) :=
          Category.assoc _ _ _
        _ = simplexPullbackMap p u ≫
            (simplexPullbackMap p v ≫ pullback.snd p r.hom) :=
          congrArg (simplexPullbackMap p u ≫ ·)
            (simplexPullbackMap_snd p v).symm
        _ = (simplexPullbackMap p u ≫ simplexPullbackMap p v) ≫
            pullback.snd p r.hom := (Category.assoc _ _ _).symm

/-- Reindexing in the simplex category preserves the source projection. -/
@[reassoc]
theorem simplexPullbackDiagram_map_fst {Z Y : SSet.{u}} (p : Z ⟶ Y)
    {s t : SimplexIndex Y} (u : s ⟶ t) :
    (simplexPullbackDiagram p).map u ≫ pullback.fst p t.hom =
      pullback.fst p s.hom := by
  exact simplexPullbackMap_fst p u

/-- Reindexing in the simplex category postcomposes the standard-simplex
projection by the underlying simplex-category map. -/
@[reassoc]
theorem simplexPullbackDiagram_map_snd {Z Y : SSet.{u}} (p : Z ⟶ Y)
    {s t : SimplexIndex Y} (u : s ⟶ t) :
    (simplexPullbackDiagram p).map u ≫ pullback.snd p t.hom =
      pullback.snd p s.hom ≫ SSet.stdSimplex.map u.left := by
  exact simplexPullbackMap_snd p u

/-- Canonical map between pullbacks induced by a commuting triangle over the
same target. -/
noncomputable def simplexPullbackTriangleMap
    {Z Z' Y : SSet.{u}} {p : Z ⟶ Y} {q : Z' ⟶ Y}
    (u : Z ⟶ Z') (hu : u ≫ q = p) (s : SimplexIndex Y) :
    pullback p s.hom ⟶ pullback q s.hom :=
  pullback.lift (pullback.fst p s.hom ≫ u)
    (pullback.snd p s.hom) (by
      calc
        (pullback.fst p s.hom ≫ u) ≫ q =
            pullback.fst p s.hom ≫ (u ≫ q) := Category.assoc _ _ _
        _ = pullback.fst p s.hom ≫ p := by rw [hu]
        _ = pullback.snd p s.hom ≫ s.hom := pullback.condition)

@[reassoc (attr := simp)]
theorem simplexPullbackTriangleMap_fst
    {Z Z' Y : SSet.{u}} {p : Z ⟶ Y} {q : Z' ⟶ Y}
    (u : Z ⟶ Z') (hu : u ≫ q = p) (s : SimplexIndex Y) :
    simplexPullbackTriangleMap u hu s ≫ pullback.fst q s.hom =
      pullback.fst p s.hom ≫ u :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem simplexPullbackTriangleMap_snd
    {Z Z' Y : SSet.{u}} {p : Z ⟶ Y} {q : Z' ⟶ Y}
    (u : Z ⟶ Z') (hu : u ≫ q = p) (s : SimplexIndex Y) :
    simplexPullbackTriangleMap u hu s ≫ pullback.snd q s.hom =
      pullback.snd p s.hom :=
  pullback.lift_snd _ _ _

/-- A commuting triangle over `Y` induces a map of simplex pullback diagrams. -/
noncomputable def simplexPullbackDiagramMap
    {Z Z' Y : SSet.{u}} {p : Z ⟶ Y} {q : Z' ⟶ Y}
    (u : Z ⟶ Z') (hu : u ≫ q = p) :
    simplexPullbackDiagram p ⟶ simplexPullbackDiagram q where
  app s := simplexPullbackTriangleMap u hu s
  naturality {s t} k := by
    change simplexPullbackMap p k ≫ simplexPullbackTriangleMap u hu t =
      simplexPullbackTriangleMap u hu s ≫ simplexPullbackMap q k
    apply pullback.hom_ext
    · calc
        (simplexPullbackMap p k ≫ simplexPullbackTriangleMap u hu t) ≫
            pullback.fst q t.hom =
          simplexPullbackMap p k ≫
            (simplexPullbackTriangleMap u hu t ≫ pullback.fst q t.hom) :=
          Category.assoc _ _ _
        _ = simplexPullbackMap p k ≫ (pullback.fst p t.hom ≫ u) :=
          congrArg (simplexPullbackMap p k ≫ ·)
            (simplexPullbackTriangleMap_fst u hu t)
        _ = (simplexPullbackMap p k ≫ pullback.fst p t.hom) ≫ u :=
          (Category.assoc _ _ _).symm
        _ = pullback.fst p s.hom ≫ u :=
          congrArg (· ≫ u) (simplexPullbackMap_fst p k)
        _ = simplexPullbackTriangleMap u hu s ≫ pullback.fst q s.hom :=
          (simplexPullbackTriangleMap_fst u hu s).symm
        _ = simplexPullbackTriangleMap u hu s ≫
            (simplexPullbackMap q k ≫ pullback.fst q t.hom) :=
          congrArg (simplexPullbackTriangleMap u hu s ≫ ·)
            (simplexPullbackMap_fst q k).symm
        _ = (simplexPullbackTriangleMap u hu s ≫ simplexPullbackMap q k) ≫
            pullback.fst q t.hom := (Category.assoc _ _ _).symm
    · calc
        (simplexPullbackMap p k ≫ simplexPullbackTriangleMap u hu t) ≫
            pullback.snd q t.hom =
          simplexPullbackMap p k ≫
            (simplexPullbackTriangleMap u hu t ≫ pullback.snd q t.hom) :=
          Category.assoc _ _ _
        _ = simplexPullbackMap p k ≫ pullback.snd p t.hom :=
          congrArg (simplexPullbackMap p k ≫ ·)
            (simplexPullbackTriangleMap_snd u hu t)
        _ = pullback.snd p s.hom ≫ SSet.stdSimplex.map k.left :=
          simplexPullbackMap_snd p k
        _ = simplexPullbackTriangleMap u hu s ≫
            pullback.snd q s.hom ≫ SSet.stdSimplex.map k.left :=
          congrArg (· ≫ SSet.stdSimplex.map k.left)
            (simplexPullbackTriangleMap_snd u hu s).symm
        _ = simplexPullbackTriangleMap u hu s ≫
            (pullback.snd q s.hom ≫ SSet.stdSimplex.map k.left) := rfl
        _ = simplexPullbackTriangleMap u hu s ≫
            (simplexPullbackMap q k ≫ pullback.snd q t.hom) :=
          congrArg (simplexPullbackTriangleMap u hu s ≫ ·)
            (simplexPullbackMap_snd q k).symm
        _ = (simplexPullbackTriangleMap u hu s ≫ simplexPullbackMap q k) ≫
            pullback.snd q t.hom := (Category.assoc _ _ _).symm

/-- The triangle map applies `u` to the source projection. -/
@[reassoc]
theorem simplexPullbackDiagramMap_app_fst
    {Z Z' Y : SSet.{u}} {p : Z ⟶ Y} {q : Z' ⟶ Y}
    (u : Z ⟶ Z') (hu : u ≫ q = p) (s : SimplexIndex Y) :
    (simplexPullbackDiagramMap u hu).app s ≫ pullback.fst q s.hom =
      pullback.fst p s.hom ≫ u := by
  exact simplexPullbackTriangleMap_fst u hu s

/-- The triangle map preserves the standard-simplex projection. -/
@[reassoc]
theorem simplexPullbackDiagramMap_app_snd
    {Z Z' Y : SSet.{u}} {p : Z ⟶ Y} {q : Z' ⟶ Y}
    (u : Z ⟶ Z') (hu : u ≫ q = p) (s : SimplexIndex Y) :
    (simplexPullbackDiagramMap u hu).app s ≫ pullback.snd q s.hom =
      pullback.snd p s.hom := by
  exact simplexPullbackTriangleMap_snd u hu s

/-- The diagram map of an identity triangle is the identity. -/
@[simp]
theorem simplexPullbackDiagramMap_id {Z Y : SSet.{u}} (p : Z ⟶ Y) :
    simplexPullbackDiagramMap (𝟙 Z) (by simp) =
      𝟙 (simplexPullbackDiagram p) := by
  apply NatTrans.ext
  funext s
  let hid : 𝟙 Z ≫ p = p := by simp
  change simplexPullbackTriangleMap (𝟙 Z) hid s = 𝟙 (pullback p s.hom)
  apply pullback.hom_ext
  · calc
      simplexPullbackTriangleMap (𝟙 Z) hid s ≫ pullback.fst p s.hom =
          pullback.fst p s.hom ≫ 𝟙 Z :=
        simplexPullbackTriangleMap_fst (𝟙 Z) hid s
      _ = pullback.fst p s.hom := Category.comp_id _
      _ = 𝟙 _ ≫ pullback.fst p s.hom := (Category.id_comp _).symm
  · calc
      simplexPullbackTriangleMap (𝟙 Z) hid s ≫ pullback.snd p s.hom =
          pullback.snd p s.hom :=
        simplexPullbackTriangleMap_snd (𝟙 Z) hid s
      _ = 𝟙 _ ≫ pullback.snd p s.hom := (Category.id_comp _).symm

/-- Triangle maps compose strictly, in direct-to-iterated orientation. -/
theorem simplexPullbackDiagramMap_comp
    {Z₀ Z₁ Z₂ Y : SSet.{u}}
    {p₀ : Z₀ ⟶ Y} {p₁ : Z₁ ⟶ Y} {p₂ : Z₂ ⟶ Y}
    (u : Z₀ ⟶ Z₁) (v : Z₁ ⟶ Z₂)
    (hu : u ≫ p₁ = p₀) (hv : v ≫ p₂ = p₁) :
    simplexPullbackDiagramMap (u ≫ v) (by rw [Category.assoc, hv, hu]) =
      simplexPullbackDiagramMap u hu ≫ simplexPullbackDiagramMap v hv := by
  apply NatTrans.ext
  funext s
  let huv : (u ≫ v) ≫ p₂ = p₀ := by rw [Category.assoc, hv, hu]
  change simplexPullbackTriangleMap (u ≫ v) huv s =
    simplexPullbackTriangleMap u hu s ≫
      simplexPullbackTriangleMap v hv s
  apply pullback.hom_ext
  · calc
      simplexPullbackTriangleMap (u ≫ v) huv s ≫ pullback.fst p₂ s.hom =
          pullback.fst p₀ s.hom ≫ (u ≫ v) :=
        simplexPullbackTriangleMap_fst (u ≫ v) huv s
      _ = (pullback.fst p₀ s.hom ≫ u) ≫ v :=
        (Category.assoc _ _ _).symm
      _ = (simplexPullbackTriangleMap u hu s ≫ pullback.fst p₁ s.hom) ≫ v :=
        congrArg (· ≫ v) (simplexPullbackTriangleMap_fst u hu s).symm
      _ = simplexPullbackTriangleMap u hu s ≫
          (pullback.fst p₁ s.hom ≫ v) := Category.assoc _ _ _
      _ = simplexPullbackTriangleMap u hu s ≫
          (simplexPullbackTriangleMap v hv s ≫ pullback.fst p₂ s.hom) :=
        congrArg (simplexPullbackTriangleMap u hu s ≫ ·)
          (simplexPullbackTriangleMap_fst v hv s).symm
      _ = (simplexPullbackTriangleMap u hu s ≫
          simplexPullbackTriangleMap v hv s) ≫ pullback.fst p₂ s.hom :=
        (Category.assoc _ _ _).symm
  · calc
      simplexPullbackTriangleMap (u ≫ v) huv s ≫ pullback.snd p₂ s.hom =
          pullback.snd p₀ s.hom :=
        simplexPullbackTriangleMap_snd (u ≫ v) huv s
      _ = simplexPullbackTriangleMap u hu s ≫ pullback.snd p₁ s.hom :=
        (simplexPullbackTriangleMap_snd u hu s).symm
      _ = simplexPullbackTriangleMap u hu s ≫
          (simplexPullbackTriangleMap v hv s ≫ pullback.snd p₂ s.hom) :=
        congrArg (simplexPullbackTriangleMap u hu s ≫ ·)
          (simplexPullbackTriangleMap_snd v hv s).symm
      _ = (simplexPullbackTriangleMap u hu s ≫
          simplexPullbackTriangleMap v hv s) ≫ pullback.snd p₂ s.hom :=
        (Category.assoc _ _ _).symm

/-- The simplex object represented by `y`. -/
noncomputable def leftFiberSimplexIndex {Y : SSet.{u}} {m : ℕ}
    (y : Y _⦋m⦌) : SimplexIndex Y :=
  CostructuredArrow.mk (SSet.yonedaEquiv.symm y)

/-- At the simplex object represented by `y`, the pullback diagram is the
landed left fiber. -/
@[simp]
theorem simplexPullbackDiagram_obj_leftFiberSimplexIndex
    {Z Y : SSet.{u}} (p : Z ⟶ Y) {m : ℕ} (y : Y _⦋m⦌) :
    (simplexPullbackDiagram p).obj (leftFiberSimplexIndex y) =
      SSet.leftFiber p y :=
  rfl

/-- The source projection at a represented simplex is `leftFiber.π`. -/
@[simp]
theorem simplexPullbackDiagram_fst_leftFiberSimplexIndex
    {Z Y : SSet.{u}} (p : Z ⟶ Y) {m : ℕ} (y : Y _⦋m⦌) :
    pullback.fst p (leftFiberSimplexIndex y).hom =
      SSet.leftFiber.π p y :=
  rfl

/-- The standard-simplex projection at a represented simplex is
`leftFiber.toSimplex`. -/
@[simp]
theorem simplexPullbackDiagram_snd_leftFiberSimplexIndex
    {Z Y : SSet.{u}} (p : Z ⟶ Y) {m : ℕ} (y : Y _⦋m⦌) :
    pullback.snd p (leftFiberSimplexIndex y).hom =
      SSet.leftFiber.toSimplex p y :=
  rfl

/-- The simplex resolution of `p` is the Bousfield--Kan carrier of its
simplex pullback diagram. -/
noncomputable def simplexResolution {Z Y : SSet.{u}} (p : Z ⟶ Y) : SSet.{u} :=
  bkHocolim (simplexPullbackDiagram p)

/-- Map of simplex resolutions induced by a commuting triangle over the same
target. -/
noncomputable def simplexResolutionMap
    {Z Z' Y : SSet.{u}} {p : Z ⟶ Y} {q : Z' ⟶ Y}
    (u : Z ⟶ Z') (hu : u ≫ q = p) :
    simplexResolution p ⟶ simplexResolution q :=
  bkHocolimMap (simplexPullbackDiagramMap u hu)

/-- Identity triangles induce identity resolution maps. -/
@[simp]
theorem simplexResolutionMap_id {Z Y : SSet.{u}} (p : Z ⟶ Y) :
    simplexResolutionMap (𝟙 Z) (by simp) = 𝟙 (simplexResolution p) := by
  unfold simplexResolutionMap simplexResolution
  rw [simplexPullbackDiagramMap_id, bkHocolimMap_id]

/-- Composite triangles induce composite resolution maps. -/
theorem simplexResolutionMap_comp
    {Z₀ Z₁ Z₂ Y : SSet.{u}}
    {p₀ : Z₀ ⟶ Y} {p₁ : Z₁ ⟶ Y} {p₂ : Z₂ ⟶ Y}
    (u : Z₀ ⟶ Z₁) (v : Z₁ ⟶ Z₂)
    (hu : u ≫ p₁ = p₀) (hv : v ≫ p₂ = p₁) :
    simplexResolutionMap (u ≫ v) (by rw [Category.assoc, hv, hu]) =
      simplexResolutionMap u hu ≫ simplexResolutionMap v hv := by
  unfold simplexResolutionMap simplexResolution
  have hd := simplexPullbackDiagramMap_comp u v hu hv
  rw [hd, bkHocolimMap_comp]

/-- The first projections form the canonical cocone from the simplex pullback
diagram to its source. -/
noncomputable def simplexPullbackCocone
    {Z Y : SSet.{u}} (p : Z ⟶ Y) :
    simplexPullbackDiagram p ⟶
      (Functor.const (SimplexIndex Y)).obj Z where
  app s := pullback.fst p s.hom
  naturality {s t} u := by
    change simplexPullbackMap p u ≫ pullback.fst p t.hom =
      pullback.fst p s.hom ≫ ((Functor.const (SimplexIndex Y)).obj Z).map u
    calc
      simplexPullbackMap p u ≫ pullback.fst p t.hom =
          pullback.fst p s.hom := simplexPullbackMap_fst p u
      _ = pullback.fst p s.hom ≫
          ((Functor.const (SimplexIndex Y)).obj Z).map u := by
        rw [Functor.const_obj_map, Category.comp_id]

/-- Canonical augmentation from the simplex resolution to the source. -/
noncomputable def simplexResolutionAugmentation
    {Z Y : SSet.{u}} (p : Z ⟶ Y) :
    simplexResolution p ⟶ Z :=
  bkAugmentation (simplexPullbackCocone p)

/-- Resolution augmentations are natural in commuting triangles over `Y`. -/
@[reassoc]
theorem simplexResolutionAugmentation_naturality
    {Z Z' Y : SSet.{u}} {p : Z ⟶ Y} {q : Z' ⟶ Y}
    (u : Z ⟶ Z') (hu : u ≫ q = p) :
    simplexResolutionMap u hu ≫ simplexResolutionAugmentation q =
      simplexResolutionAugmentation p ≫ u := by
  apply bkAugmentation_naturality
  intro s
  exact simplexPullbackDiagramMap_app_fst u hu s

end SSet

end
