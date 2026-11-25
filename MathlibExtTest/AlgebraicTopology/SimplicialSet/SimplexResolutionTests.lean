/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexResolution

/-!
# Simplex-resolution tests

These tests pin the category-of-simplices variance, both pullback
projections, triangle functoriality, represented left fibers, and strict
resolution-augmentation naturality. They make no contraction,
weak-equivalence, realization, or Theorem A claim.
-/

open CategoryTheory Limits Opposite Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.SimplexResolutionTests

universe u

variable {Z Z' Z'' Y : SSet.{u}}
variable {p : Z ⟶ Y} {q : Z' ⟶ Y} {r : Z'' ⟶ Y}

example : Type u := SSet.SimplexIndex Y

#synth Category.{0} (SSet.SimplexIndex Y)

/-- The diagram has the intended category-of-simplices type. -/
noncomputable example : SSet.SimplexIndex Y ⥤ SSet.{u} :=
  SSet.simplexPullbackDiagram p

/-- Reindexing preserves the first projection and postcomposes the second. -/
example {s t : SSet.SimplexIndex Y} (k : s ⟶ t) :
    (SSet.simplexPullbackDiagram p).map k ≫ pullback.fst p t.hom =
        pullback.fst p s.hom ∧
      (SSet.simplexPullbackDiagram p).map k ≫ pullback.snd p t.hom =
        pullback.snd p s.hom ≫ SSet.stdSimplex.map k.left :=
  ⟨SSet.simplexPullbackDiagram_map_fst p k,
    SSet.simplexPullbackDiagram_map_snd p k⟩

/-- A commuting triangle acts on the first projection and fixes the second. -/
example (u : Z ⟶ Z') (hu : u ≫ q = p) (s : SSet.SimplexIndex Y) :
    (SSet.simplexPullbackDiagramMap u hu).app s ≫ pullback.fst q s.hom =
        pullback.fst p s.hom ≫ u ∧
      (SSet.simplexPullbackDiagramMap u hu).app s ≫ pullback.snd q s.hom =
        pullback.snd p s.hom :=
  ⟨SSet.simplexPullbackDiagramMap_app_fst u hu s,
    SSet.simplexPullbackDiagramMap_app_snd u hu s⟩

/-- Diagram maps preserve identities and composition strictly. -/
example (u : Z ⟶ Z') (v : Z' ⟶ Z'')
    (hu : u ≫ q = p) (hv : v ≫ r = q) :
    SSet.simplexPullbackDiagramMap (𝟙 Z) (by simp) =
        𝟙 (SSet.simplexPullbackDiagram p) ∧
      SSet.simplexPullbackDiagramMap (u ≫ v)
          (by rw [Category.assoc, hv, hu]) =
        SSet.simplexPullbackDiagramMap u hu ≫
          SSet.simplexPullbackDiagramMap v hv :=
  ⟨SSet.simplexPullbackDiagramMap_id p,
    SSet.simplexPullbackDiagramMap_comp u v hu hv⟩

/-- At a represented simplex the diagram object and projections are the
landed left-fiber APIs. -/
example {m : ℕ} (y : Y _⦋m⦌) :
    (SSet.simplexPullbackDiagram p).obj
          (SSet.leftFiberSimplexIndex y) = SSet.leftFiber p y ∧
      pullback.fst p (SSet.leftFiberSimplexIndex y).hom =
          SSet.leftFiber.π p y ∧
      pullback.snd p (SSet.leftFiberSimplexIndex y).hom =
          SSet.leftFiber.toSimplex p y :=
  ⟨SSet.simplexPullbackDiagram_obj_leftFiberSimplexIndex p y,
    SSet.simplexPullbackDiagram_fst_leftFiberSimplexIndex p y,
    SSet.simplexPullbackDiagram_snd_leftFiberSimplexIndex p y⟩

/-- Resolutions and their maps have the intended types. -/
noncomputable example : SSet.{u} := SSet.simplexResolution p

noncomputable example (u : Z ⟶ Z') (hu : u ≫ q = p) :
    SSet.simplexResolution p ⟶ SSet.simplexResolution q :=
  SSet.simplexResolutionMap u hu

/-- Resolution maps preserve identities and composition strictly. -/
example (u : Z ⟶ Z') (v : Z' ⟶ Z'')
    (hu : u ≫ q = p) (hv : v ≫ r = q) :
    SSet.simplexResolutionMap (𝟙 Z) (by simp) =
        𝟙 (SSet.simplexResolution p) ∧
      SSet.simplexResolutionMap (u ≫ v)
          (by rw [Category.assoc, hv, hu]) =
        SSet.simplexResolutionMap u hu ≫
          SSet.simplexResolutionMap v hv :=
  ⟨SSet.simplexResolutionMap_id p,
    SSet.simplexResolutionMap_comp u v hu hv⟩

/-- The resolution augmentation is the first-projection cocone and is natural
in triangles over `Y`. -/
example (u : Z ⟶ Z') (hu : u ≫ q = p) :
    SSet.simplexResolutionMap u hu ≫
        SSet.simplexResolutionAugmentation q =
      SSet.simplexResolutionAugmentation p ≫ u :=
  SSet.simplexResolutionAugmentation_naturality u hu

/-- The resolution cocone and augmentation retain their literal definitions. -/
example (s : SSet.SimplexIndex Y) :
    (SSet.simplexPullbackCocone p).app s = pullback.fst p s.hom :=
  rfl

example :
    SSet.simplexResolutionAugmentation p =
      SSet.bkAugmentation (SSet.simplexPullbackCocone p) :=
  rfl

section UniverseOne

variable {Z₁ Y₁ : SSet.{1}} (p₁ : Z₁ ⟶ Y₁)

noncomputable example : SSet.{1} := SSet.simplexResolution p₁

noncomputable example : SSet.simplexResolution p₁ ⟶ Z₁ :=
  SSet.simplexResolutionAugmentation p₁

#synth Category.{0} (SSet.SimplexIndex Y₁)

end UniverseOne

section UniverseZero

variable {Z₀ Y₀ : SSet.{0}} (p₀ : Z₀ ⟶ Y₀)

noncomputable example : SSet.{0} := SSet.simplexResolution p₀

noncomputable example : SSet.simplexResolution p₀ ⟶ Z₀ :=
  SSet.simplexResolutionAugmentation p₀

#synth Category.{0} (SSet.SimplexIndex Y₀)

end UniverseZero

section BoundaryFixtures

noncomputable example :
    SSet.simplexResolution (𝟙 (Δ[0] : SSet.{0})) ⟶ Δ[0] :=
  SSet.simplexResolutionAugmentation (𝟙 (Δ[0] : SSet.{0}))

noncomputable example :
    SSet.simplexResolution (𝟙 (Δ[1] : SSet.{0})) ⟶ Δ[1] :=
  SSet.simplexResolutionAugmentation (𝟙 (Δ[1] : SSet.{0}))

noncomputable example :
    SSet.simplexResolution (𝟙 (⊥_ SSet.{0})) ⟶ (⊥_ SSet.{0}) :=
  SSet.simplexResolutionAugmentation (𝟙 (⊥_ SSet.{0}))

private noncomputable abbrev disconnected : SSet.{0} :=
  (Δ[0] : SSet.{0}) ⨿ (Δ[0] : SSet.{0})

noncomputable example :
    SSet.simplexResolution (𝟙 disconnected) ⟶ disconnected :=
  SSet.simplexResolutionAugmentation (𝟙 disconnected)

end BoundaryFixtures

#print axioms SSet.simplexPullbackDiagramMap_comp
#print axioms SSet.simplexPullbackDiagram_obj_leftFiberSimplexIndex
#print axioms SSet.simplexResolutionAugmentation_naturality

end MathlibExtTest.AlgebraicTopology.SimplicialSet.SimplexResolutionTests
